using System.Text.Json.Nodes;

namespace Lapila;

/// Refactors that cut indentation, offered as `refactor.rewrite` code actions on an `if`: invert it, turn it into an
/// early exit (a guard), merge it with the `if` it holds. The structure comes from a fresh parse of the text and the
/// layout from its lines: a moved body is only re-indented, so every comment and blank line in it stays. Only the
/// condition is rewritten, as text: the operator's own spelling is swapped in place (`==` and `!=`, `===` and `!==`,
/// and `<` with `>=` between integers or Decimal), `not x` loses its `not`, `and` and `or` go through De Morgan, and
/// anything else, a float comparison, a chained comparison, and what this code cannot tell the type of, is written
/// `not (...)`: with `nan`, `a < b` and `a >= b` are both false. An action is offered only where it is correct, so a
/// shape the code does not understand gets none.
public static partial class LanguageServer
{
    private const int RefactorIndent = 4;

    /// One refactor: the lines `StartLine` to `EndLine` (0-based, whole lines) become `NewText`.
    internal sealed record Refactor(string Title, int StartLine, int EndLine, string NewText);

    // Types whose comparisons have the usual order. A binary float or an IEEE decimal float has `nan`, so those are
    // wrapped in `not (...)`. `Decimal` is never a NaN.
    private static readonly HashSet<string> OrderedTypes =
    [
        "S8", "S16", "S32", "S64", "S128", "S256", "U8", "U16", "U32", "U64", "U128", "U256", "Byte", "Char", "Decimal",
    ];

    /// Where the lines of a body lead when they run out: the end of a routine (whether it has a result) or the end of a
    /// loop round (whether the loop carries values).
    private sealed record RefactorScope(bool InLoop, bool Flag);

    /// The refactors for the `if` statements whose header lies on the 0-based lines `first` to `last` of `text`.
    internal static List<Refactor> Refactors(string text, int first, int last)
    {
        var result = new List<Refactor>();
        string normalized = text.Replace("\r\n", "\n");
        string[] lines = normalized.Split('\n');
        List<Decl> decls;
        try
        {
            decls = ParseRecovering("input.lpa", normalized, false, []);
        }
        catch (CompileError)
        {
            return result;
        }

        foreach (var routine in decls.OfType<RoutineDecl>())
        {
            if (routine.Blocks is null) continue;
            var types = TypesOf(routine);
            foreach (var block in routine.Blocks)
            {
                var scope = block.Name == "entry" ? new RefactorScope(false, routine.ReturnType.Name != "None") : null;
                VisitRefactors(block.Stmts, scope, new RefactorWork(lines, first + 1, last + 1, types), result);
            }
        }
        if (text.Contains("\r\n"))
            for (int i = 0; i < result.Count; i++) result[i] = result[i] with { NewText = result[i].NewText.Replace("\n", "\r\n") };
        return result;
    }

    private sealed record RefactorWork(string[] Lines, int First, int Last, Dictionary<string, TypeRef?> Types);

    /// The type each name of a routine is bound with: its parameters, its bindings, its loop variables and carried
    /// values. A name bound with two different types has none.
    private static Dictionary<string, TypeRef?> TypesOf(RoutineDecl routine)
    {
        var types = new Dictionary<string, TypeRef?>();
        void Bind(string name, TypeRef? type)
        {
            if (types.TryGetValue(name, out var known)) types[name] = known is not null && type is not null && known.ToString() == type.ToString() ? known : null;
            else types[name] = type;
        }
        foreach (var p in routine.Params) Bind(p.Name, p.Type);
        void Walk(List<Stmt>? stmts)
        {
            if (stmts is null) return;
            foreach (var s in stmts)
                switch (s)
                {
                    case BindStmt b:
                        Bind(b.Name, b.Type);
                        break;
                    case IfStmt i:
                        Walk(i.Then);
                        Walk(i.Else);
                        break;
                    case WhenStmt w:
                        foreach (var arm in w.Arms) Walk(arm.Body);
                        break;
                    case LoopStmt l:
                        foreach (var c in l.With) Bind(c.Name, c.Type);
                        if (l.Var is { } v) Bind(v, l.VarType ?? LoopVarType(l, types));
                        Walk(l.Body);
                        Walk(l.Then);
                        break;
                }
        }
        foreach (var block in routine.Blocks ?? []) Walk(block.Stmts);
        return types;
    }

    /// The type a `for i in a til b` walks when it writes none: the type of a bound that is a name, else `S64`.
    private static TypeRef? LoopVarType(LoopStmt loop, Dictionary<string, TypeRef?> types)
    {
        if (loop.Source is not RangeExpr range) return null;
        foreach (var bound in new[] { range.From, range.To })
            if (bound is ValueRef v && types.GetValueOrDefault(v.Name) is { } t) return t;
        return range.From is IntLit && range.To is IntLit ? new TypeRef("S64", [], loop.Pos) : null;
    }

    private static void VisitRefactors(List<Stmt>? stmts, RefactorScope? scope, RefactorWork work, List<Refactor> result)
    {
        if (stmts is null) return;
        for (int i = 0; i < stmts.Count; i++)
        {
            if (stmts[i] is IfStmt) ConsiderIf(stmts, i, scope, work, result);
            switch (stmts[i])
            {
                case IfStmt s:
                    VisitRefactors(s.Then, null, work, result);
                    VisitRefactors(s.Else, null, work, result);
                    break;
                case LoopStmt loop:
                    VisitRefactors(loop.Body, new RefactorScope(true, loop.With.Count > 0), work, result);
                    VisitRefactors(loop.Then, null, work, result);
                    break;
                case WhenStmt whenStmt:
                    foreach (var arm in whenStmt.Arms) VisitRefactors(arm.Body, null, work, result);
                    break;
            }
        }
    }

    // ── The statement ───────────────────────────────────────────────────────

    private static int IndentOf(string line)
    {
        int n = 0;
        while (n < line.Length && line[n] == ' ') n++;
        return n;
    }

    private static bool BlankLine(string line) => line.Trim().Length == 0;

    /// The last line (1-based) of the body that starts on line `from` under a header with `indent` spaces: the last line
    /// with text before the first line that is not indented deeper. A comment line at the header's level ends the body.
    /// One less than `from` when the body has no line.
    private static int BodyEnd(RefactorWork work, int from, int indent)
    {
        int last = from - 1;
        for (int k = from; k <= work.Lines.Length; k++)
        {
            string line = work.Lines[k - 1];
            if (BlankLine(line)) continue;
            if (IndentOf(line) <= indent) break;
            last = k;
        }
        return last;
    }

    /// The lines (1-based, both included) moved by `shift` spaces: negative takes spaces off the front, positive puts
    /// them on. Blank lines stay empty.
    private static IEnumerable<string> Shifted(RefactorWork work, int from, int to, int shift)
    {
        for (int k = from; k <= to; k++)
        {
            string line = work.Lines[k - 1];
            yield return BlankLine(line) ? "" : shift >= 0 ? new string(' ', shift) + line : line[-shift..];
        }
    }

    private static Refactor MakeRefactor(string title, int fromLine, int toLine, IEnumerable<string> lines) =>
        new(title, fromLine - 1, toLine - 1, string.Join("\n", lines));

    private static void ConsiderIf(List<Stmt> stmts, int at, RefactorScope? scope, RefactorWork work, List<Refactor> result)
    {
        var s = (IfStmt)stmts[at];
        int header = s.Pos.Line;
        if (header < work.First || header > work.Last || header > work.Lines.Length || s.Then.Count == 0
            || s.Then is [NothingStmt]) return;
        string line = work.Lines[header - 1];
        int indent = IndentOf(line);
        if (s.Pos.Col - 1 != indent || !line.AsSpan(indent).StartsWith("if ", StringComparison.Ordinal)) return;
        if (!HeaderIsOneLine(work, header, indent)) return;
        int thenEnd = BodyEnd(work, header + 1, indent);
        if (thenEnd < header + 1) return;

        int comment = CommentStart(line);
        string trailing = comment < 0 ? "" : "  " + line[comment..].TrimEnd();
        int condEnd = comment < 0 ? line.Length : comment;
        // The condition is the header's text between `if ` and its comment.
        int condStart = indent + 3;
        if (condStart >= condEnd) return;

        if (TryInvert(s, work, indent, header, thenEnd, condStart, condEnd, trailing) is { } inverted) result.Add(inverted);
        if (TryGuard(stmts, at, scope, work, indent, header, thenEnd, condStart, condEnd, trailing) is { } guard) result.Add(guard);
        if (TryMerge(s, work, indent, header, thenEnd, condStart, condEnd, trailing) is { } merged) result.Add(merged);
    }

    /// Whether the condition fits on the header line: its brackets close, it does not end on an operator word, and
    /// the next line is not a continuation (one that leads with `and`, `or` or `.`).
    private static bool HeaderIsOneLine(RefactorWork work, int header, int indent)
    {
        string line = work.Lines[header - 1];
        int comment = CommentStart(line);
        string code = (comment < 0 ? line : line[..comment]).TrimEnd();
        int depth = 0;
        for (int i = 0; i < code.Length; i++)
        {
            if (code[i] is '"' or '\'')
            {
                i = LiteralEnd(code, i);
                continue;
            }
            if (code[i] is '(' or '[' or '{') depth++;
            else if (code[i] is ')' or ']' or '}') depth--;
        }
        if (depth != 0 || code.EndsWith(" and", StringComparison.Ordinal) || code.EndsWith(" or", StringComparison.Ordinal)
            || code.EndsWith(',') || code.EndsWith('\\')) return false;
        if (header >= work.Lines.Length) return false;
        string next = work.Lines[header].TrimStart();
        return !(next.StartsWith("and ", StringComparison.Ordinal) || next.StartsWith("or ", StringComparison.Ordinal)
                 || next.StartsWith('.'));
    }

    /// The index of the `#` that starts a comment on the line (outside text and character literals), or -1.
    private static int CommentStart(string s)
    {
        for (int i = 0; i < s.Length; i++)
        {
            if (s[i] is '"' or '\'') i = LiteralEnd(s, i);
            else if (s[i] == '#') return i;
        }
        return -1;
    }

    /// The index of the quote that closes the literal opened at `open` (or the line's end).
    private static int LiteralEnd(string s, int open)
    {
        for (int i = open + 1; i < s.Length; i++)
        {
            if (s[i] == '\\') i++;
            else if (s[i] == s[open]) return i;
        }
        return s.Length;
    }

    // ── Invert ──────────────────────────────────────────────────────────────

    /// `if c A else B` becomes `if not c B else A`.
    private static Refactor? TryInvert(IfStmt s, RefactorWork work, int indent, int header, int thenEnd, int condStart,
        int condEnd, string trailing)
    {
        if (s.Else is null) return null;
        int elseLine = thenEnd + 1;
        while (elseLine <= work.Lines.Length && BlankLine(work.Lines[elseLine - 1])) elseLine++;
        if (elseLine > work.Lines.Length || work.Lines[elseLine - 1] != new string(' ', indent) + "else") return null;
        int elseEnd = BodyEnd(work, elseLine + 1, indent);
        if (elseEnd < elseLine + 1) return null;
        if (Negated(work.Lines[header - 1], s.Cond, condStart, condEnd, work) is not { } condition) return null;

        var lines = new List<string> { new string(' ', indent) + "if " + condition.Text + trailing };
        lines.AddRange(Shifted(work, elseLine + 1, elseEnd, 0));
        lines.Add(new string(' ', indent) + "else");
        lines.AddRange(Shifted(work, header + 1, thenEnd, 0));
        return MakeRefactor("Invert 'if'", header, elseEnd, lines);
    }

    // ── Early exit ──────────────────────────────────────────────────────────

    /// `if c { body }` followed by nothing but the end of the routine (or its final `return`) or the end of the loop
    /// round becomes `if not c { return }` (`continue` in a loop) and the body one level out. With a result,
    /// `if c { ...; return a }` then `return b` becomes `if not c { return b }` then the body.
    private static Refactor? TryGuard(List<Stmt> stmts, int at, RefactorScope? scope, RefactorWork work, int indent,
        int header, int thenEnd, int condStart, int condEnd, string trailing)
    {
        var s = (IfStmt)stmts[at];
        if (scope is null || s.Else is not null) return null;
        var tail = stmts.Skip(at + 1).ToList();
        bool bodyEndsInReturn = s.Then is [.., ReturnStmt { IsThrow: false }];
        string guard = "";
        int regionEnd = thenEnd, tailStart = 0, tailEnd = 0;
        if (scope.InLoop)
        {
            if (tail.Count != 0 || scope.Flag) return null;
            guard = "continue";
        }
        else
        {
            switch (tail)
            {
                case []:
                    if (scope.Flag) return null;
                    guard = "return";
                    break;
                case [ReturnStmt { Value: null, IsThrow: false } bare]:
                    if (scope.Flag) return null;
                    guard = "return";
                    if (bodyEndsInReturn) (tailStart, tailEnd) = TailLines(work, bare, indent);
                    break;
                case [ReturnStmt { Value: not null, IsThrow: false } valued]:
                    if (s.Then is not [.., ReturnStmt { Value: not null, IsThrow: false }]) return null;
                    (tailStart, tailEnd) = TailLines(work, valued, indent);
                    if (tailStart == 0) return null;
                    break;
                default:
                    return null;
            }
            if (tailStart > 0)
            {
                if (tailStart <= thenEnd || tailEnd < tailStart) return null;
                // Only blank lines may lie between the body and the `return`: a comment there would be lost.
                for (int k = thenEnd + 1; k < tailStart; k++)
                    if (!BlankLine(work.Lines[k - 1])) return null;
                regionEnd = tailEnd;
            }
        }
        if (Negated(work.Lines[header - 1], s.Cond, condStart, condEnd, work) is not { } condition) return null;

        var lines = new List<string> { new string(' ', indent) + "if " + condition.Text + trailing };
        if (guard.Length > 0) lines.Add(new string(' ', indent + RefactorIndent) + guard);
        else lines.AddRange(Shifted(work, tailStart, tailEnd, RefactorIndent));
        lines.AddRange(Shifted(work, header + 1, thenEnd, -RefactorIndent));
        return MakeRefactor(scope.InLoop ? "Exit early with 'continue'" : "Exit early with 'return'", header, regionEnd, lines);
    }

    /// The lines (1-based) of a `return` that is the last statement of a body: from its own line to the last line
    /// indented deeper than it. (0, 0) when its line is not where a plain `return` of that level stands.
    private static (int Start, int End) TailLines(RefactorWork work, ReturnStmt tail, int indent)
    {
        int start = tail.Pos.Line;
        if (start < 1 || start > work.Lines.Length || IndentOf(work.Lines[start - 1]) != indent
            || !work.Lines[start - 1].AsSpan(indent).StartsWith("return", StringComparison.Ordinal)) return (0, 0);
        return (start, BodyEnd(work, start + 1, indent));
    }

    // ── Merge ───────────────────────────────────────────────────────────────

    /// `if a` holding only `if b` (no `else` on either) becomes `if a and b`.
    private static Refactor? TryMerge(IfStmt s, RefactorWork work, int indent, int header, int thenEnd, int condStart,
        int condEnd, string trailing)
    {
        if (s.Else is not null || s.Then is not [IfStmt inner] || inner.Else is not null) return null;
        int innerLine = inner.Pos.Line;
        if (innerLine != header + 1 || innerLine > work.Lines.Length) return null;
        string line = work.Lines[innerLine - 1];
        if (IndentOf(line) != indent + RefactorIndent || inner.Pos.Col - 1 != indent + RefactorIndent
            || !line.AsSpan(indent + RefactorIndent).StartsWith("if ", StringComparison.Ordinal)
            || !HeaderIsOneLine(work, innerLine, indent + RefactorIndent)) return null;
        int innerEnd = BodyEnd(work, innerLine + 1, indent + RefactorIndent);
        // Nothing may follow the inner `if` in the outer body, not even a comment.
        if (innerEnd < innerLine + 1 || innerEnd != thenEnd) return null;

        int innerComment = CommentStart(line);
        string innerTrailing = innerComment < 0 ? "" : "  " + line[innerComment..].TrimEnd();
        if (trailing.Length > 0 && innerTrailing.Length > 0) return null;
        int innerCondStart = indent + RefactorIndent + 3;
        int innerCondEnd = innerComment < 0 ? line.Length : innerComment;
        if (innerCondStart >= innerCondEnd) return null;

        string outer = Joinable(work.Lines[header - 1], s.Cond, condStart, condEnd);
        string innerText = Joinable(line, inner.Cond, innerCondStart, innerCondEnd);
        var lines = new List<string> { new string(' ', indent) + "if " + outer + " and " + innerText + trailing + innerTrailing };
        lines.AddRange(Shifted(work, innerLine + 1, innerEnd, -RefactorIndent));
        return MakeRefactor("Merge nested 'if'", header, innerEnd, lines);
    }

    /// An operand of `and`: the condition's text, in parentheses when it joins things with `or` (the two do not mix).
    private static string Joinable(string line, Expr cond, int lo, int hi)
    {
        string text = line[lo..hi].Trim();
        return cond is BinaryExpr { Op: "or" } && !Parenthesized(text) ? "(" + text + ")" : text;
    }

    // ── Negation ────────────────────────────────────────────────────────────

    /// A condition's text and the logical operator it joins at the top (`and`, `or`, or none).
    private readonly record struct Cond(string Text, string? Joiner);

    private static Cond? Negated(string line, Expr cond, int lo, int hi, RefactorWork work)
    {
        try
        {
            return Negate(line, cond, lo, hi, work);
        }
        catch (RefactorGiveUp)
        {
            return null;
        }
    }

    /// Raised where the text and the tree do not agree, so no action is offered.
    private sealed class RefactorGiveUp : Exception;

    /// The condition that holds exactly when `e` (the text between `lo` and `hi` of `line`) does not.
    private static Cond Negate(string line, Expr e, int lo, int hi, RefactorWork work)
    {
        (lo, hi) = Trimmed(line, lo, hi);
        (lo, hi) = Unparenthesized(line, lo, hi);
        switch (e)
        {
            case BoolLit b:
                return new Cond(b.Value ? "false" : "true", null);
            case UnaryExpr { Op: "not" } u:
            {
                int at = OperatorAt(line, u.Pos, "not", lo, hi);
                var (from, to) = Unparenthesized(line, Trimmed(line, at + 3, hi));
                return new Cond(line[from..to], u.Operand is BinaryExpr { Op: "and" or "or" } j ? j.Op : null);
            }
            case BinaryExpr { Op: "and" or "or" } j:
            {
                int at = OperatorAt(line, j.Pos, j.Op, lo, hi);
                string op = j.Op == "and" ? "or" : "and";
                var left = Negate(line, j.Left, lo, at, work);
                var right = Negate(line, j.Right, at + j.Op.Length, hi, work);
                return new Cond(Operand(left, op) + " " + op + " " + Operand(right, op), op);
            }
            case BinaryExpr b when SwapSpelling(b.Op, b, work) is { } swapped:
            {
                int at = OperatorAt(line, b.Pos, b.Op, lo, hi);
                return new Cond(line[lo..at] + swapped + line[(at + b.Op.Length)..hi], null);
            }
        }
        string text = line[lo..hi];
        return new Cond("not " + (e is ValueRef or CallExpr or MethodCallExpr or NsCallExpr or FieldExpr or GetItemExpr or PresetRef
            ? text
            : "(" + text + ")"), null);
    }

    /// An operand of `and` / `or` joined by `op`: in parentheses when it joins by the other one.
    private static string Operand(Cond c, string op) => c.Joiner is { } j && j != op && !Parenthesized(c.Text) ? "(" + c.Text + ")" : c.Text;

    /// The spelling that holds when `op` does not, or null when there is none to swap in.
    private static string? SwapSpelling(string op, BinaryExpr b, RefactorWork work) => op switch
    {
        "==" => "!=",
        "!=" => "==",
        "===" => "!==",
        "!==" => "===",
        "<" when ComparesOrdered(b, work) => ">=",
        "<=" when ComparesOrdered(b, work) => ">",
        ">" when ComparesOrdered(b, work) => "<=",
        ">=" when ComparesOrdered(b, work) => "<",
        _ => null,
    };

    /// Whether both sides of a comparison are integers or Decimal. A bare integer literal takes the type of the other
    /// side. The types are those the routine writes for its names, so anything else is not known.
    private static bool ComparesOrdered(BinaryExpr b, RefactorWork work)
    {
        bool left = OrderedSide(b.Left, work, out bool leftKnown);
        bool right = OrderedSide(b.Right, work, out bool rightKnown);
        return left && right && (leftKnown || rightKnown);
    }

    private static bool OrderedSide(Expr side, RefactorWork work, out bool known)
    {
        known = false;
        if (side is IntLit or UnaryExpr { Op: "-", Operand: IntLit }) return true;
        if (side is ValueRef v && work.Types.GetValueOrDefault(v.Name) is { Path: null, Args.Count: 0, Amp: false, Question: false } t)
            return known = OrderedTypes.Contains(t.Name);
        return false;
    }

    /// The column index of the operator `op` the node stands at, checked against the text.
    private static int OperatorAt(string line, Pos pos, string op, int lo, int hi)
    {
        int at = pos.Col - 1;
        if (at < lo || at + op.Length > hi || string.CompareOrdinal(line, at, op, 0, op.Length) != 0) throw new RefactorGiveUp();
        return at;
    }

    private static (int Lo, int Hi) Trimmed(string line, int lo, int hi)
    {
        while (lo < hi && line[lo] == ' ') lo++;
        while (hi > lo && line[hi - 1] == ' ') hi--;
        return (lo, hi);
    }

    private static (int Lo, int Hi) Unparenthesized(string line, int lo, int hi)
    {
        while (hi - lo >= 2 && line[lo] == '(' && MatchingClose(line, lo) == hi - 1) (lo, hi) = Trimmed(line, lo + 1, hi - 1);
        return (lo, hi);
    }

    private static (int Lo, int Hi) Unparenthesized(string line, (int Lo, int Hi) range) => Unparenthesized(line, range.Lo, range.Hi);

    private static bool Parenthesized(string text) => text.Length >= 2 && text[0] == '(' && MatchingClose(text, 0) == text.Length - 1;

    private static int MatchingClose(string s, int open)
    {
        int depth = 0;
        for (int i = open; i < s.Length; i++)
        {
            if (s[i] is '"' or '\'')
            {
                i = LiteralEnd(s, i);
                continue;
            }
            if (s[i] == '(') depth++;
            else if (s[i] == ')' && --depth == 0) return i;
        }
        return -1;
    }

    // ── The request ─────────────────────────────────────────────────────────

    /// The refactor code actions for the lines of a request's range.
    private static JsonArray RefactorActions(string uri, string text, int first, int last)
    {
        var actions = new JsonArray();
        string[] lines = text.Replace("\r\n", "\n").Split('\n');
        foreach (var r in Refactors(text, first, last))
        {
            var edit = new JsonObject
            {
                ["range"] = new JsonObject
                {
                    ["start"] = new JsonObject { ["line"] = r.StartLine, ["character"] = 0 },
                    ["end"] = new JsonObject { ["line"] = r.EndLine, ["character"] = lines[r.EndLine].Length },
                },
                ["newText"] = r.NewText,
            };
            actions.Add(new JsonObject
            {
                ["title"] = r.Title,
                ["kind"] = "refactor.rewrite",
                ["edit"] = new JsonObject { ["changes"] = new JsonObject { [uri] = new JsonArray(edit) } },
            });
        }
        return actions;
    }
}
