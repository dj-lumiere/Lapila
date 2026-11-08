using System.Text.Json.Nodes;

namespace Lapila;

/// Doc comments written for you. Typing `###` alone on the line above a declaration fills in the frame: a summary line,
/// then for a routine a `:typeparam` line per type parameter of its own, a `:param` line per parameter but `me`, a
/// `:returns:` line unless it returns None and a `:throws:` line per crashable its body throws. It comes as a completion
/// item (a snippet, the cursor on the summary) and as on-type formatting, since editors offer one or the other. A routine
/// whose doc comment lacks some of those lines gets a quick fix that adds them where they belong, and one whose doc
/// comment names a parameter it doesn't have, or a result it doesn't give, gets a separate quick fix that removes those.
public static partial class LanguageServer
{
    /// What a doc comment is held to: the routine's own type parameters, its parameters but `me`, whether it returns a
    /// value and the crashables its body throws. A type has none of them.
    internal sealed record DocFacts(List<string> TypeParams, List<string> Params, bool Returns, List<string> Throws);

    /// One doc line and the lines that continue it: a field (`:param x: ...`) with its kind and name, or a summary line.
    private sealed record DocBlock(string? Kind, string? Name, int First, int Last);

    // How the kinds of a doc comment follow one another. Other kinds (`:note:`, `:see:`) come last.
    private static int DocRank(string? kind) => kind switch
    {
        null => 0,
        "typeparam" => 1,
        "param" => 2,
        "returns" => 3,
        "throws" => 4,
        _ => 5,
    };

    /// The declarations of a parsed text with the 1-based line each starts on (its first annotation's, else its own),
    /// and what a doc comment above it is held to. A concept's routines are declarations of their own.
    private static List<(int Line, DocFacts Facts, int Header)> DocTargets(string text)
    {
        List<Decl> decls;
        try
        {
            decls = ParseRecovering("input.lpa", text.Replace("\r\n", "\n"), false, []);
        }
        catch (CompileError)
        {
            return [];
        }

        var result = new List<(int, DocFacts, int)>();
        void Add(Decl d, DocFacts facts)
        {
            int first = d.Annotations.Select(a => a.Pos.Line).Append(d.Pos.Line).Min();
            result.Add((first, facts, d.Pos.Line));
        }
        foreach (var d in decls)
        {
            switch (d)
            {
                case RoutineDecl r:
                    Add(r, FactsOf(r));
                    break;
                case ConceptDecl c:
                    Add(c, new DocFacts([], [], false, []));
                    foreach (var r in c.Routines) Add(r, FactsOf(r));
                    break;
                case RecordDecl or ChoiceDecl or VariantDecl or PresetDecl or AliasDecl:
                    Add(d, new DocFacts([], [], false, []));
                    break;
            }
        }
        return result;
    }

    private static DocFacts FactsOf(RoutineDecl r)
    {
        var throws = r.Blocks is { } blocks
            ? blocks.SelectMany(b => Bodies.All(b.Stmts))
                .OfType<ReturnStmt>()
                .Where(s => s.IsThrow)
                .Select(s => s.Value is CallExpr made ? made.Name : null)
                .OfType<string>()
                .Distinct()
                .ToList()
            : [];
        return new DocFacts(r.TypeParams, r.Params.Select(p => p.Name).Where(p => p != "me").ToList(),
            r.ReturnType.Name != "None", throws);
    }

    /// The frame for the declaration starting right below the 0-based line `line`, which holds `###` alone. Null when no
    /// declaration starts there, or a doc line already sits above the `###`. With `snippet`, the summary and each
    /// description is a tab stop.
    internal static string? DocFrame(string text, int line, bool snippet)
    {
        string[] lines = text.Replace("\r\n", "\n").Split('\n');
        if (line < 0 || line >= lines.Length || lines[line].Trim() != "###") return null;
        if (line > 0 && lines[line - 1].TrimStart().StartsWith("###", StringComparison.Ordinal)) return null;
        var target = DocTargets(text).FirstOrDefault(t => t.Line == line + 2);
        if (target.Facts is null) return null;

        string indent = lines[line][..(lines[line].Length - lines[line].TrimStart().Length)];
        int stop = 1;
        string Stop() => snippet ? $"${stop++}" : "";
        string Text(string s) => snippet ? s.Replace("\\", "\\\\").Replace("$", "\\$").Replace("}", "\\}") : s;
        var frame = new List<string> { $"{indent}### {Stop()}" };
        foreach (string t in target.Facts.TypeParams) frame.Add($"{indent}### :typeparam {Text(t)}: {Stop()}");
        foreach (string p in target.Facts.Params) frame.Add($"{indent}### :param {Text(p)}: {Stop()}");
        if (target.Facts.Returns) frame.Add($"{indent}### :returns: {Stop()}");
        foreach (string e in target.Facts.Throws) frame.Add($"{indent}### :throws: {{{Text(e)}}} {Stop()}");
        return string.Join("\n", frame.Select(l => snippet ? l : l.TrimEnd())) + (snippet ? "$0" : "");
    }

    /// The `###` completion: the frame as a snippet in place of the `###` the cursor ends.
    private static JsonObject? DocFrameCompletion(string text, int line, int character)
    {
        string[] lines = text.Replace("\r\n", "\n").Split('\n');
        if (line >= lines.Length || lines[line][..Math.Min(character, lines[line].Length)].Trim() != "###") return null;
        if (DocFrame(text, line, snippet: true) is not { } frame) return null;
        return new JsonObject
        {
            ["label"] = "###",
            ["kind"] = KindKeyword,
            ["detail"] = Ko("doc comment", "문서 주석"),
            ["sortText"] = "0###",
            ["filterText"] = "###",
            ["insertTextFormat"] = 2,
            ["textEdit"] = new JsonObject
            {
                ["range"] = new JsonObject
                {
                    ["start"] = new JsonObject { ["line"] = line, ["character"] = 0 },
                    ["end"] = new JsonObject { ["line"] = line, ["character"] = lines[line].Length },
                },
                ["newText"] = frame,
            },
        };
    }

    /// The on-type answer to the third `#`: the frame in place of the line.
    private static JsonArray DocFrameOnType(string uri, int line)
    {
        string? text;
        lock (Documents) text = Documents.TryGetValue(uri, out var doc) ? doc.Text : null;
        if (text is null || DocFrame(text, line, snippet: false) is not { } frame) return [];
        string[] lines = text.Replace("\r\n", "\n").Split('\n');
        return
        [
            new JsonObject
            {
                ["range"] = new JsonObject
                {
                    ["start"] = new JsonObject { ["line"] = line, ["character"] = 0 },
                    ["end"] = new JsonObject { ["line"] = line, ["character"] = lines[line].Length },
                },
                ["newText"] = frame,
            },
        ];
    }

    /// The quick fixes for a doc comment that doesn't match its routine, offered on the routine's header or doc lines
    /// (0-based `first` to `last`): one adds the lines it lacks, one removes the lines that name nothing it has.
    internal static List<(string Title, int StartLine, int EndLine, string NewText)> DocFixes(string text, int first, int last)
    {
        var fixes = new List<(string, int, int, string)>();
        string[] lines = text.Replace("\r\n", "\n").Split('\n');
        foreach (var (start, facts, header) in DocTargets(text))
        {
            // The doc lines right above the declaration (0-based), past nothing but other comments.
            int top = start - 1;
            while (top > 0 && lines[top - 1].TrimStart().StartsWith("###", StringComparison.Ordinal)) top--;
            int bottom = start - 2;
            if (bottom < top || last < top || first > header - 1) continue;

            List<DocBlock> blocks = DocBlocks(lines, top, bottom);
            string indent = lines[top][..(lines[top].Length - lines[top].TrimStart().Length)];
            if (Filled(lines, blocks, facts, indent) is { } filled)
                fixes.Add((Ko("Fill in the doc comment", "문서 주석 채우기"), top, bottom, filled));
            if (Pruned(lines, blocks, facts) is { } pruned)
                fixes.Add((Ko("Remove doc lines that match nothing", "맞지 않는 문서 줄 지우기"), top, bottom, pruned));
        }
        return fixes;
    }

    /// The doc lines `top` to `bottom` as blocks: each field line with the lines after it that aren't fields.
    private static List<DocBlock> DocBlocks(string[] lines, int top, int bottom)
    {
        var blocks = new List<DocBlock>();
        for (int i = top; i <= bottom; i++)
        {
            string body = lines[i].Trim()[3..].Trim();
            if (body.StartsWith(':') && body.IndexOf(':', 1) is var end and > 0)
            {
                string[] spec = body[1..end].Trim().Split(' ', 2, StringSplitOptions.RemoveEmptyEntries);
                if (spec.Length > 0)
                {
                    blocks.Add(new DocBlock(spec[0].ToLowerInvariant(), spec.Length > 1 ? spec[1].Trim() : null, i, i));
                    continue;
                }
            }
            // A line that continues the field above it, else a summary line.
            if (blocks.Count > 0 && blocks[^1].Kind is not null) blocks[^1] = blocks[^1] with { Last = i };
            else blocks.Add(new DocBlock(null, null, i, i));
        }
        return blocks;
    }

    /// The doc lines with the lines they lack added where they belong, or null when nothing is missing.
    private static string? Filled(string[] lines, List<DocBlock> blocks, DocFacts facts, string indent)
    {
        bool Has(string kind, string? name) => blocks.Any(b => b.Kind == kind && (name is null || b.Name == name));
        bool Thrown(string error) => blocks.Any(b => b.Kind == "throws" &&
            Enumerable.Range(b.First, b.Last - b.First + 1).Any(i => lines[i].Contains($"{{{error}}}", StringComparison.Ordinal)));
        var missing = new List<(int Rank, int Order, string Line)>();
        for (int i = 0; i < facts.TypeParams.Count; i++)
            if (!Has("typeparam", facts.TypeParams[i])) missing.Add((1, i, $"{indent}### :typeparam {facts.TypeParams[i]}:"));
        for (int i = 0; i < facts.Params.Count; i++)
            if (!Has("param", facts.Params[i])) missing.Add((2, i, $"{indent}### :param {facts.Params[i]}:"));
        if (facts.Returns && !Has("returns", null)) missing.Add((3, 0, $"{indent}### :returns:"));
        foreach (string e in facts.Throws.Where(e => !Thrown(e))) missing.Add((4, 0, $"{indent}### :throws: {{{e}}}"));
        if (missing.Count == 0) return null;

        // Each new line goes before the first block that comes after it: a later kind, or a later parameter.
        int OrderOf(DocBlock b) => b.Kind switch
        {
            "typeparam" => facts.TypeParams.IndexOf(b.Name ?? ""),
            "param" => facts.Params.IndexOf(b.Name ?? ""),
            _ => -1,
        };
        var output = new List<string>();
        var pending = new Queue<(int Rank, int Order, string Line)>(missing.OrderBy(m => m.Rank).ThenBy(m => m.Order));
        foreach (var b in blocks)
        {
            int rank = DocRank(b.Kind);
            while (pending.Count > 0 && rank > 0 &&
                   (pending.Peek().Rank < rank || pending.Peek().Rank == rank && OrderOf(b) > pending.Peek().Order))
                output.Add(pending.Dequeue().Line);
            for (int i = b.First; i <= b.Last; i++) output.Add(lines[i]);
        }
        output.AddRange(pending.Select(p => p.Line));
        return string.Join("\n", output);
    }

    /// The doc lines without the fields that name nothing the routine has, or null when every field matches.
    private static string? Pruned(string[] lines, List<DocBlock> blocks, DocFacts facts)
    {
        bool Stale(DocBlock b) => b.Kind switch
        {
            "param" => b.Name is null || !facts.Params.Contains(b.Name),
            "typeparam" => b.Name is null || !facts.TypeParams.Contains(b.Name),
            "returns" => !facts.Returns,
            _ => false,
        };
        if (!blocks.Any(Stale)) return null;
        var kept = blocks.Where(b => !Stale(b)).SelectMany(b => Enumerable.Range(b.First, b.Last - b.First + 1)).Select(i => lines[i]);
        return string.Join("\n", kept);
    }
}
