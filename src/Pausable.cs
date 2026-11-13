using System.Text;
using System.Text.RegularExpressions;

namespace Lapila;

/// Pausable routines. A `pausable routine f(a: A) -> R` waits with `pauseuntil X carrying (b, c)`. Before anything is
/// checked, the builder turns each one into Lapila declarations of its own:
///
/// - `entity PausedF obeys Eventual[PausedF, R]`: the state record. Its fields are the parameters, every value a
///   `carrying` list names (a `<-` place as a `Carried[T]` that holds its value in the record), the values a loop with a
///   pause in it keeps from round to round, `at` (the pause it stopped at, 0 before the first line), and `room`, a
///   `StepRoom` as large as the largest step the routine waits for.
/// - `PausedF.construct(a: A)`, the record before its first line, and `wake_when_done`, which does nothing: the step at
///   the bottom of a chain of pausable routines is the one that wakes the work.
/// - `routine @PausedF.resume() -> R | Pending`, written as blocks: the entry goes on at the pause `at` names, each
///   `pauseuntil` is the block that puts the step in the room and the block that asks it for its result, and an `if`,
///   `when` or loop with a pause inside is blocks joined by jumps. A value the program binds is a field when it is
///   kept across a pause, and stays a value of its block when it isn't.
///
/// The routine's own declaration stays, with no lines, for its name, parameters and result: `f.to[Work](...)` makes
/// pausable work from it (FunctionGen.EvalWork), and a plain call of it is a build error. The transformation knows
/// nothing that is special to waiting: a generator (`yield`) is the same record, resumed by a `for` instead.
public static class Pausable
{
    /// The annotation on a pausable routine's declaration that stays, and on the declarations made from it: the
    /// state record's name.
    public const string StateMark = "pausable_state";

    /// The state record a pausable routine's declaration names (StateMark), or null for any other routine.
    public static string? StateOf(RoutineDecl r) => r.IsPausable ? r.AnnotationNamed(StateMark)?.First : null;

    /// The field of a pausable routine's state record that keeps an access its view parameter `param` is handed with
    /// steal, or null.
    public static string? HandedField(RoutineDecl r, string param) =>
        r.AnnotationNamed(StateMark)?.Args.FirstOrDefault(a => a.Key == param)?.Value;

    /// Replaces each pausable routine in `decls` with its declaration (no lines) and the declarations made from it.
    /// `shown` is what was made, as Lapila source, for `[debug] show-pausable`.
    public static List<Decl> Lower(List<Decl> decls, out string shown)
    {
        var sb = new StringBuilder();
        if (!decls.Any(d => d is RoutineDecl { IsPausable: true }))
        {
            shown = "";
            return decls;
        }
        var world = new World(decls);
        var pausables = decls.OfType<RoutineDecl>().Where(r => r.IsPausable).ToList();
        foreach (var r in pausables) Validate(r);
        var names = new Dictionary<RoutineDecl, string>(ReferenceEqualityComparer.Instance);
        var taken = decls.Select(d => d switch { RecordDecl x => x.Name, VariantDecl v => v.Name, ChoiceDecl c => c.Name, AliasDecl a => a.Name, _ => null })
            .Where(n => n is not null).ToHashSet()!;
        foreach (var r in pausables)
        {
            string name = "Paused" + string.Concat(r.Name.Split('_', StringSplitOptions.RemoveEmptyEntries)
                .Select(p => char.ToUpperInvariant(p[0]) + p[1..]));
            string unique = name;
            for (int i = 2; taken.Contains(unique); i++) unique = name + i;
            taken.Add(unique!);
            names[r] = unique!;
        }
        world.States = pausables.ToDictionary(r => r.Name + "@" + r.Module, r => (r, names[r]));
        var lowered = pausables.Select(r => new Lowering(r, names[r], world).Run()).ToList();
        CheckCycles(lowered);
        var result = new List<Decl>();
        foreach (var d in decls)
        {
            if (d is RoutineDecl { IsPausable: true } r)
            {
                var low = lowered.First(l => ReferenceEquals(l.Routine, r));
                result.Add(r with
                {
                    Annotations = [.. r.Annotations, new Annotation(StateMark,
                        [new AnnotationArg(null, names[r], false), .. low.Handed.Select(h => new AnnotationArg(h.Key, h.Value, false))], r.Pos)],
                    Blocks = [new BlockDecl("entry", [], [new UnreachableStmt(r.Pos)], r.Pos)],
                });
                result.AddRange(low.Made);
                if (!r.IsLibrary) sb.Append(low.Shown);
                continue;
            }
            result.Add(d);
        }
        shown = sb.ToString();
        return result;
    }

    /// The forms a pausable routine can't take.
    private static void Validate(RoutineDecl r)
    {
        if (r.Owner is not null)
            throw new CompileError(Li.PausableForm, r.Pos, $"'{r.DisplayName}' is pausable and on a type: a pausable routine is a free routine "
                + "for now. Write it on its own and take the value as a parameter");
        if (r.TypeParams.Count > 0)
            throw new CompileError(Li.PausableForm, r.Pos, $"'{r.Name}' is pausable and generic: a pausable routine has one state record, "
                + "so it names its types. Write one routine for each type");
        if (r.Blocks is null)
            throw new CompileError(Li.PausableForm, r.Pos, $"'{r.Name}' is pausable and has no lines: a pausable routine is written in Lapila");
        if (r.Blocks.Count > 1 || r.AnnotationNamed(BlockRule.Generated) is not null)
            throw new CompileError(Li.PausableForm, r.Pos, $"'{r.Name}' is pausable and written with blocks: the builder writes a pausable "
                + "routine's blocks itself, so write its lines with if, when and loops");
        if (r.Params.Count > 4)
            throw new CompileError(Li.PausableForm, r.Pos, $"'{r.Name}' is pausable and has {r.Params.Count} parameters: pausable work takes at "
                + "most four, as every piece of work does. Hand it a record of them");
    }

    /// A pausable routine waiting on itself through other pausable routines would need a state record inside itself.
    private static void CheckCycles(List<Lowering> lowered)
    {
        var edges = new Dictionary<RoutineDecl, List<(RoutineDecl, Pos)>>(ReferenceEqualityComparer.Instance);
        foreach (var l in lowered) edges[l.Routine] = l.Waits;
        var state = new Dictionary<RoutineDecl, int>(ReferenceEqualityComparer.Instance);
        var path = new List<(RoutineDecl R, Pos At)>();
        void Visit(RoutineDecl r)
        {
            state[r] = 1;
            foreach (var (callee, at) in edges.GetValueOrDefault(r) ?? [])
            {
                path.Add((r, at));
                if (state.GetValueOrDefault(callee) == 1)
                {
                    int from = path.FindIndex(p => ReferenceEquals(p.R, callee));
                    var cycle = path.Skip(from).Select(p => p.R.Name).Append(callee.Name);
                    throw new CompileError(Li.PausableCycle, path[from].At, $"these pausable routines wait for each other through pauseuntil: "
                        + $"{string.Join(" -> ", cycle)}. A routine waiting for itself would hold its own state record inside it, which has "
                        + "no size: wait in a loop instead, or start the inner one as work of its own with f.to[Work](...) on a "
                        + "PausingFiber and pauseuntil its finish()");
                }
                if (!state.ContainsKey(callee)) Visit(callee);
                path.RemoveAt(path.Count - 1);
            }
            state[r] = 2;
        }
        foreach (var l in lowered)
            if (!state.ContainsKey(l.Routine)) Visit(l.Routine);
    }

    /// The declarations of the build, looked up by name: what the transformation reads the types of a step from.
    private sealed class World
    {
        public readonly Dictionary<string, List<RoutineDecl>> Free = [];
        public readonly Dictionary<(string Owner, string Name), List<RoutineDecl>> Methods = [];
        public readonly Dictionary<string, List<Decl>> Types = [];
        public readonly Dictionary<string, List<PresetDecl>> Globals = [];
        public Dictionary<string, (RoutineDecl Routine, string State)> States = [];

        public World(List<Decl> decls)
        {
            foreach (var d in decls)
                switch (d)
                {
                    case RoutineDecl { Owner: null } r: Add(Free, r.Name, r); break;
                    case RoutineDecl r: Add(Methods, (r.Owner!.Name, r.Name), r); break;
                    case RecordDecl x: Add(Types, x.Name, x); break;
                    case VariantDecl v: Add(Types, v.Name, v); break;
                    case ChoiceDecl c: Add(Types, c.Name, c); break;
                    case PresetDecl { Owner: null } p: Add(Globals, p.Name, p); break;
                }
        }

        private static void Add<TK, TV>(Dictionary<TK, List<TV>> into, TK key, TV value) where TK : notnull
        {
            if (!into.TryGetValue(key, out var list)) into[key] = list = [];
            list.Add(value);
        }

        /// The pausable routine a call names, and its state record, or null.
        public (RoutineDecl Routine, string State)? PausableCalled(Expr e, string module) => e switch
        {
            CallExpr c when States.TryGetValue(c.Name + "@" + (c.Path ?? module), out var own) => own,
            CallExpr { Path: null } c when States.Values.Where(s => s.Routine.Name == c.Name).ToList() is [var only] => only,
            _ => null,
        };

        /// Whether a type is an entity: an entity record, or the standard library's places and tickets.
        public bool IsEntity(TypeRef t)
        {
            if (t.Amp || t.Question) return t.Amp;
            if (t.Name is "PointedCell" or "PointedSlice" && t.Path is null) return false;
            return Types.TryGetValue(t.Name, out var found) && found.Any(d => d is RecordDecl { IsEntity: true });
        }
    }

    /// A field of the state record.
    private enum FieldKind
    {
        /// A value bound with `=` (or a parameter that takes a value or a view): read with `peek`, written with `poke`.
        Value,

        /// A `<-` place of the routine's frame, or a parameter that takes an entity over: a `Carried[T]` that holds the
        /// value in the record. `x.load()` reads `me.x.value.peek()`.
        Cell,

        /// A `<-` name that holds something it gives back itself (a place from a manager, a ticket): a `Carried[T]` of
        /// that thing, whose own routines are called on `me.x.value`.
        Holder,
    }

    private sealed record Field(string Name, TypeRef Type, FieldKind Kind, bool Param);

    /// One `pauseuntil`: its number (its `at`), the statement it stands in, what it waits for and the step's type.
    private sealed record Pause(int Number, Stmt Stmt, PauseExpr Expr, HashSet<string> Live);

    private sealed class Lowering(RoutineDecl r, string state, World world)
    {
        public RoutineDecl Routine => r;
        public List<Decl> Made { get; } = [];
        public string Shown { get; private set; } = "";

        /// The pausable routines this one waits for, and where.
        public List<(RoutineDecl, Pos)> Waits { get; } = [];

        private readonly Pos _pos = r.Pos;
        private readonly Dictionary<string, Field> _fields = [];
        private readonly Dictionary<string, (TypeRef Type, BindStmt? Bind)> _locals = [];
        private readonly Dictionary<Stmt, Pause> _pauses = new(ReferenceEqualityComparer.Instance);
        private readonly List<(TypeRef Step, TypeRef Result, bool Nested)> _steps = [];
        private readonly Dictionary<PauseExpr, (TypeRef Step, TypeRef Result, bool Nested)> _stepOf = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<string> _hidden = [];
        private string _at = "at", _room = "room";

        /// The field that keeps an access handed in for each view parameter, by the parameter's name.
        private readonly Dictionary<string, string> _handed = [];

        private string AccessField(string param)
        {
            string name = $"{param}_access";
            while (_locals.ContainsKey(name)) name = "pause_" + name;
            return name;
        }

        /// The fields that keep an access a view parameter may be handed with steal, by the parameter's name.
        public IReadOnlyDictionary<string, string> Handed => _handed;

        public Lowering Run()
        {
            var body = r.Blocks![0].Stmts;
            foreach (var p in r.Params) _locals[p.Name] = (p.Type, null);
            CollectLocals(body);
            CheckLines(body);
            int number = 0;
            NumberPauses(body, ref number);
            // The hidden fields take names no value of the routine has.
            while (_locals.ContainsKey(_at)) _at = "pause_" + _at;
            while (_locals.ContainsKey(_room)) _room = "pause_" + _room;
            foreach (var p in r.Params)
                _fields[p.Name] = new Field(p.Name, p.Type, world.IsEntity(p.Type) ? FieldKind.Cell : FieldKind.Value, Param: true);
            // A view parameter may be an access the work was handed with steal: the record gives it back when it ends.
            foreach (var p in r.Params.Where(p => p.Type is { Name: "PointedCell" or "PointedSlice", Path: null }))
                _handed[p.Name] = AccessField(p.Name);
            Analyze(body, new Ctx([], () => []));
            foreach (var pause in _pauses.Values) ResolveStep(pause.Expr);
            CheckCarrying();
            var resume = BuildResume(body);
            MakeDecls(resume);
            return this;
        }

        // ── What the routine binds ─────────────────────────────────────────────────────────────────────────────

        private void CollectLocals(List<Stmt> body)
        {
            foreach (var s in Bodies.All(body))
            {
                switch (s)
                {
                    case BindStmt b: Note(b.Name, b.Type, b); break;
                    case LoopStmt l:
                        foreach (var c in l.With) Note(c.Name, c.Type, null);
                        if (l.Var is { } v) Note(v, l.VarType ?? RangeType(l) ?? TypeRef.Simple("S64", l.Pos), null);
                        break;
                    case WhenStmt w:
                        foreach (var arm in w.Arms)
                            foreach (var c in arm.Cases ?? [])
                                if (c is IsPattern { Binding: { } bound } ip) Note(bound.Name, ip.Type, null);
                        break;
                }
                foreach (var e in Bodies.Exprs(s))
                    if (e is WhenExpr we)
                        foreach (var arm in we.When.Arms)
                            foreach (var c in arm.Cases ?? [])
                                if (c is IsPattern { Binding: { } bound } ip) Note(bound.Name, ip.Type, null);
            }
        }

        private void Note(string name, TypeRef type, BindStmt? bind)
        {
            // The same name bound twice (in two bodies) can't be one field: the first binding is the one a field takes.
            if (_locals.ContainsKey(name)) _hidden.Add(name);
            else _locals[name] = (type, bind);
        }

        /// The element type of a `for` over a range, read off a bound whose type the routine writes.
        private TypeRef? RangeType(LoopStmt l)
        {
            if (l.Source is not RangeExpr range) return null;
            foreach (var e in new[] { range.From, range.To })
                if (e is ValueRef v && _locals.TryGetValue(v.Name, out var known) && !known.Type.Amp) return known.Type;
            return null;
        }

        /// The lines a pausable routine can't have.
        private void CheckLines(List<Stmt> body)
        {
            foreach (var s in Bodies.All(body))
            {
                if (s is BindStmt { Borrows: true, Type: { Name: "PointedCell" or "PointedSlice", Path: null } } access)
                    throw new CompileError(Li.PausableAccess, access.Pos, $"'{access.Name}' takes an access with '<-' in pausable routine "
                        + $"'{r.Name}', which would hold it across its pauses: work that waits for the same access on this thread would "
                        + "never go on. Take the access outside, and hand the routine a view of it (held: @T), or take it in a routine "
                        + "that doesn't pause and give it back there");
                if (s is JumpStmt)
                    throw new CompileError(Li.PausableForm, s.Pos, "a pausable routine is written with if, when and loops: the builder writes its blocks");
                foreach (var top in Bodies.Exprs(s))
                    foreach (var e in ExprTree.All(top))
                        CheckCall(e);
            }
        }

        /// A retrieve() of work on this thread, which would run the manager inside one of its own steps.
        private void CheckCall(Expr e)
        {
            if (e is not MethodCallExpr { Name: "retrieve" } m) return;
            var receiver = m.Receiver is MethodCallExpr { Name: "waitfor" } w ? w.Receiver : m.Receiver;
            if (receiver is not ValueRef v || !_locals.TryGetValue(v.Name, out var known)) return;
            if (known.Type.Name is "Fiber" or "PausingFiber")
                throw new CompileError(Li.PausableRetrieve, m.Pos, $"'{v.Name}' is a {known.Type.Name} of this thread's CoroutineManager, and "
                    + $"its retrieve() inside pausable routine '{r.Name}' would run the manager inside one of its own steps: wait for it "
                    + $"with pauseuntil {v.Name}.finish(), which lets the manager run it");
        }

        private void NumberPauses(List<Stmt> body, ref int number)
        {
            foreach (var s in body)
            {
                if (PauseIn(s) is { } pause)
                {
                    number++;
                    _pauses[s] = new Pause(number, s, pause, []);
                }
                else CheckNoPause(s);
                foreach (var inner in Bodies.Inner(s))
                {
                    if (s is BindStmt or ReturnStmt or BecomesStmt or DestructureStmt)
                    {
                        // The arms of a when that is a value give one value: a pause there is in an expression.
                        foreach (var x in Bodies.All(inner))
                            if (PauseIn(x) is { } deep)
                                throw new CompileError(Li.PauseForm, deep.Pos, "a when that gives a value can't pause in its arms: bind "
                                    + "the pause's result to a name on a line of its own first, then use it in the arm");
                        continue;
                    }
                    NumberPauses(inner, ref number);
                }
            }
        }

        /// The pause a statement is, when it is one: `pauseuntil X` as a line, `try`/`check` in front of it, a binding of
        /// its value, or the value a `when` looks at.
        private static PauseExpr? PauseIn(Stmt s)
        {
            static PauseExpr? Bare(Expr? e) => e switch
            {
                PauseExpr p => p,
                UnaryExpr { Op: "try" or "check", Operand: PauseExpr p } => p,
                _ => null,
            };
            return s switch
            {
                ExprStmt e => Bare(e.Value),
                BindStmt { Value: WhenExpr w } => Bare(w.When.Value),
                BindStmt b => Bare(b.Value),
                WhenStmt w => Bare(w.Value),
                _ => null,
            };
        }

        /// A pause anywhere else in the statement's own expressions is in an expression, which can't stop half done.
        private static void CheckNoPause(Stmt s)
        {
            foreach (var top in Bodies.Exprs(s))
                if (s is not BindStmt { Value: WhenExpr } && ExprTree.All(top).OfType<PauseExpr>().FirstOrDefault() is { } deep)
                    throw new CompileError(Li.PauseForm, deep.Pos, "pauseuntil stands at the start of a line, as a binding's value, or as what a "
                        + "when looks at (try or check may go in front of it): the routine can't stop in the middle of an expression. "
                        + "Bind the result first: x: T = pauseuntil ...");
        }

        private static bool HasPause(Stmt s) => Bodies.All([s]).Any(x => PauseIn(x) is not null);

        // ── Which values a pause keeps ─────────────────────────────────────────────────────────────────────────

        /// What is in scope at a line and what the lines after it use: Visible holds the routine's values bound before
        /// the line, After the names the code after the line's body uses.
        private sealed record Ctx(HashSet<string> Visible, Func<HashSet<string>> After);

        private void Analyze(List<Stmt> list, Ctx ctx)
        {
            var visible = new HashSet<string>(ctx.Visible);
            for (int i = 0; i < list.Count; i++)
            {
                var s = list[i];
                int at = i;
                var seen = new HashSet<string>(visible);
                HashSet<string>? after = null;
                HashSet<string> AfterHere() => after ??= [.. UsedFrom(list, at + 1, []), .. ctx.After()];
                if (_pauses.TryGetValue(s, out var pause))
                {
                    var used = new HashSet<string>(AfterHere());
                    // `when pauseuntil X`: the arms run after the pause.
                    if (s is WhenStmt w) used.UnionWith(UsedArms(w));
                    if (s is BindStmt { Value: WhenExpr we }) used.UnionWith(UsedArms(we.When));
                    pause.Live.UnionWith(seen.Where(used.Contains));
                }
                // A value used in another block than the one that binds it is kept in the record.
                if (HasPause(s))
                {
                    var used = new HashSet<string>(AfterHere());
                    foreach (var inner in Bodies.Inner(s)) used.UnionWith(UsedFrom(inner, 0, []));
                    if (s is LoopStmt { Cond: { } cond }) used.UnionWith(Names(cond));
                    foreach (var n in seen.Where(used.Contains)) Keep(n, s.Pos);
                }
                switch (s)
                {
                    case IfStmt f:
                        Analyze(f.Then, new Ctx(seen, AfterHere));
                        if (f.Else is not null) Analyze(f.Else, new Ctx(seen, AfterHere));
                        break;
                    case WhenStmt w:
                        foreach (var arm in w.Arms)
                        {
                            var armSeen = new HashSet<string>(seen);
                            foreach (var c in arm.Cases ?? [])
                                if (c is IsPattern { Binding: { } b }) armSeen.Add(b.Name);
                            Analyze(arm.Body, new Ctx(armSeen, AfterHere));
                        }
                        break;
                    case LoopStmt l:
                    {
                        var round = new HashSet<string>(seen);
                        foreach (var c in l.With) round.Add(c.Name);
                        if (l.Var is { } v) round.Add(v);
                        // A round that ends in `continue with` every carried value gives the next round, and the then
                        // lines after the loop's own end, the new values: those uses don't read this round's.
                        var with = l.With.Select(c => c.Name).ToHashSet();
                        bool rebinds = with.Count > 0 && AlwaysLeaves(l.Body)
                                       && Bodies.All(l.Body).OfType<ContinueStmt>().All(c => c.Target is not null || c.With is { } w && with.All(n => w.Any(x => x.Name == n)));
                        bool breaks = Bodies.All(l.Body).Any(x => x is BreakStmt);
                        HashSet<string>? again = null;
                        HashSet<string> Again()
                        {
                            if (again is not null) return again;
                            var next = new HashSet<string>([.. l.Cond is null ? [] : Names(l.Cond), .. UsedFrom(l.Body, 0, l.Var is null ? [] : [l.Var])]);
                            var after = l.Then is null ? [] : UsedFrom(l.Then, 0, []);
                            if (rebinds) next.ExceptWith(with);
                            if (rebinds && !breaks) after.ExceptWith(with);
                            return again = [.. next, .. after, .. AfterHere()];
                        }
                        Analyze(l.Body, new Ctx(round, Again));
                        if (l.Then is not null)
                        {
                            var thenSeen = new HashSet<string>(seen);
                            foreach (var c in l.With) thenSeen.Add(c.Name);
                            Analyze(l.Then, new Ctx(thenSeen, AfterHere));
                        }
                        // The values a loop with a pause carries from round to round live in the record.
                        if (HasPause(l))
                            foreach (var c in l.With) Keep(c.Name, c.Pos);
                        break;
                    }
                }
                foreach (var b in Binds(s)) visible.Add(b);
            }
        }

        private static IEnumerable<string> Binds(Stmt s) => s switch
        {
            BindStmt b => [b.Name],
            DestructureStmt d => d.Names.Select(n => n.Name),
            StealStmt st => [st.Name],
            _ => [],
        };

        /// The names the lines of `list` from `from` on use, a name bound among them counting only before its line.
        private HashSet<string> UsedFrom(List<Stmt> list, int from, HashSet<string> shadow)
        {
            var used = new HashSet<string>();
            var hidden = new HashSet<string>(shadow);
            for (int i = from; i < list.Count; i++)
            {
                var s = list[i];
                foreach (var e in Bodies.Exprs(s))
                    used.UnionWith(Names(e).Where(n => !hidden.Contains(n)));
                if (s is ContinueStmt { With: { } with })
                    foreach (var (_, v, _) in with) used.UnionWith(Names(v).Where(n => !hidden.Contains(n)));
                if (s is ReturnStmt { Value: { } rv }) used.UnionWith(Names(rv).Where(n => !hidden.Contains(n)));
                if (s is LoopStmt l)
                {
                    foreach (var c in l.With) used.UnionWith(Names(c.Init).Where(n => !hidden.Contains(n)));
                    if (l.Source is not null) used.UnionWith(Names(l.Source).Where(n => !hidden.Contains(n)));
                    if (l.Cond is not null) used.UnionWith(Names(l.Cond).Where(n => !hidden.Contains(n)));
                }
                foreach (var inner in Bodies.Inner(s))
                {
                    var innerShadow = new HashSet<string>(hidden);
                    if (s is LoopStmt lp && lp.Var is { } v) innerShadow.Add(v);
                    used.UnionWith(UsedFrom(inner, 0, innerShadow));
                }
                foreach (var b in Binds(s)) hidden.Add(b);
            }
            return used;
        }

        private HashSet<string> UsedArms(WhenStmt w)
        {
            var used = new HashSet<string>();
            foreach (var arm in w.Arms) used.UnionWith(UsedFrom(arm.Body, 0, []));
            return used;
        }

        /// The value names an expression reads: its names, those in the holes of its text, and not the names a
        /// `carrying` list writes.
        private static HashSet<string> Names(Expr e)
        {
            var names = new HashSet<string>();
            var listed = new HashSet<ValueRef>(ReferenceEqualityComparer.Instance);
            foreach (var x in ExprTree.All(e))
                if (x is PauseExpr p)
                    foreach (var c in p.Carrying) listed.Add(c);
            foreach (var x in ExprTree.All(e))
            {
                if (x is ValueRef v && !listed.Contains(v)) names.Add(v.Name);
                if (x is StrLit s)
                    foreach (Match m in HoleName.Matches(HoleText(s.Value))) names.Add(m.Value);
            }
            return names;
        }

        private static readonly Regex HoleName = new(@"(?<![\.\w])[a-z_][A-Za-z0-9_]*", RegexOptions.Compiled);

        /// The text inside a string's `{...}` holes.
        private static string HoleText(string s)
        {
            var sb = new StringBuilder();
            for (int i = 0; i < s.Length; i++)
            {
                if (s[i] == '{' && i + 1 < s.Length && s[i + 1] == '{')
                {
                    i++;
                    continue;
                }
                if (s[i] != '{') continue;
                int end = Lexer.HoleEnd(s, i);
                if (end < 0) break;
                sb.Append(' ').Append(s, i + 1, end - i - 1);
                i = end;
            }
            return sb.ToString();
        }

        /// Makes `name` a field of the record.
        private void Keep(string name, Pos at)
        {
            if (_fields.ContainsKey(name)) return;
            if (!_locals.TryGetValue(name, out var local))
                throw new CompileError(Li.CarryingMissing, at, $"'{name}' is kept across a pause, and the builder can't tell its type: bind it "
                    + $"with one, {name}: T = ...");
            if (_hidden.Contains(name))
                throw new CompileError(Li.CarryingMissing, at, $"'{name}' is kept across a pause, and pausable routine '{r.Name}' binds two "
                    + "values of that name: give one of them another name");
            _fields[name] = local.Bind is { Borrows: true } b ? CellField(b) : new Field(name, local.Type, FieldKind.Value, Param: false);
        }

        /// The field a `<-` name kept across a pause becomes.
        private Field CellField(BindStmt b)
        {
            var t = b.Type;
            if (t is { Amp: true, Name: "BorrowedSlice" } && b.Value is ArrayLit)
                throw new CompileError(Li.CarryingStackView, b.Pos, $"'{b.Name}' is a run of values in the routine's frame (STACK), kept across a "
                    + $"pause: a pausable routine's frame goes away at each pause. Borrow it from a manager, {b.Name}: {t} <- ... from HEAP");
            // A STACK place holds its value in the record. A place from a manager, a thing a call lends (a ticket, a
            // BorrowedCell / BorrowedSlice a routine returns) is kept as it is, and gives its memory back itself.
            if (t is { Amp: true, Name: "BorrowedCell", Args: [TypeArgType inner] } && !GivesPlace(b.Value))
                return new Field(b.Name, inner.Type, FieldKind.Cell, Param: false);
            if (!t.Amp && !GivesPlace(b.Value) && !world.IsEntity(t))
                return new Field(b.Name, t, FieldKind.Cell, Param: false);
            return new Field(b.Name, t, FieldKind.Holder, Param: false);
        }

        /// Whether the value of a `<-` line is a place from a manager or a call that lends one, rather than a value
        /// put in a STACK place.
        private bool GivesPlace(Expr value)
        {
            if (value is AtExpr) return true;
            IEnumerable<RoutineDecl> called = value switch
            {
                CallExpr c => world.Free.GetValueOrDefault(c.Name) ?? [],
                MethodCallExpr m => world.Methods.Where(kv => kv.Key.Name == m.Name).SelectMany(kv => kv.Value),
                NsCallExpr n => world.Methods.GetValueOrDefault((n.Owner.Name, n.Name)) ?? [],
                _ => [],
            };
            return called.Any(d => d.ReturnType is { Amp: true } or { Name: "BorrowedCell" or "BorrowedSlice" or "Thread" or "Fiber" or "PausingFiber" or "PassableFiber" });
        }

        /// Every value a pause keeps is in its carrying list, and the list names values of the routine.
        private void CheckCarrying()
        {
            foreach (var pause in _pauses.Values.OrderBy(p => p.Number))
            {
                var listed = pause.Expr.Carrying.Select(c => c.Name).ToHashSet();
                foreach (var c in pause.Expr.Carrying)
                    if (!_locals.ContainsKey(c.Name))
                        throw new CompileError(Li.CarryingMissing, c.Pos, $"carrying names '{c.Name}', which isn't a value of pausable routine '{r.Name}'");
                var missing = pause.Live.Where(n => !listed.Contains(n) && !r.Params.Any(p => p.Name == n)).Order(StringComparer.Ordinal).ToList();
                if (missing.Count > 0)
                {
                    var all = pause.Expr.Carrying.Select(c => c.Name).Concat(missing);
                    throw new CompileError(Li.CarryingMissing, pause.Expr.Pos, $"{Quoted(missing)} {(missing.Count == 1 ? "is" : "are")} used after this "
                        + $"pause, and the routine's frame goes away while it waits: list {(missing.Count == 1 ? "it" : "them")} in carrying, "
                        + $"pauseuntil ... carrying ({string.Join(", ", all)})");
                }
                foreach (var c in pause.Expr.Carrying)
                {
                    Keep(c.Name, c.Pos);
                    CheckNotFrameView(c.Name, pause);
                }
            }
        }

        /// A view carried across a pause may not point into the routine's frame: the frame is gone while it waits.
        private void CheckNotFrameView(string name, Pause pause)
        {
            var (type, bind) = _locals[name];
            if (type is not { Name: "PointedCell" or "PointedSlice", Path: null } || bind is null) return;
            foreach (var e in ExprTree.All(bind.Value))
                if (e is ValueRef v && _locals.TryGetValue(v.Name, out var of) && of.Bind is { Borrows: true } cell && !_fields.ContainsKey(v.Name)
                    && !GivesPlace(cell.Value))
                    throw new CompileError(Li.CarryingStackView, pause.Expr.Pos, $"'{name}' views '{v.Name}', a place in the routine's frame "
                        + $"(STACK), and carrying keeps the view across this pause, while the frame goes away: carry '{v.Name}' itself, "
                        + $"which puts it in the state record, carrying ({string.Join(", ", pause.Expr.Carrying.Select(c => c.Name).Append(v.Name))})");
        }

        private static string Quoted(List<string> names) => names.Count == 1 ? $"'{names[0]}'"
            : string.Join(", ", names.Take(names.Count - 1).Select(n => $"'{n}'")) + $" and '{names[^1]}'";

        // ── The step a pause waits for ─────────────────────────────────────────────────────────────────────────

        private void ResolveStep(PauseExpr pause)
        {
            if (world.PausableCalled(pause.Target, r.Module) is var (callee, calleeState))
            {
                Waits.Add((callee, pause.Pos));
                var step = new TypeRef(calleeState, [], pause.Pos);
                _stepOf[pause] = (step, callee.ReturnType, true);
                _steps.Add(_stepOf[pause]);
                return;
            }
            var stepType = TypeOf(pause.Target)
                ?? throw new CompileError(Li.PauseTarget, pause.Target.Pos, "the builder can't tell the type of what this pause waits for: bind it "
                    + "to a name with its type on the line before, step: ClockStep = Clock.after(5ms), then pauseuntil step");
            var result = ResultOf(stepType)
                ?? throw new CompileError(Li.PauseTarget, pause.Target.Pos, $"a pause waits for a pausable routine's call or an Eventual[T] step, "
                    + $"and this gives {stepType}, which doesn't obey Eventual: a plain routine runs to its end, so call it without pauseuntil");
            _stepOf[pause] = (stepType, result, false);
            _steps.Add(_stepOf[pause]);
        }

        /// The type of an expression whose type the declarations show: a value of the routine, a global, a call of a
        /// routine (its declared result), a record made by its type's name.
        private TypeRef? TypeOf(Expr e)
        {
            switch (e)
            {
                case ValueRef v when _locals.TryGetValue(v.Name, out var known): return Held(known.Type);
                case ValueRef v when world.Globals.TryGetValue(v.Name, out var globals) && globals.Count == 1: return Held(globals[0].Type);
                case PresetRef { Owner: null } p when world.Globals.TryGetValue(p.Name, out var presets) && presets.Count == 1: return Held(presets[0].Type);
                case CallExpr c when world.Types.TryGetValue(c.Name, out var types) && types.OfType<RecordDecl>().Any():
                    return new TypeRef(c.Name, c.TypeArgs.Select(a => (TypeArg)new TypeArgType(a)).ToList(), c.Pos) { Path = c.Path };
                case CallExpr c when world.Free.TryGetValue(c.Name, out var routines):
                    return SameResult(routines.Select(d => Subst(d.ReturnType, Bind(d.TypeParams, c.TypeArgs), null)));
                case NsCallExpr { Owner.Args.Count: 0 } n when !world.Types.ContainsKey(n.Owner.Name)
                                                              && TypeOf(new ValueRef(n.Owner.Name, n.Pos)) is { } recv
                                                              && world.Methods.TryGetValue((recv.Name, n.Name), out var onGlobal):
                    return SameResult(onGlobal.Select(d => Subst(d.ReturnType, Bind(OwnerParams(d), recv.Args.OfType<TypeArgType>().Select(a => a.Type).ToList()), recv)));
                case NsCallExpr n when world.Methods.TryGetValue((n.Owner.Name, n.Name), out var common):
                    return SameResult(common.Select(d => Subst(d.ReturnType, Bind(OwnerParams(d), n.Owner.Args.OfType<TypeArgType>().Select(a => a.Type).ToList()), n.Owner)));
                case MethodCallExpr m when TypeOf(m.Receiver) is { } recv && world.Methods.TryGetValue((recv.Name, m.Name), out var methods):
                    return SameResult(methods.Select(d => Subst(d.ReturnType, Bind(OwnerParams(d), recv.Args.OfType<TypeArgType>().Select(a => a.Type).ToList()), recv)));
                default: return null;
            }
        }

        /// The value a place or a view holds: `&T` and `@T` are where a `T` is.
        private static TypeRef Held(TypeRef t) => t switch
        {
            { Amp: true, Name: "BorrowedCell", Args: [TypeArgType inner] } => inner.Type,
            { Name: "PointedCell", Path: null, Args: [TypeArgType inner] } => inner.Type,
            _ => t,
        };

        private static TypeRef? SameResult(IEnumerable<TypeRef> results)
        {
            var distinct = results.GroupBy(t => t.ToString()).Select(g => g.First()).ToList();
            return distinct is [var one] ? one : null;
        }

        private static List<string> OwnerParams(RoutineDecl d)
        {
            var owner = d.Owner is { Name: "PointedCell", Args: [TypeArgType inner] } ? inner.Type : d.Owner!;
            return owner.Args.Select(a => a is TypeArgType { Type: { Args.Count: 0 } t } ? t.Name : "").ToList();
        }

        private static Dictionary<string, TypeRef> Bind(List<string> names, List<TypeRef> args)
        {
            var map = new Dictionary<string, TypeRef>();
            for (int i = 0; i < names.Count && i < args.Count; i++)
                if (names[i] != "") map[names[i]] = args[i];
            return map;
        }

        private static TypeRef Subst(TypeRef t, Dictionary<string, TypeRef> map, TypeRef? me)
        {
            if (t.Path is null && t.Args.Count == 0)
            {
                if (map.TryGetValue(t.Name, out var bound)) return bound;
                if (t.Name == "Me" && me is not null) return me;
            }
            return t with
            {
                Args = t.Args.Select(a => a switch
                {
                    TypeArgType at => new TypeArgType(Subst(at.Type, map, me)),
                    TypeArgTuple tu => new TypeArgTuple(tu.Types.Select(x => Subst(x, map, me)).ToList()),
                    _ => a,
                }).ToList(),
            };
        }

        /// The `T` of the `Eventual[S, T]` a step's type obeys.
        private TypeRef? ResultOf(TypeRef step)
        {
            if (!world.Types.TryGetValue(step.Name, out var decls)) return null;
            foreach (var d in decls)
            {
                var (typeParams, clauses) = d switch
                {
                    RecordDecl x => (x.TypeParams, x.Clauses),
                    VariantDecl v => (v.TypeParams, v.Clauses),
                    _ => ([], []),
                };
                foreach (var c in clauses.Where(c => c.Kind == "conform").SelectMany(c => c.Concepts))
                    if (c.Name == "Eventual" && c.Args is [_, TypeArgType result])
                        return Subst(result.Type, Bind(typeParams, step.Args.OfType<TypeArgType>().Select(a => a.Type).ToList()), step);
            }
            return null;
        }

        // ── The record's resume ────────────────────────────────────────────────────────────────────────────────

        private readonly List<BlockDecl> _blocks = [];
        private List<Stmt> _cur = [];
        private int _labels;

        /// A loop turned into blocks: where its rounds start and where it is left.
        private sealed record LoopBlocks(string? Name, string Head, string Exit, LoopStmt Loop, string? Next);

        private readonly List<LoopBlocks> _loops = [];

        private List<BlockDecl> BuildResume(List<Stmt> body)
        {
            var entry = new List<Stmt>();
            foreach (var pause in _pauses.Values.OrderBy(p => p.Number))
                entry.Add(new IfStmt(new BinaryExpr("==", Peek(_at), new IntLit(pause.Number, _pos), _pos),
                    [new JumpStmt(Wait(pause.Number), [], _pos)], null, _pos));
            _cur = entry;
            _blocks.Add(new BlockDecl("entry", [], entry, _pos));
            EmitList(body);
            return _blocks;
        }

        private static string Wait(int number) => $"pause{number}";

        private void StartBlock(string name, List<Param>? ps = null)
        {
            _cur = [];
            _blocks.Add(new BlockDecl(name, ps ?? [], _cur, _pos));
        }

        private string Label(string what) => $"{what}{++_labels}";

        /// Emits `list` into the current block and the blocks it needs. Returns whether the lines may go on past their
        /// end (no return or jump on every path).
        private bool EmitList(List<Stmt> list)
        {
            foreach (var s in list)
            {
                if (!HasPause(s))
                {
                    _cur.AddRange(Rewrite(s, 0));
                    if (AlwaysLeaves([s])) return false;
                    continue;
                }
                if (_pauses.TryGetValue(s, out var pause))
                {
                    EmitPause(pause);
                    continue;
                }
                switch (s)
                {
                    case IfStmt f:
                    {
                        string then = Label("then"), join = Label("join");
                        string? other = f.Else is null ? null : Label("else");
                        _cur.Add(new IfStmt(RewriteExpr(f.Cond), [Jump(then)], [Jump(other ?? join)], f.Pos));
                        StartBlock(then);
                        if (EmitList(f.Then)) _cur.Add(Jump(join));
                        if (other is not null)
                        {
                            StartBlock(other);
                            if (EmitList(f.Else!)) _cur.Add(Jump(join));
                        }
                        StartBlock(join);
                        break;
                    }
                    case WhenStmt w:
                        EmitWhen(w, w.Value is null ? null : RewriteExpr(w.Value), [], null);
                        break;
                    case LoopStmt l:
                        EmitLoop(l);
                        break;
                    default:
                        throw new CompileError(Li.PauseForm, s.Pos, "a pause can't stand inside this line");
                }
            }
            return true;
        }

        /// Whether lines leave on every path: a return, a jump, a break or continue, or an if or when whose every arm does.
        private static bool AlwaysLeaves(List<Stmt> lines) => lines.Count > 0 && lines[^1] switch
        {
            ReturnStmt or JumpStmt or BreakStmt or ContinueStmt or UnreachableStmt or TodoStmt => true,
            IfStmt { Else: { } other } f => AlwaysLeaves(f.Then) && AlwaysLeaves(other),
            WhenStmt w => w.Arms.Any(a => a.IsElse) && w.Arms.All(a => AlwaysLeaves(a.Body)),
            LoopStmt l => l.NeverEndsByItself && !Bodies.All(l.Body).Any(x => x is BreakStmt),
            _ => false,
        };

        /// A `when` whose arms pause: each such arm goes on in a block of its own, taking the arm's value.
        private void EmitWhen(WhenStmt w, Expr? subject, List<Stmt> armPrefix, WhenArm? first)
        {
            string join = Label("join");
            var arms = new List<WhenArm>();
            if (first is not null) arms.Add(first);
            var later = new List<(string Block, WhenArm Arm, Param? Bound)>();
            foreach (var arm in w.Arms)
            {
                var bound = arm.Cases?.OfType<IsPattern>().FirstOrDefault(c => c.Binding is not null);
                if (!arm.Body.Any(HasPause))
                {
                    var lines = new List<Stmt>(armPrefix);
                    lines.AddRange(arm.Body.SelectMany(x => Rewrite(x, 0)));
                    if (BindsField(bound) is { } poke) lines.Insert(armPrefix.Count, poke);
                    if (!AlwaysLeaves(arm.Body)) lines.Add(Jump(join));
                    arms.Add(arm with { Body = lines, OneLine = false });
                    continue;
                }
                string block = Label("arm");
                var p = bound is { Binding: { } b } ? new Param(b.Name, bound.Type, b.Pos) : null;
                var go = new List<Stmt>(armPrefix) { new JumpStmt(block, p is null ? [] : [new ValueRef(p.Name, _pos)], _pos) };
                arms.Add(arm with { Body = go, OneLine = false });
                later.Add((block, arm, p));
            }
            _cur.Add(new WhenStmt(subject, arms, w.Pos) { ElseBinding = w.ElseBinding });
            // A when without an else over conditions may take no arm.
            if (subject is null && !w.Arms.Any(a => a.IsElse)) _cur.Add(Jump(join));
            foreach (var (block, arm, p) in later)
            {
                StartBlock(block, p is null ? [] : [p]);
                if (p is not null && _fields.ContainsKey(p.Name)) _cur.Add(PokeField(p.Name, new ValueRef(p.Name, _pos)));
                if (EmitList(arm.Body)) _cur.Add(Jump(join));
            }
            StartBlock(join);
        }

        /// The poke that keeps a when arm's value in its field, when the value is kept across a pause.
        private Stmt? BindsField(IsPattern? bound) =>
            bound?.Binding is { } b && _fields.ContainsKey(b.Name) ? PokeField(b.Name, new ValueRef(b.Name, _pos)) : null;

        private void EmitLoop(LoopStmt l)
        {
            string head = Label("loop"), body = Label("round"), exit = Label("after");
            string? next = null, end = null;
            foreach (var c in l.With) _cur.Add(PokeField(c.Name, RewriteExpr(c.Init)));
            if (l.Kind == LoopKind.For)
            {
                if (l.Source is not RangeExpr range)
                    throw new CompileError(Li.PauseForm, l.Pos, "a for over an emitter can't pause inside its body yet: walk the indices with "
                        + "for i in 0 til xs.count(), or pause in a loop of your own");
                if (range.Step is not (null or IntLit { Value.Sign: > 0 }))
                    throw new CompileError(Li.PauseForm, range.Step.Pos, "a for with a pause inside takes a step that is a positive number");
                var type = l.VarType ?? RangeType(l) ?? TypeRef.Simple("S64", l.Pos);
                next = Hidden($"{head}_next");
                end = Hidden($"{head}_end");
                _fields[next] = new Field(next, type, FieldKind.Value, false);
                _fields[end] = new Field(end, type, FieldKind.Value, false);
                _cur.Add(PokeField(next, RewriteExpr(range.From)));
                _cur.Add(PokeField(end, RewriteExpr(range.To)));
                _cur.Add(Jump(head));
                StartBlock(head);
                _cur.Add(new IfStmt(new BinaryExpr(range.Inclusive ? "<=" : "<", Peek(next), Peek(end), l.Pos), [Jump(body)], null, l.Pos));
                _cur.Add(Jump(exit));
                StartBlock(body);
                var index = Peek(next);
                if (_fields.ContainsKey(l.Var!)) _cur.Add(PokeField(l.Var!, index));
                else _cur.Add(new BindStmt(l.Var!, type, index, l.Pos));
                _cur.Add(PokeField(next, new BinaryExpr("+", Peek(next), range.Step ?? new IntLit(1, l.Pos), l.Pos)));
            }
            else
            {
                _cur.Add(Jump(head));
                StartBlock(head);
                if (l.NeverEndsByItself) _cur.Add(Jump(body));
                else
                {
                    var cond = RewriteExpr(l.Cond!);
                    var (go, stop) = l.Kind == LoopKind.Until ? (exit, body) : (body, exit);
                    _cur.Add(new IfStmt(cond, [Jump(go)], null, l.Pos));
                    _cur.Add(Jump(stop));
                }
                StartBlock(body);
            }
            _loops.Add(new LoopBlocks(l.Name, head, exit, l, next));
            if (EmitList(l.Body)) _cur.Add(Jump(head));
            _loops.RemoveAt(_loops.Count - 1);
            StartBlock(exit);
            // A loop only a return or throw leaves never gets here.
            if (l.NeverEndsByItself && !Bodies.All(l.Body).Any(x => x is BreakStmt)) _cur.Add(new UnreachableStmt(l.Pos));
            else if (l.Then is not null) EmitList(l.Then);
        }

        private string Hidden(string name)
        {
            while (_locals.ContainsKey(name) || _fields.ContainsKey(name)) name = "pause_" + name;
            return name;
        }

        /// `pauseuntil X`: the block that puts X in the room and the block that asks it for its result.
        private void EmitPause(Pause pause)
        {
            var (step, result, nested) = _stepOf[pause.Expr];
            var p = pause.Expr;
            // What isn't carried is given back before the routine stops: the frame's names at the jump, the kept places here.
            foreach (var f in _fields.Values.Where(f => f.Kind != FieldKind.Value && !f.Param && !pause.Live.Contains(f.Name)
                                                         && !p.Carrying.Any(c => c.Name == f.Name)))
                _cur.Add(new ExprStmt(Call(FieldOf(f.Name), "end"), p.Pos));
            Expr made = nested && p.Target is CallExpr call
                ? new NsCallExpr(step, "construct", [], call.Args.Select(RewriteExpr).ToList(), call.Pos) { ArgNames = call.ArgNames }
                : RewriteExpr(p.Target);
            _cur.Add(new ExprStmt(new MethodCallExpr(FieldOf(_room), "hold", [step], [made], p.Pos), p.Pos));
            _cur.Add(new ExprStmt(Call(FieldOf(_at), "poke", new IntLit(pause.Number, p.Pos)), p.Pos));
            _cur.Add(Jump(Wait(pause.Number)));
            StartBlock(Wait(pause.Number));
            string stepName = Hidden($"pause{pause.Number}_step");
            _cur.Add(new BindStmt(stepName, new TypeRef("PointedCell", [new TypeArgType(step)], p.Pos),
                new MethodCallExpr(FieldOf(_room), "place", [step], [], p.Pos), p.Pos));
            Expr poll = nested
                ? new MethodCallExpr(new ValueRef(stepName, p.Pos), "resume", [], [], p.Pos)
                : new CallExpr("poll_step", [step, result], [new ValueRef(stepName, p.Pos)], p.Pos) { Path = "Fiber" };
            var pending = new WhenArm(null, [new IsPattern(PendingType(p.Pos), null, p.Pos)],
                [new ReturnStmt(new CallExpr("Pending", [], [], p.Pos) { Path = "Fiber" }, p.Pos)], p.Pos);
            var end = new ExprStmt(Call(FieldOf(_room), "end"), p.Pos);
            switch (pause.Stmt)
            {
                case ExprStmt { Value: var v }:
                {
                    var subject = v is UnaryExpr u ? u with { Operand = poll } : poll;
                    var rest = new WhenArm(null, null, [new NothingStmt(p.Pos)], p.Pos);
                    _cur.Add(new WhenStmt(subject, [pending, rest], p.Pos));
                    _cur.Add(end);
                    break;
                }
                case BindStmt { Value: WhenExpr we } b:
                {
                    var subject = we.When.Value is UnaryExpr u ? u with { Operand = poll } : poll;
                    var arms = new List<WhenArm> { pending };
                    foreach (var arm in we.When.Arms)
                    {
                        var lines = new List<Stmt> { end };
                        if (BindsField(arm.Cases?.OfType<IsPattern>().FirstOrDefault(c => c.Binding is not null)) is { } poke) lines.Add(poke);
                        lines.AddRange(arm.Body.SelectMany(x => Rewrite(x, 0)));
                        arms.Add(arm with { Body = lines, OneLine = false });
                    }
                    var value = new WhenExpr(new WhenStmt(subject, arms, we.When.Pos) { ElseBinding = we.When.ElseBinding }, we.Pos);
                    BindValue(b, value);
                    break;
                }
                case BindStmt b:
                {
                    if (b.Value is UnaryExpr { Op: "check" })
                        throw new CompileError(Li.PauseForm, b.Pos, $"'{b.Name}' takes a check of a pause, and a Check comes only from the check "
                            + "that makes it, while a pause gives its result after it waits: observe the failures with when check pauseuntil ... "
                            + "and its arms, or take an Optional with try pauseuntil ...");
                    if (b.Borrows)
                        throw new CompileError(Li.PauseForm, b.Pos, $"'{b.Name}' takes a pause's result with '<-': a pause gives a value bound with "
                            + "'=' for now, so a step whose result is an entity can't be waited for yet");
                    var (subject, arms) = b.Value switch
                    {
                        UnaryExpr { Op: "try" } u => ((Expr)(u with { Operand = poll }), ValueArms(b.Type is { Question: true, Args: [TypeArgType t] } ? t.Type : null, b, orNone: true)),
                        _ => (poll, ValueArms(b.Type, b, orNone: false)),
                    };
                    var value = new WhenExpr(new WhenStmt(subject, [pending, .. arms], p.Pos), p.Pos);
                    BindValue(b, value);
                    _cur.Add(end);
                    break;
                }
                case WhenStmt w:
                {
                    var subject = w.Value is UnaryExpr u ? u with { Operand = poll } : poll;
                    EmitWhen(w, subject, [end], pending);
                    break;
                }
            }
        }

        /// The arms that take a pause's result: `is T as v => v`, and for a try the empty one, `is None => none`.
        private List<WhenArm> ValueArms(TypeRef? value, BindStmt b, bool orNone)
        {
            if (value is null)
                throw new CompileError(Li.PauseForm, b.Pos, $"'{b.Name}' takes a pause with try, so its type is T?, what try gives");
            string got = Hidden("pause_value");
            var arms = new List<WhenArm>
            {
                new(null, [new IsPattern(value, new ValueRef(got, b.Pos), b.Pos)], [new BecomesStmt(new ValueRef(got, b.Pos), b.Pos)], b.Pos),
            };
            if (orNone) arms.Add(new WhenArm(null, [new IsPattern(TypeRef.Simple("None", b.Pos), null, b.Pos)], [new BecomesStmt(Compiler.NoneValue(b.Pos), b.Pos)], b.Pos));
            return arms;
        }

        /// `name: T = value` in the block, and in the record too when the name is kept across a pause.
        private void BindValue(BindStmt b, Expr value)
        {
            _cur.Add(new BindStmt(b.Name, b.Type, value, b.Pos));
            if (_fields.ContainsKey(b.Name)) _cur.Add(PokeField(b.Name, new ValueRef(b.Name, b.Pos)));
        }

        private static TypeRef PendingType(Pos pos) => new("Pending", [], pos) { Path = "Fiber" };

        private JumpStmt Jump(string block) => new(block, [], _pos);

        // ── Names to fields ────────────────────────────────────────────────────────────────────────────────────

        private Expr Me() => new ValueRef("me", _pos);
        private FieldExpr FieldOf(string name) => new(Me(), name, _pos);
        private static MethodCallExpr Call(Expr receiver, string name, params Expr[] args) => new(receiver, name, [], [.. args], receiver.Pos);
        private Expr Peek(string field) => Call(FieldOf(field), "peek");

        /// The view of the value a kept place holds: `me.x.value`.
        private Expr Held(string field) => new FieldExpr(FieldOf(field), "value", _pos);

        private Stmt PokeField(string name, Expr value)
        {
            var f = _fields[name];
            return f.Kind == FieldKind.Value
                ? new ExprStmt(Call(FieldOf(name), "poke", value), value.Pos)
                : new ExprStmt(Call(FieldOf(name), "fill", value), value.Pos);
        }

        private List<Stmt> Rewrite(Stmt s, int innerLoops) => RewriteOne(s, innerLoops) switch
        {
            IfStmt { Cond: BoolLit { Value: true }, Else: null } grouped when grouped.Pos.Line < 0 => grouped.Then,
            var one => [one],
        };

        private Stmt RewriteOne(Stmt s, int innerLoops)
        {
            switch (s)
            {
                case BindStmt b when _fields.TryGetValue(b.Name, out var f):
                {
                    if (b.Value is WhenExpr we)
                    {
                        // A when value can't be poked: bind it in the block, then keep it.
                        return Group([new BindStmt(b.Name, b.Type, RewriteExpr(we), b.Pos), PokeField(b.Name, new ValueRef(b.Name, b.Pos))]);
                    }
                    if (b.Bare && f.Kind == FieldKind.Value) return new ExprStmt(Call(FieldOf(b.Name), "zeroinit", new IntLit(1, b.Pos)), b.Pos);
                    if (b.Bare) return new NothingStmt(b.Pos);
                    return PokeField(b.Name, RewriteExpr(b.Value));
                }
                case BindStmt b: return b with { Value = RewriteExpr(b.Value) };
                case DestructureStmt d when d.Names.Any(n => _fields.ContainsKey(n.Name)):
                    throw new CompileError(Li.CarryingMissing, d.Pos, "a value taken out of a tuple is kept across a pause: bind it with its type, "
                        + "x: T = pair.item0, so the builder can keep it");
                case DestructureStmt d: return d with { Value = RewriteExpr(d.Value) };
                case ExprStmt e: return e with { Value = RewriteExpr(e.Value) };
                case DropStmt { Value: ValueRef v } d when _fields.TryGetValue(v.Name, out var f):
                    return f.Kind == FieldKind.Value ? new NothingStmt(d.Pos) : new ExprStmt(Call(FieldOf(v.Name), "end"), d.Pos);
                case DropStmt d: return d with { Value = RewriteExpr(d.Value) };
                case FillStmt { Place: ValueRef v } fill when _fields.ContainsKey(v.Name):
                    return new ExprStmt(Call(FieldOf(v.Name), "fill", RewriteExpr(fill.Value)), fill.Pos);
                case FillStmt fill: return fill with { Place = RewriteExpr(fill.Place), Value = RewriteExpr(fill.Value) };
                case StealStmt st when _fields.ContainsKey(st.Name):
                    throw new CompileError(Li.CarryingMissing, st.Pos, $"'{st.Name}' takes a value with steal ... as {st.Name}, and is kept across a "
                        + $"pause: bind it with '<-' instead, {st.Name}: &T <- steal ...");
                case StealStmt st: return st with { From = RewriteExpr(st.From), Inject = st.Inject is null ? null : RewriteExpr(st.Inject) };
                case IfStmt f:
                    return f with { Cond = RewriteExpr(f.Cond), Then = f.Then.SelectMany(x => Rewrite(x, innerLoops)).ToList(), Else = f.Else?.SelectMany(x => Rewrite(x, innerLoops)).ToList() };
                case WhenStmt w:
                    return w with
                    {
                        Value = w.Value is null ? null : RewriteExpr(w.Value),
                        Arms = w.Arms.Select(a =>
                        {
                            var lines = a.Body.SelectMany(x => Rewrite(x, innerLoops)).ToList();
                            if (BindsField(a.Cases?.OfType<IsPattern>().FirstOrDefault(c => c.Binding is not null)) is { } poke) lines.Insert(0, poke);
                            return a with { Cond = a.Cond is null ? null : RewriteExpr(a.Cond), Cases = a.Cases?.Select(RewriteExpr).ToList(), Body = lines, OneLine = a.OneLine && lines.Count == a.Body.Count };
                        }).ToList(),
                    };
                case LoopStmt l:
                    if (l.With.Any(c => _fields.ContainsKey(c.Name)) || l.Var is { } lv && _fields.ContainsKey(lv))
                        throw new CompileError(Li.CarryingMissing, l.Pos, "a value of this loop is kept across a pause outside it: give it another name "
                            + "in the loop");
                    return l with
                    {
                        Cond = l.Cond is null ? null : RewriteExpr(l.Cond),
                        Source = l.Source is null ? null : RewriteExpr(l.Source),
                        With = l.With.Select(c => c with { Init = RewriteExpr(c.Init) }).ToList(),
                        Body = l.Body.SelectMany(x => Rewrite(x, innerLoops + 1)).ToList(),
                        Then = l.Then?.SelectMany(x => Rewrite(x, innerLoops)).ToList(),
                    };
                case ReturnStmt { IsThrow: true } t: return t with { Value = t.Value is null ? null : RewriteExpr(t.Value) };
                case ReturnStmt ret: return Finish(ret);
                case BecomesStmt b: return b with { Value = RewriteExpr(b.Value) };
                case BreakStmt br when Target(br.Target, innerLoops) is { } loop: return Jump(loop.Exit);
                case ContinueStmt c when Target(c.Target, innerLoops) is { } loop:
                {
                    // Every new value is computed from the round's values before any of them changes.
                    var lines = new List<Stmt>();
                    var temps = new List<(string Field, string Temp)>();
                    foreach (var (name, value, at) in c.With ?? [])
                    {
                        string temp = Hidden($"{name}_next");
                        var type = loop.Loop.With.First(w => w.Name == name).Type;
                        lines.Add(new BindStmt(temp, type, RewriteExpr(value), at));
                        temps.Add((name, temp));
                    }
                    foreach (var (name, temp) in temps) lines.Add(PokeField(name, new ValueRef(temp, c.Pos)));
                    lines.Add(Jump(loop.Head));
                    return Group(lines);
                }
                case ContinueStmt c: return c with { With = c.With?.Select(w => (w.Name, RewriteExpr(w.Value), w.Pos)).ToList() };
                default: return s;
            }
        }

        /// Several lines standing for one: Rewrite spreads them out where the one was.
        private static Stmt Group(List<Stmt> lines) => lines.Count == 1 ? lines[0] : new IfStmt(new BoolLit(true, default), lines, null, new Pos("", -1, 0));

        /// The loop of the routine's that a break or continue leaves, when the builder turned it into blocks.
        private LoopBlocks? Target(string? name, int innerLoops)
        {
            if (name is not null) return _loops.LastOrDefault(l => l.Name == name);
            return innerLoops == 0 && _loops.Count > 0 ? _loops[^1] : null;
        }

        /// `return v`: the routine's end. The places it keeps in the record end here, the last made first.
        private Stmt Finish(ReturnStmt ret)
        {
            var kept = _fields.Values.Where(f => f.Kind != FieldKind.Value).Reverse().ToList();
            var value = ret.Value is null ? Compiler.NoneValue(ret.Pos) : RewriteExpr(ret.Value);
            if (kept.Count == 0) return ret with { Value = value };
            string result = Hidden("pause_result");
            var lines = new List<Stmt> { new BindStmt(result, r.ReturnType, value, ret.Pos) };
            foreach (var f in kept) lines.Add(new ExprStmt(Call(FieldOf(f.Name), "end"), ret.Pos));
            lines.Add(new ReturnStmt(new ValueRef(result, ret.Pos), ret.Pos));
            return Group(lines);
        }

        private Expr RewriteExpr(Expr e)
        {
            switch (e)
            {
                case ValueRef v when _fields.TryGetValue(v.Name, out var f):
                    return f.Kind == FieldKind.Value ? Peek(v.Name) : Held(v.Name);
                case StrLit s: return s with { Value = RewriteHoles(s) };
                case MethodCallExpr { Receiver: ValueRef v } m when _fields.TryGetValue(v.Name, out var f) && f.Kind == FieldKind.Cell:
                    return m.Name switch
                    {
                        "load" when m.Args.Count == 0 => Call(Held(v.Name), "peek"),
                        "store" when m.Args.Count == 1 => Call(Held(v.Name), "poke", RewriteExpr(m.Args[0])),
                        "getview" when m.Args.Count == 0 => Held(v.Name),
                        _ => m with { Receiver = Held(v.Name), Args = m.Args.Select(RewriteExpr).ToList() },
                    };
                case MethodCallExpr { Name: "store_into", Args: [ValueRef v] } m when _fields.TryGetValue(v.Name, out var f) && f.Kind == FieldKind.Cell:
                    return new MethodCallExpr(RewriteExpr(m.Receiver), "poke_into", [], [Held(v.Name)], m.Pos);
                case StealExpr { Value: ValueRef v } st when _fields.TryGetValue(v.Name, out var f):
                    return f.Kind == FieldKind.Value ? Peek(v.Name) : st with { Value = Held(v.Name) };
                case MethodCallExpr m: return m with { Receiver = RewriteExpr(m.Receiver), Args = m.Args.Select(RewriteExpr).ToList() };
                case CallExpr c: return c with { Args = c.Args.Select(RewriteExpr).ToList() };
                case NsCallExpr n: return n with { Args = n.Args.Select(RewriteExpr).ToList() };
                case ImplicitCallExpr i: return i with { Args = i.Args.Select(RewriteExpr).ToList() };
                case BinaryExpr b: return b with { Left = RewriteExpr(b.Left), Right = RewriteExpr(b.Right) };
                case ChainedComparison c: return c with { Operands = c.Operands.Select(RewriteExpr).ToList() };
                case UnaryExpr u: return u with { Operand = RewriteExpr(u.Operand) };
                case StealExpr st: return st with { Value = RewriteExpr(st.Value) };
                case GetItemExpr g: return g with { Base = RewriteExpr(g.Base), Index = RewriteExpr(g.Index) };
                case RangeExpr rg: return rg with { From = RewriteExpr(rg.From), To = RewriteExpr(rg.To), Step = rg.Step is null ? null : RewriteExpr(rg.Step) };
                case IfExpr i: return i with { Cond = RewriteExpr(i.Cond), Then = RewriteExpr(i.Then), Else = RewriteExpr(i.Else) };
                case WhenExpr w:
                {
                    var stmt = (WhenStmt)RewriteOne(w.When, 1);
                    return w with { When = stmt };
                }
                case FieldExpr f: return f with { Base = RewriteExpr(f.Base) };
                case IndexExpr ix: return ix with { Base = RewriteExpr(ix.Base), Index = RewriteExpr(ix.Index) };
                case RecordLit rl: return rl with { Fields = rl.Fields.Select(x => (x.Name, RewriteExpr(x.Value), x.Pos)).ToList() };
                case ArrayLit a: return a with { Elements = a.Elements.Select(RewriteExpr).ToList(), Repeat = a.Repeat is null ? null : RewriteExpr(a.Repeat) };
                case WorkExpr w: return w with { Args = w.Args.Select(RewriteExpr).ToList() };
                case AtExpr at: return at with { Value = RewriteExpr(at.Value), Manager = RewriteExpr(at.Manager) };
                case TempSlotExpr t: return t with { Value = RewriteExpr(t.Value) };
                case TypedLit t: return t with { Literal = RewriteExpr(t.Literal) };
                default: return e;
            }
        }

        /// The holes of a write template, with the names kept in the record read from it.
        private string RewriteHoles(StrLit s)
        {
            string text = s.Value;
            if (!text.Contains('{') || !_fields.Keys.Any(text.Contains)) return text;
            var sb = new StringBuilder();
            for (int i = 0; i < text.Length; i++)
            {
                char ch = text[i];
                if (ch is '{' or '}' && i + 1 < text.Length && text[i + 1] == ch)
                {
                    sb.Append(ch).Append(ch);
                    i++;
                    continue;
                }
                if (ch != '{')
                {
                    sb.Append(ch);
                    continue;
                }
                int end = Lexer.HoleEnd(text, i);
                if (end < 0)
                {
                    sb.Append(text, i, text.Length - i);
                    break;
                }
                string source = text[(i + 1)..end];
                try
                {
                    var hole = new Parser(new Lexer(s.Pos.File, source, s.Pos.Line, s.Pos.Col).Lex(), s.Pos.File,
                        values: [.. _locals.Keys, .. _fields.Keys, "me"]).ParseLoneExpr();
                    sb.Append('{').Append(new Printer().Expr(RewriteExpr(hole))).Append('}');
                }
                catch (CompileError)
                {
                    sb.Append('{').Append(source).Append('}');
                }
                i = end;
            }
            return sb.ToString();
        }

        // ── The declarations ───────────────────────────────────────────────────────────────────────────────────

        private void MakeDecls(List<BlockDecl> resumeBlocks)
        {
            string P(TypeRef t) => Printer.Type(t);
            var ret = r.ReturnType;
            var steps = _steps.Select(s => P(s.Step)).Distinct().ToList();
            string size = steps.Count switch
            {
                0 => "1",
                1 => $"sizeof[{steps[0]}]()",
                _ => $"max({string.Join(", ", steps.Select(s => $"sizeof[{s}]()"))})",
            };
            var src = new StringBuilder();
            src.Append($"### The state of pausable routine `{r.Name}` while it waits: what it keeps across its pauses.\n");
            src.Append($"entity {state}\nobeys Fiber/Eventual[{state}, {P(ret)}]\n");
            foreach (var f in _fields.Values)
            {
                string type = f.Kind == FieldKind.Value ? P(f.Type) : $"Fiber/Carried[{P(f.Type)}]";
                src.Append($"    {f.Name}: {type}\n");
            }
            foreach (var (param, field) in _handed)
                src.Append($"    ### The access handed in as `{param}` with steal, given back when the record ends.\n    {field}: Fiber/HandedAccess\n");
            src.Append($"    ### The pause it stopped at, 0 before its first line.\n    {_at}: U32\n");
            src.Append($"    ### The step it waits for.\n    {_room}: Fiber/StepRoom[{size}]\n\n");
            string ps = string.Join(", ", r.Params.Select(p => $"{Printer.Name(p.Name)}: {P(p.Type)}"));
            src.Append($"### `{r.Name}` before its first line.\n");
            foreach (var p in r.Params) src.Append($"### :param {p.Name}: Its `{p.Name}`.\n");
            src.Append("### :returns: The state.\n");
            src.Append($"common routine {state}.construct({ps}) -> Me\n    lateinit made: &Me\n    made.zeroinit(1)\n");
            foreach (var p in r.Params)
                src.Append(_fields[p.Name].Kind == FieldKind.Value
                    ? $"    made.{p.Name}.poke({Printer.Name(p.Name)})\n"
                    : $"    made.{p.Name}.fill(steal {Printer.Name(p.Name)})\n");
            src.Append($"    made.{_room}.poke(.construct())\n    return made\n\n");
            src.Append("### Does nothing: the step at the bottom of the routine's pause wakes the work.\n### :param waiter: Unused.\n");
            src.Append($"routine @{state}.wake_when_done(waiter: Hosted/Waiter) -> None\n    return\n");
            var tokens = new Lexer(r.File, src.ToString(), r.Pos.Line, 1).Lex();
            var parsed = new Parser(tokens, r.File, r.IsLibrary, acceptLegacy: true).ParseModule().Decls
                .Where(d => d is not ModuleDecl).ToList();
            var resultType = new TypeRef(TypeRef.UnionName, [new TypeArgType(ret), new TypeArgType(PendingType(_pos))], _pos);
            var owner = new TypeRef(state, [], _pos);
            var me = new Param("me", new TypeRef("PointedCell", [new TypeArgType(owner)], _pos), _pos) { Implicit = true };
            var resume = new RoutineDecl(r.File, [new Annotation(BlockRule.Generated, [], _pos), new Annotation(StateMark, [new AnnotationArg(null, state, false)], _pos)],
                owner, "resume", [], [me], resultType, [], resumeBlocks, _pos) { HeaderEndLine = r.HeaderEndLine, EndLine = r.EndLine };
            foreach (var d in parsed.Append(resume))
            {
                var marked = d is RoutineDecl rd && !rd.Annotations.Any(a => a.Name == StateMark)
                    ? rd with { Annotations = [.. rd.Annotations, new Annotation(StateMark, [new AnnotationArg(null, state, false)], _pos)] }
                    : d;
                Made.Add(marked with { Module = r.Module, IsLibrary = r.IsLibrary, IsPrivate = r.IsPrivate });
            }
            var shown = new StringBuilder(src.ToString());
            shown.Append($"\n### Goes on from the pause `{_at}` names until the next one, or the end.\n### :returns: The result, or `Pending`.\n");
            shown.Append($"@generated\nroutine @{state}.resume() -> {P(resultType)}\n");
            try { PrintBlocks(shown, resumeBlocks); }
            catch (InvalidOperationException) { shown.Append("    # (lines the printer can't write)\n"); }
            Shown = shown.ToString() + "\n";
        }

        private static void PrintBlocks(StringBuilder shown, List<BlockDecl> resumeBlocks)
        {
            foreach (var b in resumeBlocks)
            {
                var text = new Printer();
                text.Body(b.Stmts, 1);
                if (b.Name != "entry")
                    shown.Append($"block {b.Name}({string.Join(", ", b.Params.Select(p => $"{p.Name}: {Printer.Type(p.Type)}"))})\n");
                shown.Append(text.ToString());
            }
        }
    }
}
