using System.Globalization;
using System.Text;

namespace Lapila;

/// Places that store a value of a protocol: `xs: &List[Enemy]`, `boss: Enemy` in an entity, `x: &Enemy`, `Enemy?`, a
/// result `-> Enemy`, and the parameters `e: @Enemy`, `e: %Enemy` and `e: Enemy`. A protocol written as a type drops its
/// own first argument, the way `needs T obeys Enemy` does (`Emitter[S64]` is a place for `Emitter[?, S64]`).
///
/// For each protocol of the program the builder declares an entity of the protocol's name that holds the value's type id
/// (`typeid[T]()`, never 0) and the address of its `&T`, with the `&T`'s manager (none for a STACK place). A `&T` gives
/// its own memory back, so the stored value is never copied: it goes in with `steal`, other names reach it through
/// `@Enemy` / `%Enemy` views, and it ends once. Each routine of the protocol becomes a routine on that entity whose body
/// the builder writes when it builds it: a branch on the type id over every type the build puts into places of the
/// protocol, calling that type's routine. Its `destruct` branches the same way and ends the `&T` (the type's destruct,
/// then the memory back to its manager).
public static class Dispatch
{
    /// The annotation of the entity the builder declares for a protocol.
    public const string PlaceMark = "protocol_place";

    /// The annotation of a routine on that entity whose body the builder writes from the types that reach it. Its
    /// argument says the routine's kind: `address` (the protocol takes `@Me`), `value` (it takes `Me`), `self` (it takes
    /// or gives `Me` elsewhere, so it can't be called on a stored value) or `destruct`.
    public const string RoutineMark = "dispatch";

    /// The routines a `when` over a stored value calls: the type id and the address. Their names can't be written.
    public const string TypeIdRoutine = "$type_id";
    public const string AddressRoutine = "$address";

    /// The names the reaching types are bound to while a dispatch body is built.
    public const string ReachPrefix = "TReach";

    /// Whether a declaration is the entity of a protocol's places.
    public static bool IsPlaceDecl(Decl d) => d.AnnotationNamed(PlaceMark) is not null;

    /// The entity of a protocol's places `t` is, or null.
    public static RecordType? PlaceOf(DType? t) => t is RecordType { Decl: var d } r && IsPlaceDecl(d) ? r : null;

    /// The entity of a protocol's places, or a view or place of one.
    public static RecordType? PlaceThrough(DType? t) => PlaceOf(t is PtrType { Pointee: var inner } ? inner : t);

    /// The entities and routines the builder declares for the program's protocols.
    public static IEnumerable<Decl> Declarations(List<Decl> decls)
    {
        var concepts = decls.OfType<ConceptDecl>().ToList();
        if (!concepts.Any(c => !c.IsLibrary)) return [];
        var byName = concepts.GroupBy(c => c.Name).ToDictionary(g => g.Key, g => g.ToList());
        var types = decls.Where(d => d is RecordDecl or VariantDecl or ChoiceDecl or AliasDecl)
            .Select(d => (d switch { RecordDecl r => r.Name, VariantDecl v => v.Name, ChoiceDecl c => c.Name, AliasDecl a => a.Name, _ => "" }, d.Module))
            .ToHashSet();
        var made = new List<Decl>();
        foreach (var c in concepts.Where(c => !c.IsLibrary && c.TypeParams.Count > 0 && !types.Contains((c.Name, c.Module))))
            made.AddRange(Place(c, byName));
        return made;
    }

    private static ConceptDecl? Named(TypeRef t, ConceptDecl from, Dictionary<string, List<ConceptDecl>> byName) =>
        byName.GetValueOrDefault(t.Name) is { } found ? found.FirstOrDefault(c => c.Module == from.Module) ?? found[0] : null;

    /// The protocols `c` obeys, all the way up, each with its routines written in the same names: a parent whose own
    /// parameters other than the first are passed as `c`'s parameters of the same names.
    private static (List<ConceptDecl> Parents, bool AllMapped) Ancestors(ConceptDecl c, Dictionary<string, List<ConceptDecl>> byName)
    {
        var found = new List<ConceptDecl>();
        bool mapped = true;
        var queue = new Queue<ConceptDecl>([c]);
        while (queue.Count > 0)
        {
            var at = queue.Dequeue();
            foreach (var parent in at.Clauses.Where(cl => cl.Kind == "conform").SelectMany(cl => cl.Concepts))
            {
                if (Named(parent, at, byName) is not { } pd || found.Contains(pd) || pd == c) continue;
                bool same = parent.Args.Count == pd.TypeParams.Count
                    && parent.Args[0] is TypeArgType { Type: { Args.Count: 0 } first } && first.Name == at.TypeParams[0]
                    && parent.Args.Skip(1).Select((a, i) => a is TypeArgType { Type: { Args.Count: 0 } t } && t.Name == pd.TypeParams[i + 1]).All(x => x);
                if (!same)
                {
                    mapped = false;
                    continue;
                }
                found.Add(pd);
                queue.Enqueue(pd);
            }
        }
        return (found, mapped);
    }

    /// Whether `t` names `name` anywhere.
    private static bool Mentions(TypeRef t, string name) =>
        t.Path is null && t.Name == name
        || t.Args.Any(a => a switch
        {
            TypeArgType at => Mentions(at.Type, name),
            TypeArgTuple tuple => tuple.Types.Any(x => Mentions(x, name)),
            _ => false,
        });

    private static List<Decl> Place(ConceptDecl c, Dictionary<string, List<ConceptDecl>> byName)
    {
        var rest = c.TypeParams.Skip(1).ToList();
        string handle = rest.Count == 0 ? c.Name : $"{c.Name}[{string.Join(", ", rest)}]";
        var (parents, mapped) = Ancestors(c, byName);
        bool obeys = mapped;
        // The required routines of the protocol and of each parent, once by name: those on the first parameter, taking me.
        var routines = new List<(RoutineDecl Req, string Kind)>();
        foreach (var p in parents.Prepend(c))
            foreach (var r in p.Routines)
            {
                string self = p.TypeParams[0];
                if (r.IsCommon || r.Fixed.Count > 0 || r.Owner is not { Args.Count: 0 } owner || owner.Name != "Me" && owner.Name != self)
                {
                    obeys = false;
                    continue;
                }
                if (routines.Any(x => x.Req.Name == r.Name)) continue;
                bool takesSelf = r.Params.Where(x => !x.Implicit).Any(x => Mentions(x.Type, "Me") || Mentions(x.Type, self))
                                 || Mentions(r.ReturnType, "Me") || Mentions(r.ReturnType, self);
                string kind = takesSelf ? "self" : r.TakesAddress ? "address" : "value";
                if (kind != "address") obeys = false;
                routines.Add((r, kind));
            }
        var withRoutines = parents.Prepend(c).Where(p => p.Routines.Count > 0).ToList();
        string Obeyed(ConceptDecl p) => p.TypeParams.Count == 1 ? $"{p.Name}[{handle}]" : $"{p.Name}[{handle}, {string.Join(", ", p.TypeParams.Skip(1))}]";
        var sb = new StringBuilder();
        sb.Append($"### The stored value of a type that obeys {c.Name}: its type id and its address. The builder writes it.\n");
        sb.Append($"@{PlaceMark}\n@none_is_zero\nentity {handle}\n");
        if (obeys && withRoutines.Count > 0) sb.Append($"obeys {string.Join(", ", withRoutines.Select(Obeyed))}\n");
        sb.Append("    secret id: U64\n    secret at: @Byte\n    secret manager: @MemoryManager\n\n");
        sb.Append($"### The stored value.\n### :param id: The type id.\n### :param at: The address.\n### :param manager: The manager, or none.\n"
                  + $"### :returns: The stored value.\nsecret common routine {handle}.construct(id: U64, at: @Byte, manager: @MemoryManager) -> Me\n"
                  + "    return Me(id: id, at: at, manager: manager)\n\n");
        sb.Append($"### The type id of the value.\n### :returns: The type id.\n@readonly\nroutine @{handle}.dispatch_type_id() -> U64\n    return me.id.peek()\n\n");
        sb.Append($"### The address of the value.\n### :returns: The address.\nroutine @{handle}.dispatch_address() -> @Byte\n    return me.at.peek()\n\n");
        sb.Append($"### Ends the value.\n@{RoutineMark}(\"destruct\")\nroutine @{handle}.destruct() -> None\n    return\n");
        var tokens = new Lexer(c.File, sb.ToString(), c.Pos.Line, c.Pos.Col).Lex();
        var implicitMark = new Annotation("derived", [new AnnotationArg(null, "implicit", false)], c.Pos);
        var selection = c.Annotations.Where(a => a.Name is "target" or "feature").ToList();
        var decls = new Parser(tokens, c.File, c.IsLibrary, acceptLegacy: true).ParseModule().Decls
            .Select(d => d switch
            {
                RoutineDecl { Name: "dispatch_type_id" } r => r with { Name = TypeIdRoutine },
                RoutineDecl { Name: "dispatch_address" } r => r with { Name = AddressRoutine },
                _ => d,
            })
            .Select(d => (Decl)(d with
            {
                Annotations = [.. d.Annotations, .. selection, .. (d is RoutineDecl ? new[] { implicitMark } : [])],
                Module = c.Module, IsLibrary = c.IsLibrary, IsPrivate = c.IsPrivate,
            }))
            .ToList();
        var ownerRef = new TypeRef(c.Name, rest.Select(n => (TypeArg)new TypeArgType(TypeRef.Simple(n, c.Pos))).ToList(), c.Pos);
        foreach (var (r, kind) in routines)
        {
            var annotations = r.Annotations.Where(a => a.Name is "readonly").ToList();
            if (kind is "value" or "self" && annotations.Count == 0) annotations.Add(new Annotation("readonly", [], r.Pos));
            var me = new Param("me", new TypeRef("PointedCell", [new TypeArgType(ownerRef)], r.Pos) { ReadOnly = annotations.Count > 0 }, r.Pos)
                { Implicit = true };
            annotations.Add(new Annotation(RoutineMark, [new AnnotationArg(null, kind, false)], r.Pos));
            annotations.Add(implicitMark);
            annotations.AddRange(selection);
            decls.Add(r with
            {
                File = c.File, Owner = ownerRef, Params = [me, .. r.Params.Where(x => !x.Implicit)],
                Blocks = [new BlockDecl("entry", [], [new UnreachableStmt(r.Pos)], r.Pos)],
                Annotations = annotations, Module = c.Module, IsLibrary = c.IsLibrary, IsPrivate = c.IsPrivate,
            });
        }
        return decls;
    }

    /// The body of a dispatch routine for `types`, the types that reach its places, bound to `TReach0`, `TReach1`, ...
    /// in the routine's environment. `kind` is the routine's (RoutineMark), `name` its name, `typeArgs` its own type
    /// parameters, `args` its parameters but me, each with whether it is handed on with steal, `returns` whether it gives
    /// a value.
    public static string Body(string kind, string name, string protocol, List<string> typeArgs, List<(string Name, bool Steal)> args, bool returns, int count)
    {
        // The header names the parameters only so the lines see them: the routine's own header stays.
        var sb = new StringBuilder($"routine @DispatchOwner.dispatch_body({string.Join(", ", args.Select(a => $"{a.Name}: U8"))}) -> None\n");
        if (kind == "self")
        {
            sb.Append($"    build_error(\"'{name}' takes or gives Me, the value's own type, and a stored {protocol} may hold any type that obeys "
                      + $"{protocol}, so it can't be called on one: call it where the type is known, inside when x is T as t\")\n");
            return sb.ToString();
        }
        if (count == 0)
        {
            sb.Append(kind == "destruct" ? "    return\n" : "    unreachable\n");
            return sb.ToString();
        }
        sb.Append("    dispatch_id: U64 = me.id.peek()\n");
        if (kind == "destruct")
        {
            sb.Append("    if dispatch_id == 0\n        return\n");
            for (int i = 0; i < count; i++)
                sb.Append($"    if dispatch_id == typeid[{ReachPrefix}{i}]()\n"
                          + $"        drop BorrowedCell[{ReachPrefix}{i}](at: me.at.peek().to[@{ReachPrefix}{i}](), manager: me.manager.peek())\n");
            sb.Append("    me.zeroinit(1)\n    return\n");
            return sb.ToString();
        }
        string typeArgText = typeArgs.Count == 0 ? "" : $"[{string.Join(", ", typeArgs)}]";
        string argText = string.Join(", ", args.Select(a => $"{a.Name}: {(a.Steal ? "steal " : "")}{a.Name}"));
        for (int i = 0; i < count; i++)
        {
            string call = $"me.at.peek().to[@{ReachPrefix}{i}](){(kind == "value" ? ".peek()" : "")}.{name}{typeArgText}({argText})";
            sb.Append($"    if dispatch_id == typeid[{ReachPrefix}{i}]()\n");
            sb.Append(returns ? $"        return {call}\n" : $"        {call}\n        return\n");
        }
        sb.Append("    unreachable\n");
        return sb.ToString();
    }

    /// The type id as a constant.
    public static string Id(ulong id) => id.ToString(CultureInfo.InvariantCulture);
}

/// The types each protocol place is given in this build, and the dispatch bodies built from them.
public sealed partial class Compiler
{
    /// The types put into places of each protocol (by the place entity's key), in the order the build met them.
    private readonly Dictionary<string, List<DType>> _reaching = [];

    /// The reaching types each dispatch routine instance was built for, by its symbol: one built before a type reached
    /// is built again (FinishThrows).
    private readonly Dictionary<string, string> _dispatchSeen = [];

    /// A value of `t` goes into a place of `place`: the dispatch routines branch on it from here on. Two types that reach
    /// with one type id are a build error (TypeId).
    public void NoteReaching(RecordType place, DType t, Pos pos)
    {
        TypeId(t, pos);
        if (!_reaching.TryGetValue(place.Key, out var list)) _reaching[place.Key] = list = [];
        if (!list.Any(x => x.Equals(t))) list.Add(t);
    }

    /// The types that reach places of `place`.
    public List<DType> Reaching(RecordType place) => _reaching.GetValueOrDefault(place.Key) ?? [];

    private static string ReachKey(List<DType> types) => string.Join("|", types.Select(t => t.Key));

    /// The protocol a place entity is for.
    public ConceptDecl PlaceProtocol(RecordType place) =>
        _conceptDecls[place.Decl.Name].First(c => c.Module == place.Decl.Module && c.File == place.Decl.File);

    /// Null when a value of `t` may go into a place of `place` (t obeys the protocol), else why not.
    public string? StoreMisfit(RecordType place, DType t, string file, Pos pos) =>
        Conforms(PlaceProtocol(place), [t, .. place.Args], file, pos);

    /// The protocol a place entity is for, as a message writes it.
    public static string ProtocolName(RecordType place) => place.Name;

    /// The dispatch routine instances built for fewer types than reach their place now.
    private IEnumerable<string> StaleDispatch() =>
        _dispatchSeen.Where(kv => _instances.TryGetValue(kv.Key, out var inst) && PlaceThroughParam(inst) is { } place
                                  && ReachKey(Reaching(place)) != kv.Value)
            .Select(kv => kv.Key)
            .Concat(_endsSeen.Where(kv => _instances.ContainsKey(kv.Key) && kv.Value.Values.Any(seen => ReachKey(Reaching(seen.Place)) != seen.Reach))
                .Select(kv => kv.Key))
            .Distinct().ToList();

    /// The routine instances that call a routine that ends entities of a pool of a protocol (`remove`, the pool's end), by
    /// symbol: for each place, the reaching types the instance was built with. What such a call ends grows with the types
    /// that reach, so the instance is built again when more reach (FinishThrows).
    private readonly Dictionary<string, Dictionary<string, (RecordType Place, string Reach)>> _endsSeen = [];

    /// The instance `symbol` calls a routine that ends entities of a pool of the protocol of `place`.
    public void NoteEndsThroughPlace(string symbol, RecordType place)
    {
        if (!_endsSeen.TryGetValue(symbol, out var seen)) _endsSeen[symbol] = seen = [];
        seen[place.Key] = (place, ReachKey(Reaching(place)));
    }

    private static RecordType? PlaceThroughParam(Instance inst) =>
        inst.Params.Count > 0 ? Dispatch.PlaceThrough(inst.Params[0]) : null;

    /// Puts the body of a dispatch routine in place for the types that reach it now, and gives the environment that
    /// binds them (`TReach0`, ...).
    public TypeEnv PrepareDispatch(Instance inst, Func<DType, bool> handedOn)
    {
        var place = PlaceThroughParam(inst) ?? throw new CompileError(Li.TypeMismatch, inst.Decl.Pos, "a dispatch routine without its place");
        var types = Reaching(place);
        _dispatchSeen[inst.Symbol] = ReachKey(types);
        var env = inst.Env.Clone();
        for (int i = 0; i < types.Count; i++) env.Bind($"{Dispatch.ReachPrefix}{i}", types[i]);
        var decl = inst.Decl;
        string kind = decl.AnnotationNamed(Dispatch.RoutineMark)!.First!;
        var args = decl.Params.Skip(1).Select((p, i) => (p.Name, handedOn(inst.Params[i + 1]))).ToList();
        string text = Dispatch.Body(kind, decl.Name, place.Name, decl.TypeParams, args, inst.Ret is not VoidType, types.Count);
        var tokens = new Lexer(decl.File, text, decl.Pos.Line, decl.Pos.Col).Lex();
        var body = (RoutineDecl)new Parser(tokens, decl.File, decl.IsLibrary, acceptLegacy: true).ParseModule().Decls.Single(d => d is RoutineDecl);
        decl.Blocks!.Clear();
        decl.Blocks.AddRange(body.Blocks!);
        return env;
    }
}
