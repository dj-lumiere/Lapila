namespace Lapila;

/// The accesses a routine takes from the AccessManager (Hosted): `p.get_exclusive_access()` gives an
/// `m: @T <- p.get_exclusive_access()` takes exclusive access, `v: %T <- p.get_shared_read_access()` shared read access: the name is the view, and its drop (or the end of its scope) gives the access back.
/// `drop` ends the access. An access comes from
/// a manager, so the memory check follows it as it follows memory: it is given back on every path, once, its view isn't
/// used after, and a routine that returns one or gives back one it was handed tells its callers so (AccessFacts). The
/// names under an exclusive access are what thread work may change (EscapeCheck.CheckWork).
public sealed partial class FunctionGen
{
    /// The groups of the accesses this routine takes, by the place they are taken on (`counter`, `me.guard`, `G`).
    private readonly Dictionary<string, string> _accessGroups = [];

    /// The names that are the views of an access (bound from a take, or from a routine that may return one).
    private readonly HashSet<string> _accessViews = [];

    /// The names bound from a take itself: a poke through one writes what it views, never the name.
    private readonly HashSet<string> _takenViews = [];

    /// The places and names this routine holds exclusive access to: a store through one is safe from other threads.
    private readonly HashSet<string> _exclusiveRoots = [];

    /// The receiver of the give-back being emitted.
    private Expr? _givingBack;

    /// The last take of an access: where it is, its group, and whether it is exclusive.
    private (Pos Pos, string Group, bool Exclusive)? _lastAccess;

    /// The names bound to what a routine of the program gave (`v: @T = f(...)`), with the routine, for the facts of
    /// what this routine returns.
    private readonly Dictionary<string, string> _resultOf = [];

    /// The names bound with `<-` to the view of an access they took (`m: @T <- p.get_exclusive_access()`, or from a
    /// routine of the program that returns one): their drop gives the access back.
    private readonly HashSet<string> _accessBound = [];

    /// The `steal`s of an access this routine allows where they stand: an argument at a view parameter of a routine of the
    /// program, a `<-` binding, a return, a piece of work's argument, a field an entity's written destruct drops.
    private readonly HashSet<StealExpr> _accessSteals = [];

    /// The allowed steals that move an access to a new `<-` name of this routine, which takes the group over.
    private readonly HashSet<StealExpr> _accessMoves = [];

    /// The parameters a caller hands an access to with `steal` (Compiler.Access.Taken): each holds the access.
    private readonly HashSet<string> _takenParams = [];

    /// Whether the body writes `steal name` anywhere.
    private bool StealsOwn(string name) =>
        _decl.Blocks is { } blocks && blocks.SelectMany(b => Bodies.All(b.Stmts)).SelectMany(Bodies.Exprs).SelectMany(ExprTree.All)
            .Any(e => e is StealExpr { Value: ValueRef r } && r.Name == name);

    /// Whether `e` is `steal m` of a name that holds an access.
    private bool StealsAccess(Expr e) => e is StealExpr { Value: ValueRef r } && _accessBound.Contains(r.Name);

    /// The arguments of a call that hand an access over: to a view parameter of a routine of the program, which holds it
    /// from then on (its instance is built for that), or as the value a poke puts in a field an entity's destruct gives
    /// back. Anywhere else the steal is a build error (EvalSteal). Every argument at a view parameter is noted, so a
    /// parameter that takes an access over gets one on every call.
    private void NoteAccessSteals(CallPlan plan, Instance sig)
    {
        if (_c.Prechecking) return;
        // `holder.f.poke(...)` into a field that holds an access: such a field is filled when the entity is made.
        if (plan.Decl.Name is "poke" or "poke_into" && (plan.Decl.Name == "poke" ? plan.Receiver : plan.Args.FirstOrDefault()) is FieldExpr into
            && AccessField(into) is { } fieldOwner)
            throw Err(Li.AccessHandedOver, plan.Pos, $"'{into.Name}' holds an access ('{fieldOwner}.destruct' gives it back with drop me.{into.Name}), "
                + $"so it is filled when the entity is made, with steal: Me({into.Name}: steal held)");
        if (plan.Decl.IsLibrary) return;
        int offset = plan.Receiver is null ? 0 : 1;
        for (int i = 0; i < plan.Args.Count && i + offset < plan.Decl.Params.Count; i++)
        {
            var param = plan.Decl.Params[i + offset];
            if (param.Type is not { Name: "PointedCell" or "PointedSlice", Path: null }) continue;
            bool stolen = StealsAccess(plan.Args[i]);
            _c.Access.NoteViewArg(sig.Symbol, i + offset, stolen, plan.Args[i].Pos, plan.Decl.DisplayName, param.Name);
            if (!stolen) continue;
            _c.Access.NoteTaken(sig.Symbol, i + offset);
            _accessSteals.Add((StealExpr)plan.Args[i]);
        }
    }

    /// The fields of an entity being made that hold an access: the ones its written destruct drops (`drop me.f`) take one
    /// handed over with `steal`, and only those take one.
    private void NoteAccessFields(RecordType made, Dictionary<string, Expr> given)
    {
        if (_c.Prechecking) return;
        foreach (var (name, value) in given)
        {
            bool access = made.Decl.IsEntity && made.Decl.Fields.FirstOrDefault(f => f.Name == name)?.Type is { Name: "PointedCell" or "PointedSlice", Path: null }
                && _c.DropsField(made.Decl, name);
            if (StealsAccess(value))
            {
                if (!access)
                    throw Err(Li.AccessHandedOver, value.Pos, $"'{name}' would hold the access handed over here, and nothing would give it back: a field "
                        + $"holds an access when its entity's written destruct drops it, routine @{made.Decl.Name}.destruct() with drop me.{name}");
                _accessSteals.Add((StealExpr)value);
            }
            else if (access)
                throw Err(Li.AccessHandedOver, value.Pos, $"'{made.Decl.Name}.destruct' gives back the access in '{name}' (drop me.{name}), so '{name}' takes "
                    + $"an access handed over with steal, and this is a view: {name}: steal held");
        }
    }

    /// The entity whose written destruct gives back the access a field holds (`drop me.f` in it), or null for a field
    /// no destruct drops so.
    private string? AccessField(FieldExpr f)
    {
        var holder = InferQuiet(f.Base) is PtrType { Pointee: RecordType r } ? r : InferQuiet(f.Base) as RecordType;
        if (holder is not { Decl.IsEntity: true } || holder.Decl.Fields.FirstOrDefault(x => x.Name == f.Name) is not { Type: { Name: "PointedCell" or "PointedSlice", Path: null } })
            return null;
        return _c.DropsField(holder.Decl, f.Name) ? holder.Decl.Name : null;
    }

    /// The names written as a view (`v: @T = ...`, a parameter `p: %[T]`): a `drop` of one ends that reference alone.
    private readonly HashSet<string> _viewNamesWritten = [];

    /// The call a `<-` line of a view stands on, planned, or null when it can't be planned.
    private CallPlan? AccessTaker(Expr call)
    {
        try { return PlanCall(call, null); }
        catch (CompileError) { return null; }
    }

    /// Whether `d` is one of the standard library's routines that take an access.
    private static bool TakesAccess(RoutineDecl d) => d.IsLibrary && d.Name is "get_exclusive_access" or "get_shared_read_access"
        && d.Owner is { Name: "PointedCell" or "BorrowedCell" or "PointedSlice" or "BorrowedSlice" };

    /// The names bound to a shared read access taken from a routine of the program (`v: %T <- f()`): read only.
    private readonly HashSet<string> _readOnlyViews = [];

    /// The names that are a view that only reads (`v: %T`, a `%T` parameter, the me of a `@readonly` routine, a view
    /// made from one), each with what the message says of it.
    private readonly Dictionary<string, string> _readOnlyWhy = [];

    /// Whether `e` reaches memory through a view that only reads: the view of a shared read access, a `%T` / `%[T]`, or
    /// what a routine gives as one.
    private bool ReadOnlyView(Expr e) => ReadOnlyReason(e) is not null;

    /// What makes `e` a view that only reads, as a message says it, or null when `e` may write.
    private string? ReadOnlyReason(Expr e)
    {
        if (e is UnaryExpr { Op: "try" or "check" } recovered) e = recovered.Operand;
        for (var at = AsValueCall(e); at is not null;)
        {
            if (at is ValueRef named && _readOnlyWhy.TryGetValue(named.Name, out var why)) return why;
            if (ReadOnlyResult(at) is { } given) return given;
            if (at is ValueRef r && _readOnlyViews.Contains(r.Name)) return "the view of a shared read access, which reads only";
            at = at switch
            {
                FieldExpr f => f.Base,
                IndexExpr ix => ix.Base,
                MethodCallExpr { Name: "getslot" or "stride" or "offset" or "getslice" or "to" or "getview" or "peek" } m => m.Receiver,
                // A stamp read through the view gives the entity's view, read only too.
                MethodCallExpr { Name: "fetch", Args.Count: 0 } m when IsStampFetch(m) => m.Receiver,
                _ => null,
            };
        }
        return null;
    }

    /// The views fetched through a stamp (`v: @Node = s.fetch()`), and the views made from them: a call that may remove
    /// an entity from a StampManager, or end a pool, ends them all.
    private readonly HashSet<string> _stampViews = [];

    /// The type each view fetched through a stamp is of (the entity's type key), for the views a remove ends.
    private readonly Dictionary<string, string> _stampViewType = [];

    /// The view of type `key` fetched through a stamp: the root the memory check follows it by.
    private static string StampRoot(string key) => $"{StampedEntities}:{key}";

    /// The views fetched through a stamp a call ends (`name` is `$stamped` for every type, or `$stamped:key` for one),
    /// and what this routine may end from then on, which its callers read.
    private void EndStampViews(string name, string how, Pos pos, bool routineValue)
    {
        if (!_c.Prechecking) _c.NoteReshape(_inst, name, null);
        var keys = name == StampedEntities ? _stampViewType.Values.Distinct().ToList() : [name[(StampedEntities.Length + 1)..]];
        foreach (var key in keys.Where(k => _stampViewType.ContainsValue(k)))
            Mem(new MemoryRules.Reshape(StampRoot(key), how, pos) { Ends = true, ThroughValue = routineValue });
    }

    /// What a call of the standard library's `@ends_stamped` routines may end: `remove` of a `Stamped[T]` ends the
    /// entities of T and what T's destruct may end, and ending a pool may end entities of any type.
    private List<(string Param, string? Field)> StampedEnds(CallPlan plan)
    {
        if (plan.Decl.Name != "remove" || plan.Env.Get("T") is not { } t) return [(StampedEntities, null)];
        var ends = new List<(string, string?)> { (StampRoot(t.Key), null) };
        if (t is not RecordType owner) return ends;
        foreach (var destruct in _c.MethodCandidates(t, "destruct", _env.File, plan.Pos, anyModule: true)
                     .Where(d => d.Owner?.Name == owner.Decl.Name && d.Module == owner.Decl.Module && d.Blocks is { Count: > 0 }))
        {
            try
            {
                var env = BindOwner(destruct, t, plan.Pos);
                foreach (var (moved, _) in _c.ReshapesOf(_c.Signature(destruct, env), _inst, plan.Pos))
                    if (moved.StartsWith(StampedEntities, StringComparison.Ordinal) && !ends.Contains((moved, null))) ends.Add((moved, null));
            }
            catch (CompileError) { ends.Add((StampedEntities, null)); }
        }
        return ends;
    }

    /// Whether `e` reaches memory through a stamp's `fetch()`, or through a view fetched so.
    private bool FromStamp(Expr e)
    {
        for (var at = AsValueCall(e); at is not null;)
        {
            if (at is ValueRef r && _stampViews.Contains(r.Name)) return true;
            if (at is MethodCallExpr { Name: "fetch", Args.Count: 0 } fetched && IsStampFetch(fetched)) return true;
            at = at switch
            {
                FieldExpr f => f.Base,
                IndexExpr ix => ix.Base,
                MethodCallExpr { Name: "getslot" or "stride" or "offset" or "getslice" or "to" or "getview" } m => m.Receiver,
                _ => null,
            };
        }
        return false;
    }

    /// The type key of the entity `e` reaches through a stamp: the `T` of the `Stamped[T]` fetched, or the type of the
    /// view it was made from.
    private string? StampedType(Expr e)
    {
        for (var at = AsValueCall(e); at is not null;)
        {
            if (at is ValueRef r && _stampViewType.TryGetValue(r.Name, out var key)) return key;
            if (at is MethodCallExpr { Name: "fetch", Args.Count: 0 } fetched && IsStampFetch(fetched)
                && InferQuiet(fetched.Receiver) is RecordType { Args: [var entity] }) return entity.Key;
            at = at switch
            {
                FieldExpr f => f.Base,
                IndexExpr ix => ix.Base,
                MethodCallExpr { Name: "getslot" or "stride" or "offset" or "getslice" or "to" or "getview" } m => m.Receiver,
                _ => null,
            };
        }
        return null;
    }

    /// A binding of a view fetched through a stamp: the memory check follows it as a view of its entity type's entities.
    private void NoteStampView(string name, Expr value, DType t, Pos pos)
    {
        if (_c.Prechecking || !MemOn) return;
        if (t is not PtrType { Pointee: not null } && !Compiler.IsCoreSpan(t, out _)) return;
        if (!FromStamp(value)) return;
        if (StampedType(value) is not { } key) return;
        _stampViews.Add(name);
        _stampViewType[name] = key;
        _viewNames.Add(name);
        Mem(new MemoryRules.ViewOf(name, StampRoot(key), pos) { Contents = StampRoot(key) });
    }

    /// What makes the value of a call or a field read only: a routine of the program whose result is written `%T` or
    /// `%[T]`, or a field written so (`p.parent.peek()` of `parent: %Node`). Null for anything else.
    private string? ReadOnlyResult(Expr e)
    {
        if (e is MethodCallExpr { Name: "peek", Args.Count: 0, Receiver: FieldExpr f } && ReadOnlyField(f) is { } field)
            return $"the field '{f.Name}', a {field}, a view that only reads";
        if (e is not (CallExpr or NsCallExpr or MethodCallExpr)) return null;
        try
        {
            if (PlanCall(e, null) is { Decl: { ReturnType.ReadOnly: true } d }) return $"what '{d.DisplayName}' gives, a {d.ReturnType}, a view that only reads";
        }
        catch (CompileError) { }
        return null;
    }

    /// How a message says what makes `e` read only: `is` for the name itself, `is reached through` for a part of it.
    private string ReachedAs(Expr e) =>
        e is ValueRef r && (_readOnlyWhy.ContainsKey(r.Name) || _readOnlyViews.Contains(r.Name)) || ReadOnlyResult(e) is not null ? "is" : "is reached through";

    /// The written type of a field when it is a `%T` or `%[T]`, else null.
    private TypeRef? ReadOnlyField(FieldExpr f)
    {
        var holder = InferQuiet(f.Base) is PtrType { Pointee: RecordType r } ? r : InferQuiet(f.Base) as RecordType;
        return holder?.Decl.Fields.FirstOrDefault(x => x.Name == f.Name)?.Type is { ReadOnly: true } t ? t : null;
    }

    /// A view that only reads goes only where a `%T` / `%[T]` (or a library routine that doesn't write through it) takes
    /// it: never into a `@T` / `@[T]` the program wrote, which could write through it.
    private void CheckReadOnlyNarrowing(Expr value, TypeRef? into, string where)
    {
        if (_c.Prechecking || into is not { Name: "PointedCell" or "PointedSlice", Path: null, ReadOnly: false }) return;
        if (ReadOnlyReason(value) is not { } why) return;
        string spelled = $"{Spelled(value)} {ReachedAs(value)}";
        string narrow = into.Name == "PointedCell" && into.Args is [TypeArgType held] ? $"%{held.Type}" : into.Args is [TypeArgType elems] ? $"%[{elems.Type}]" : "%T";
        throw Err(Li.ReadOnlyViewWrite, value.Pos, $"{spelled} {why}, and {where}, which could write through it: a {narrow} becomes no "
            + $"{into} (write {narrow} there, or take a view that writes)");
    }

    /// A binding of a view: `v: %T = ...` only reads, a view of a read-only one is read only too, and `v: @T = ...` of
    /// a view that only reads is a build error.
    private void NoteReadOnlyBinding(BindStmt b, DType t)
    {
        if (b.Type is { Name: "PointedCell" or "PointedSlice", Path: null, Known: null }) _viewNamesWritten.Add(b.Name);
        else _viewNamesWritten.Remove(b.Name);
        if (b.Type.ReadOnly)
        {
            _readOnlyWhy[b.Name] = $"a {b.Type}, a view that only reads";
            return;
        }
        if (b.Type.Known is null && !b.Lowered && !b.Name.StartsWith('$'))
            CheckReadOnlyNarrowing(b.Value, b.Type, $"'{b.Name}' takes it as a {b.Type}");
        if (ReadOnlyReason(b.Value) is { } why && (t is PtrType || Compiler.IsCoreSpan(t, out _) || WayToChange(t) is not null))
            _readOnlyWhy[b.Name] = why;
        else _readOnlyWhy.Remove(b.Name);
    }

    /// Whether `m` is `fetch()` on a record marked `@entity_link`: a link whose `fetch()` gives the entity's view.
    private bool IsStampFetch(MethodCallExpr m) => InferQuiet(m.Receiver) is RecordType r && r.Decl.AnnotationNamed("entity_link") is not null;

    /// A write through the view of a shared read access, or handing it to a routine that may move its memory, is a
    /// build error: a shared read access reads only.
    private void CheckReadOnlyWrite(CallPlan plan, Instance sig)
    {
        if (_c.Prechecking) return;
        Expr? written = plan.Decl.Name switch
        {
            "poke" or "poke_volatile" or "poke_unbroken" or "poke_unaligned" or "zeroinit" or "copy" or "store" or "setitem" or "swap" => plan.Receiver,
            "poke_into" or "store_into" or "copy_into" => plan.Args.FirstOrDefault(),
            _ when UnbrokenNames.IsWrite(plan.Decl.Name) => plan.Receiver,
            _ => null,
        };
        if (written is not null && ReadOnlyReason(written) is { } why)
            throw why.StartsWith("the view of a shared read access", StringComparison.Ordinal)
                ? Err(Li.SharedAccessWrite, plan.Pos, $"{Spelled(written)} is the view of a shared read access, which reads only: take exclusive access "
                    + "to write (m: @T <- p.get_exclusive_access(), or @[T] for a run of values)")
                : Err(Li.ReadOnlyViewWrite, plan.Pos, $"{Spelled(written)} {ReachedAs(written)} {why}, and '{(plan.Decl.IsLibrary ? plan.Decl.Name : plan.Decl.DisplayName)}' writes through it: "
                    + "take a @T (or a @[T]) to write");
        // A view that only reads, handed where a routine of the program takes a view that writes.
        if (!plan.Decl.IsLibrary)
        {
            int at = plan.Receiver is null ? 0 : 1;
            var handed = plan.Receiver is { } receiver ? plan.Args.Prepend(receiver).ToList() : plan.Args;
            for (int i = 0; i < handed.Count && i < plan.Decl.Params.Count; i++)
            {
                var param = plan.Decl.Params[i];
                string where = i == 0 && plan.Receiver is not null
                    ? $"'{plan.Decl.DisplayName}' takes me as a {param.Type}"
                    : $"'{plan.Decl.DisplayName}' takes it as '{param.Name}', a {param.Type}";
                CheckReadOnlyNarrowing(handed[i] is StealExpr st ? st.Value : handed[i], param.Type, where);
            }
            _ = at;
        }
        foreach (var (name, _) in _c.ReshapesOf(sig, _inst, plan.Pos))
        {
            int index = plan.Decl.Params.FindIndex(p => p.Name == name);
            int offset = plan.Receiver is null ? 0 : 1;
            Expr? arg = index == 0 && plan.Receiver is not null ? plan.Receiver
                : index - offset >= 0 && index - offset < plan.Args.Count ? plan.Args[index - offset] : null;
            if (arg is not null && ReadOnlyReason(arg) is { } moved)
                throw Err(moved.StartsWith("the view of a shared read access", StringComparison.Ordinal) ? Li.SharedAccessWrite : Li.ReadOnlyViewWrite,
                    plan.Pos, $"'{plan.Decl.DisplayName}' may move the memory of {Spelled(arg)} (it is @reshaping), and "
                    + $"{Spelled(arg)} {ReachedAs(arg)} {moved}: take a view that writes to change it");
        }
    }

    /// The place an access is taken on, written out (`me.guard`, `G.count`, `xs.getslot(i)`), or null.
    private static string? AccessKey(Expr e) => e switch
    {
        ValueRef r => r.Name,
        PresetRef { Owner: null } p => p.Name,
        FieldExpr f when AccessKey(f.Base) is { } b => $"{b}.{f.Name}",
        MethodCallExpr { Name: "stride" or "getslot" or "getview", TypeArgs.Count: 0, Args: [var at] } m when AccessKey(m.Receiver) is { } b =>
            $"{b}.{m.Name}({new Printer().Expr(at, 0)})",
        _ => null,
    };

    /// The names of addresses made from an `Addr` (`p: @T = a.to[@T]()`): the build doesn't follow an `Addr`, so what is
    /// changed through one isn't counted for thread work.
    private readonly HashSet<string> _fromAddr = [];

    /// Whether `e` turns an `Addr` into a pointer (`a.to[@T]()`).
    private bool FromAddr(Expr e) => e is MethodCallExpr { Name: "to", TypeArgs.Count: 1 } m && InferQuiet(m.Receiver) is PtrType { Pointee: null };

    /// Whether a store into `place` goes through an exclusive access this routine holds, or through an address made
    /// from an `Addr`, which the build doesn't follow.
    private bool UnderExclusiveAccess(Expr place)
    {
        for (var at = AsValueCall(place); at is not null;)
        {
            if (AccessKey(at) is { } key && (_exclusiveRoots.Contains(key) || _fromAddr.Contains(key))) return true;
            if (FromAddr(at)) return true;
            at = at switch
            {
                FieldExpr f => f.Base,
                IndexExpr ix => ix.Base,
                MethodCallExpr { Name: "getslot" or "stride" or "offset" or "getslice" or "to" or "getview" or "peek" } m => m.Receiver,
                _ => null,
            };
        }
        return false;
    }

    /// The index of the parameter `name` of this routine, or -1.
    private int ParamIndex(string name) => _decl.Params.FindIndex(p => p.Name == name);

    /// The events and facts of a call: a take starts an access, a give-back ends one, and handing an access or a
    /// parameter to a routine of the program is followed there.
    private void NoteAccessCall(CallPlan plan, Instance callee)
    {
        if (_c.Prechecking) return;
        if (TakesAccess(plan.Decl) && plan.Receiver is { } taken)
        {
            bool exclusive = plan.Decl.Name == "get_exclusive_access";
            string shown = AccessKey(taken) ?? Spelled(taken);
            // One name for every access taken on the same place: a give-back on that place ends the one held on the path.
            string group = AccessKey(taken) is { } named ? $"access:{named}" : $"access:{shown}@{plan.Pos.Line}:{plan.Pos.Col}";
            Mem(new MemoryRules.Acquire(group, "taken", plan.Pos)
                {
                    Access = exclusive ? "an exclusive access" : "a shared read access", Shown = shown,
                    Run = plan.Decl.Owner is { Name: "PointedSlice" or "BorrowedSlice" },
                });
            if (AccessKey(taken) is { } key)
            {
                _accessGroups[key] = group;
                if (exclusive) _exclusiveRoots.Add(key);
            }
            _lastAccess = (plan.Pos, group, exclusive);
            return;
        }
        if (callee.IsExternalC || callee.IsTemplate || callee.IsAsm) return;
        int offset = plan.Receiver is null ? 0 : 1;
        var handed = plan.Receiver is { } r ? plan.Args.Prepend(r).ToList() : plan.Args;
        for (int i = 0; i < handed.Count; i++)
        {
            var arg = handed[i] is StealExpr st ? st.Value : handed[i];
            if (arg is ValueRef p && ParamIndex(p.Name) is >= 0 and var mine) _c.Access.NotePasses(_inst.Symbol, mine, callee.Symbol, i);
            if (plan.Decl.IsLibrary)
            {
                continue;
            }
            string how = $"handed to '{plan.Decl.DisplayName}'";
            if (arg is ValueRef v && _accessViews.Contains(v.Name)) Mem(new MemoryRules.MayEndAccess(v.Name, callee.Symbol, i, how, arg.Pos));
            else if (AccessKey(arg) is { } key && _accessGroups.TryGetValue(key, out var group))
                Mem(new MemoryRules.MayEndAccess(group, callee.Symbol, i, how, arg.Pos));
        }
        _ = offset;
    }

    /// A binding of an access (`held: @T <- p.get_exclusive_access()`), of a view made from one
    /// (`v: @T = held.getview()`), or of what a routine of the program gave, which may be an access it returns.
    private void NoteAccessBinding(string name, Expr value, DType t, Pos pos, bool taken = false, bool readOnly = false)
    {
        if (_c.Prechecking || !MemOn) return;
        // `held: @T <- steal m`: the new name takes the access over.
        if (taken && value is StealExpr { Value: ValueRef from })
        {
            _accessViews.Add(name);
            _takenViews.Add(name);
            _viewNames.Add(name);
            Mem(new MemoryRules.Alias(name, from.Name, pos));
            if (_readOnlyViews.Contains(from.Name) || readOnly) _readOnlyViews.Add(name);
            if (_exclusiveRoots.Contains(from.Name)) _exclusiveRoots.Add(name);
            return;
        }
        // `m: @T <- f()` with f a routine of the program: f returns an access (checked once every routine is built).
        if (taken && !(_lastAccess is { } took && took.Pos == value.Pos) && CalleeSymbol(value) is { } returning)
        {
            _resultOf[name] = returning;
            _accessViews.Add(name);
            _takenViews.Add(name);
            _viewNames.Add(name);
            Mem(new MemoryRules.MayAcquireAccess(name, returning, name, pos));
            _c.Access.NoteBoundFrom(returning, name, pos);
            if (readOnly) _readOnlyViews.Add(name);
            else _exclusiveRoots.Add(name);
            return;
        }
        if (_lastAccess is { } last && last.Pos == value.Pos)
        {
            _accessViews.Add(name);
            _takenViews.Add(name);
            Mem(new MemoryRules.Alias(name, last.Group, pos));
            _viewNames.Add(name);
            Mem(new MemoryRules.ViewOf(name, last.Group, pos));
            if (last.Exclusive) _exclusiveRoots.Add(name);
            else _readOnlyViews.Add(name);
            return;
        }
        // A view: a pointer, or a run of values (`v: @[T] = held.getview()`).
        if (t is not PtrType && !Compiler.IsCoreSpan(t, out _)) return;
        if (ReadOnlyView(value)) _readOnlyViews.Add(name);
        if (FromAddr(value)) _fromAddr.Add(name);
        if (RootName(value) is { } root)
        {
            if (_exclusiveRoots.Contains(root)) _exclusiveRoots.Add(name);
            if (_readOnlyViews.Contains(root)) _readOnlyViews.Add(name);
            // A view made from an access is used only while the access is held.
            if (_accessViews.Contains(root) && root != name)
            {
                _viewNames.Add(name);
                Mem(new MemoryRules.ViewOf(name, root, pos));
            }
        }
    }

    /// `drop held` of an access gives it back: its group ends there. A parameter's access given back here ends the
    /// caller's at the call (AccessFacts).
    private void NoteAccessDrop(Expr dropped, Pos pos)
    {
        if (_c.Prechecking || !MemOn || dropped is not ValueRef r) return;
        if (_accessViews.Contains(r.Name)) Mem(new MemoryRules.End(r.Name, $"drop {r.Name}", pos));
    }

    /// The symbol of the routine of the program a call expression resolves to, or null (a library routine, a template).
    private string? CalleeSymbol(Expr call)
    {
        try
        {
            if (PlanCall(call, null) is not { } plan || plan.Decl.IsLibrary) return null;
            var sig = _c.Signature(plan.Decl, plan.Env);
            if (sig.IsTemplate || sig.IsAsm || sig.IsExternalC) return null;
            return _c.RequireInstance(plan.Decl, plan.Env).Symbol;
        }
        catch (CompileError) { return null; }
    }

    /// A return of an access's view hands the access to the caller: its group ends here, and this routine returns an
    /// access (AccessFacts).
    private bool ReturnsAccessView(Expr e)
    {
        if (_c.Prechecking) return false;
        if (e is ValueRef v && _accessViews.Contains(v.Name))
        {
            if (_resultOf.TryGetValue(v.Name, out var from)) _c.Access.NoteReturnsFrom(_inst.Symbol, from);
            else _c.Access.NoteReturns(_inst.Symbol);
            Mem(new MemoryRules.End(v.Name, "returned", e.Pos));
            return true;
        }
        if (_lastAccess is { } last && last.Pos == e.Pos)
        {
            _c.Access.NoteReturns(_inst.Symbol);
            Mem(new MemoryRules.End(last.Group, "returned", e.Pos));
            return true;
        }
        if (e is CallExpr or NsCallExpr or MethodCallExpr && CalleeSymbol(e) is { } callee)
            _c.Access.NoteReturnsFrom(_inst.Symbol, callee);
        return false;
    }
}
