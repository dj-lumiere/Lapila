using System.Globalization;

namespace Lapila;

/// Protocol places (Dispatch.cs) in a routine body: a `&T` handed into one with `steal`, and `when x is T as t` on one.
public sealed partial class FunctionGen
{
    /// The `steal x` of a STACK place (or an entity parameter's slot) that went into a protocol place: the value is the
    /// slot's address, so the escape check follows the slot, not what it held.
    private readonly HashSet<Pos> _stackIntoPlace = [];

    /// `name` with its article: an Enemy, a Slime.
    private static string An(string name) => ("AEIOU".Contains(name[0]) ? "an " : "a ") + name;

    /// Whether a parameter of a dispatch routine is handed on with steal: a value with something to give back.
    private static bool HandedOnByValue(DType t) => Entities.Holds(t) || ManagedMemory(t) is not null;

    /// What `x` holds when it is a `&T` that can go into a protocol place: the T, and whether the place is a
    /// BorrowedCell from a manager (else a slot of this routine's frame). Null for anything else, a place of a
    /// protocol's own entity included (it moves as an entity does).
    private (DType Held, bool Managed)? StoredOriginal(ValueRef x)
    {
        if (!_values.ContainsKey(x.Name) || InferQuiet(x) is not PtrType { Pointee: { } inner }) return null;
        if (inner is RecordType { Decl: { Name: "BorrowedCell", Module: Compiler.SystemModule }, Args: [var held] })
            return Dispatch.PlaceOf(held) is null ? (held, true) : null;
        if (Dispatch.PlaceOf(inner) is not null || inner is RecordType { Decl.Name: "BorrowedSlice" }) return null;
        if (_stackPlaces.ContainsKey(x.Name) || _claimedSlots.Contains(x.Name) || _routineParams.ContainsKey(x.Name) && Entities.Holds(inner))
            return (inner, false);
        return null;
    }

    /// Whether `arg` is a `&T` handed with steal into a place of the protocol entity `expected`, with T obeying it.
    private bool IntoPlaceFits(Expr arg, DType expected) =>
        Dispatch.PlaceOf(expected) is { } place && arg is StealExpr { Value: ValueRef x } && StoredOriginal(x) is var (held, _)
        && _c.StoreMisfit(place, held, _env.File, arg.Pos) is null;

    /// `steal x` where a protocol's place goes: the `&T` x holds becomes the stored value (its type id, its address and
    /// its manager), and x ends. Null when `e` isn't that.
    private Val? IntoPlace(Expr e, DType expected)
    {
        if (Dispatch.PlaceOf(expected) is not { } place) return null;
        if (e is not StealExpr { Value: ValueRef x } s || StoredOriginal(x) is not var (held, managed))
        {
            if (e is ValueRef original && StoredOriginal(original) is var (originalHeld, _)
                && _c.StoreMisfit(place, originalHeld, _env.File, e.Pos) is null)
                throw Err(Li.TypeMismatch, e.Pos, $"'{original.Name}' is a &{originalHeld.Name}, and {An(place.Name)} place takes it over: "
                    + $"hand it over with steal {original.Name}");
            if (e is ValueRef copied && InferQuiet(copied) is PtrType { Pointee: var same } && same.Equals(place))
                throw Err(Li.EntityCopied, e.Pos, $"'{copied.Name}' holds a stored {place.Name}, which is never copied: it holds a &T, "
                    + "and a &T gives its own memory back, so a copy would give it back twice. Hand it over with "
                    + $"steal {copied.Name}, or take a view of it where it is, v: @{place.Name} = {copied.Name}");
            if (e is not StealExpr && InferQuiet(e) is { } given && Dispatch.PlaceThrough(given) is null && !given.Equals(expected)
                && _c.StoreMisfit(place, given is PtrType { Pointee: { } p } ? p : given, _env.File, e.Pos) is null)
            {
                string shown = given is PtrType { Pointee: { } pointee } ? pointee.Name : given.Name;
                throw Err(Li.TypeMismatch, e.Pos, $"{An(place.Name)} place holds a &{shown} handed over with steal, and this is "
                    + $"{(given is PtrType ? "a view of one" : $"a {shown} value")}: put the value in a place of its own (v: &{shown} <- value, "
                    + "from a manager or STACK) and hand that over, steal v");
            }
            return null;
        }
        if (_c.StoreMisfit(place, held, _env.File, s.Pos) is { } why)
            throw Err(Li.ProtocolNotHeld, s.Pos, $"'{x.Name}' holds {An(held.Name)}, and {An(place.Name)} place holds only a type that obeys "
                + $"{place.Name}: {why}");
        _c.NoteReaching(place, held, s.Pos);
        string id = Dispatch.Id(_c.TypeId(held, s.Pos));
        _c.EnsureTypeDefined(place);
        string at, manager;
        if (managed)
        {
            var cell = (RecordType)((PtrType)InferQuiet(x)!).Pointee!;
            var v = Eval(new StealExpr(x, s.Pos), cell);
            at = EmitTmp($"extractvalue {cell.Llvm} {v.Op}, 0");
            manager = EmitTmp($"extractvalue {cell.Llvm} {v.Op}, 1");
        }
        else
        {
            // A place borrowed in a loop body is the same slot on every pass, and the protocol place would keep it
            // past the pass.
            if (_loops.Count > 0 && _boxScopes.FindIndex(scope => scope.Any(p => p.Name == x.Name)) is var depth
                && depth >= _loops.Peek().BoxDepth)
                throw Err(Li.ManagerFill, s.Pos, $"'{x.Name}' is a place of this loop's frame, which every pass of the loop "
                    + $"borrows again, so {An(place.Name)} place would keep a slot the next pass fills: borrow it from a manager, "
                    + $"{x.Name}: &{held.Name} <- value from HEAP");
            var slot = MemUseView(x);
            at = slot.Op;
            manager = "null";
            if (MemOn && _memTracked.Contains(x.Name)) Mem(new MemoryRules.End(x.Name, $"steal {x.Name}", s.Pos));
            NoteCallerHeldEnd(x, $"steal {x.Name}", s.Pos);
            StackPlaceEnded(x);
            _stackIntoPlace.Add(s.Pos);
        }
        string a = EmitTmp($"insertvalue {place.Llvm} undef, i64 {id}, 0");
        string b = EmitTmp($"insertvalue {place.Llvm} {a}, ptr {at}, 1");
        string c = EmitTmp($"insertvalue {place.Llvm} {b}, ptr {manager}, 2");
        return new Val(c, place);
    }

    /// `when x` over a stored value of a protocol (a place, a view, or a field of one): each `is T as t` arm tests the
    /// type id, an entity's `t` is a view of it where it is (`@T`), a record's `t` a copy, and `else` takes any other
    /// type. Written as the `if` chain it stands for. Null when `w` isn't over one.
    private List<Stmt>? StoredWhen(WhenStmt w, ValueFrame? frame)
    {
        if (w.Value is not { } subject || InferQuiet(subject) is not { } st || Dispatch.PlaceThrough(st) is not { } place) return null;
        if (frame is not null)
            throw Err(Li.WhenValueArm, w.Pos, $"a when over a stored {place.Name} is a statement: bind the value in each arm, or "
                + "write a routine that returns it");
        if (!w.Arms.Any(a => a.IsElse))
            throw Err(Li.NonExhaustiveWhen, w.Pos, $"{An(place.Name)} place may hold any type that obeys {place.Name}, so a when over "
                + "one needs an else arm");
        string id = $"$storedid{_tmp++}";
        var pos = w.Pos;
        var u64 = new TypeRef("U64", [], pos);
        List<Stmt> chain = [];
        List<Stmt>? tail = null;
        for (int i = w.Arms.Count - 1; i >= 0; i--)
        {
            var arm = w.Arms[i];
            if (arm.IsElse)
            {
                tail = arm.Body;
                continue;
            }
            if (arm.Cases is not { Count: > 0 } cases || cases.Any(c => c is not IsPattern))
                throw Err(Li.WhenObservation, arm.Pos, $"an arm of a when over a stored {place.Name} names a type: is T as t");
            Expr? cond = null;
            var body = new List<Stmt>();
            foreach (IsPattern pattern in cases)
            {
                var t = Resolve(pattern.Type);
                if (_c.StoreMisfit(place, t, _env.File, pattern.Pos) is { } why)
                    throw Err(Li.StoredArmType, pattern.Pos, $"{An(place.Name)} place never holds {An(t.Name)}: {why}");
                var test = new BinaryExpr("==", new ValueRef(id, pattern.Pos),
                    new CallExpr("typeid", [new TypeRef("$stored", [], pattern.Pos) { Known = t }], [], pattern.Pos), pattern.Pos);
                cond = cond is null ? test : new BinaryExpr("or", cond, test, pattern.Pos);
                if (pattern.Binding is not { } binding) continue;
                if (cases.Count > 1)
                    throw Err(Li.WhenObservation, binding.Pos, "an arm that observes several types names none of them: one is T as t per arm");
                Expr view = new MethodCallExpr(new MethodCallExpr(subject, Dispatch.AddressRoutine, [], [], binding.Pos) { Builder = true }, "to",
                    [new TypeRef("PointedCell", [new TypeArgType(new TypeRef("$stored", [], binding.Pos) { Known = t })], binding.Pos)], [], binding.Pos);
                bool entity = Entities.Holds(t);
                var written = entity
                    ? new TypeRef("PointedCell", [new TypeArgType(new TypeRef("$stored", [], binding.Pos) { Known = t })], binding.Pos)
                    : new TypeRef("$stored", [], binding.Pos) { Known = t };
                if (!entity) view = new MethodCallExpr(view, "peek", [], [], binding.Pos);
                body.Add(new BindStmt(binding.Name, written, view, binding.Pos));
            }
            body.AddRange(arm.Body);
            chain = [new IfStmt(cond!, body, tail ?? (chain.Count > 0 ? chain : null), arm.Pos)];
            tail = null;
        }
        if (tail is not null) chain = tail;
        return [new BindStmt(id, u64, new MethodCallExpr(subject, Dispatch.TypeIdRoutine, [], [], pos) { Builder = true }, pos), .. chain];
    }
}
