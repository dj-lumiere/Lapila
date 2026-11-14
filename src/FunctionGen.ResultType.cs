namespace Lapila;

/// A call whose type argument comes only from its result (`n.to()`, a generic routine whose type parameter only its
/// result names) takes it from where the value goes. That type flows inward, never from later uses of a name: from a
/// binding's written type, a parameter, a return type, down a chain of calls that give back their receiver's type
/// (`n.to().sqrt().sin()`, and an operator, which is such a call: `n.to() * x` is `n.to().mul(x)`), and across a
/// comparison from its other side.
public sealed partial class FunctionGen
{
    /// The routines a comparison is made of.
    private static bool IsComparisonName(string name) => name is "eq" or "ne" or "lt" or "le" or "gt" or "ge" or "compare";

    /// The conversions whose target type is their type argument.
    private static bool IsConversionName(string name) => name is "to" or "to_wrap" or "to_clamp";

    /// Whether `e` has no type of its own until it is told one: a conversion without its type argument, a generic routine
    /// whose type parameter only its result names called without it, or a call, an operator or a negation made on one.
    private bool NeedsResultType(Expr e) => e switch
    {
        MethodCallExpr { TypeArgs.Count: 0, Args.Count: 0 } conv when IsConversionName(conv.Name) =>
            ConversionsAllTyped(conv),
        MethodCallExpr { TypeArgs.Count: 0 } call => NeedsResultType(call.Receiver),
        BinaryExpr { Op: not ("and" or "or") } b => NeedsResultType(b.Left),
        UnaryExpr { Op: "-" or "~" } u => NeedsResultType(u.Operand),
        CallExpr { TypeArgs.Count: 0 } free => ResultOnlyTypeParam(free) is not null,
        _ => false,
    };

    /// Whether every conversion of that name on the receiver's type is defined for a type argument, so the call names
    /// none of them until a type is given. A receiver of no type yet counts too.
    private bool ConversionsAllTyped(MethodCallExpr conv)
    {
        if (TryInfer(conv.Receiver) is not { } owner) return NeedsResultType(conv.Receiver);
        var held = owner is PtrType { Pointee: { } pointee } ? pointee : owner;
        var defined = _c.MethodsNamed(held, conv.Name);
        if (defined.Count == 0 && !ReferenceEquals(held, owner)) defined = _c.MethodsNamed(owner, conv.Name);
        return defined.Count > 0 && defined.All(d => d.Fixed.Count > 0);
    }

    /// The type parameter of the one routine a free call names, when that routine has exactly one and only its result
    /// names it (`ask[T]() -> T`), or null.
    private string? ResultOnlyTypeParam(CallExpr call)
    {
        List<RoutineDecl> candidates;
        try { candidates = _c.FreeCandidates(call.Name, _env.File, call.Pos, call.Path); }
        catch (CompileError) { return null; }
        if (candidates is not [{ TypeParams: [var only] } routine]) return null;
        return Mentions(routine.ReturnType, only) && !routine.Params.Any(p => Mentions(p.Type, only))
            ? only
            : null;
    }

    /// Whether a written type names the type parameter `name`.
    private static bool Mentions(TypeRef type, string name) =>
        type.Name == name || type.Args.Any(a => a is TypeArgType { Type: var inner } && Mentions(inner, name));

    /// `e` with the type `t` given where it needs one (see NeedsResultType), when `e` then has that type: a conversion
    /// takes it as its type argument, a call on such a value gives it to its receiver, an operator to its operands. Null
    /// when the result would be another type (`n.to().count()` with a U64 count of something that isn't a U64).
    private Expr? WithResultType(Expr e, DType t)
    {
        Expr? typed = e switch
        {
            MethodCallExpr { TypeArgs.Count: 0, Args.Count: 0 } conv when IsConversionName(conv.Name) && ConversionsAllTyped(conv) =>
                NeedsResultType(conv.Receiver)
                    ? null
                    : conv with { TypeArgs = [new TypeRef(t.Name, [], conv.Pos) { Known = t }] },
            MethodCallExpr { TypeArgs.Count: 0 } call when !IsComparisonName(call.Name) && NeedsResultType(call.Receiver) =>
                WithResultType(call.Receiver, t) is { } receiver ? call with { Receiver = receiver } : null,
            BinaryExpr { Op: not ("and" or "or") } b when NeedsResultType(b.Left) =>
                WithResultType(b.Left, t) is { } left
                    ? b with { Left = left, Right = NeedsResultType(b.Right) ? WithResultType(b.Right, t) ?? b.Right : b.Right }
                    : null,
            UnaryExpr { Op: "-" or "~" } u when NeedsResultType(u.Operand) =>
                WithResultType(u.Operand, t) is { } operand ? u with { Operand = operand } : null,
            CallExpr { TypeArgs.Count: 0 } free when ResultOnlyTypeParam(free) is not null =>
                free with { TypeArgs = [new TypeRef(t.Name, [], free.Pos) { Known = t }] },
            _ => null,
        };
        return typed is not null && TryInfer(typed) is { } given && given.Equals(t) ? typed : null;
    }

    /// The other side of a comparison gives a side that needs a type its own (`n.to() < limit`), when the comparison's
    /// routine on that type takes it. Null when it doesn't, or nothing needs it.
    private BinaryExpr? ComparisonWithResultType(BinaryExpr b)
    {
        if (b.Op is not ("==" or "!=" or "<" or "<=" or ">" or ">=") || !NeedsResultType(b.Left) || NeedsResultType(b.Right)
            || TryInfer(b.Right) is not { } known || known is PtrType)
            return null;
        return WithResultType(b.Left, known) is { } left ? b with { Left = left } : null;
    }

    /// What the message of a call that still has no type says about the places looked at.
    private const string ResultTypePlaces =
        "the builder looks at a binding's written type, a parameter, a return type, a call on the result (an operator too) "
        + "that gives back its receiver's type, and the other side of a comparison";
}
