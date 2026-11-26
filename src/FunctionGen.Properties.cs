namespace Lapila;

/// The reads of properties (Properties.cs): before a line is built, each `foe.alive` whose value has no member variable
/// of that name and a `@property` routine of it becomes the call `foe.alive()`, marked `PropertyRead`, so everything
/// after sees an ordinary call. The line's own expressions are turned here, the lines of its bodies when they are built,
/// and an expression the builder reads on its own (a hole of a write template, a loop's condition) when it is
/// evaluated (Desugar).
public sealed partial class FunctionGen
{
    /// The calls the reads became, by the read: one node per read, so what the builder keeps per node stays.
    private readonly Dictionary<FieldExpr, MethodCallExpr> _propertyReads = new(ReferenceEqualityComparer.Instance);

    /// The routines that write into what their receiver (or their first argument) names.
    private static readonly HashSet<string> WritesReceiver =
        ["poke", "poke_volatile", "poke_unbroken", "poke_unaligned", "zeroinit", "copy", "store", "setitem", "swap"];
    private static readonly HashSet<string> WritesArgument = ["poke_into", "store_into", "copy_into"];

    /// The line with its own reads of properties turned into calls, or the line itself when it has none.
    private Stmt WithPropertyReads(Stmt s)
    {
        if (_c.PropertyNames.Count == 0) return s;
        switch (s)
        {
            case BindStmt b: return Same(b.Value, PropertyReads(b.Value)) ? s : b with { Value = PropertyReads(b.Value) };
            case ExprStmt e: return Same(e.Value, PropertyReads(e.Value)) ? s : e with { Value = PropertyReads(e.Value) };
            case DestructureStmt d: return Same(d.Value, PropertyReads(d.Value)) ? s : d with { Value = PropertyReads(d.Value) };
            case ReturnStmt { Value: { } v } r: return Same(v, PropertyReads(v)) ? s : r with { Value = PropertyReads(v) };
            case BecomesStmt bc: return Same(bc.Value, PropertyReads(bc.Value)) ? s : bc with { Value = PropertyReads(bc.Value) };
            case IfStmt i: return Same(i.Cond, PropertyReads(i.Cond)) ? s : i with { Cond = PropertyReads(i.Cond) };
            case JumpStmt j:
            {
                var args = j.Args.Select(PropertyReads).ToList();
                return args.Where((a, k) => !ReferenceEquals(a, j.Args[k])).Any() ? j with { Args = args } : s;
            }
            case ContinueStmt { With: { } with } c:
            {
                var values = with.Select(w => PropertyReads(w.Value)).ToList();
                return values.Where((v, k) => !Same(v, with[k].Value)).Any()
                    ? c with { With = with.Select((w, k) => (w.Name, values[k], w.Pos)).ToList() }
                    : s;
            }
            case WhenStmt { Value: { } wv } w: return Same(wv, PropertyReads(wv)) ? s : w with { Value = PropertyReads(wv) };
            case LoopStmt l:
            {
                var inits = l.With.Select(w => PropertyReads(w.Init)).ToList();
                var source = l.Source is null ? null : PropertyReads(l.Source);
                bool changed = inits.Where((v, k) => !Same(v, l.With[k].Init)).Any() || !ReferenceEquals(source, l.Source);
                return changed ? l with { With = l.With.Select((w, k) => w with { Init = inits[k] }).ToList(), Source = source } : s;
            }
            case FillStmt f:
                NotWritten(f.Place);
                return Same(f.Value, PropertyReads(f.Value)) ? s : f with { Value = PropertyReads(f.Value) };
            case StealStmt st:
                NotWritten(st.From);
                return st.Inject is { } inject && !Same(inject, PropertyReads(inject)) ? st with { Inject = PropertyReads(inject) } : s;
            default: return s;
        }
    }

    private static bool Same(Expr a, Expr b) => ReferenceEquals(a, b);

    /// `e` with its reads of properties turned into calls. A node with none is returned as it is.
    private Expr PropertyReads(Expr e)
    {
        if (_c.PropertyNames.Count == 0) return e;
        switch (e)
        {
            case FieldExpr f:
            {
                if (_propertyReads.TryGetValue(f, out var known)) return known;
                var inner = PropertyReads(f.Base);
                var read = Same(inner, f.Base) ? f : f with { Base = inner };
                if (PropertyCall(read) is { } call)
                {
                    _propertyReads[f] = call;
                    return call;
                }
                return read;
            }
            case MethodCallExpr m:
            {
                var receiver = PropertyReads(m.Receiver);
                var args = Each(m.Args);
                if (WritesReceiver.Contains(m.Name)) NotWritten(receiver);
                if (WritesArgument.Contains(m.Name) && args.Count > 0) NotWritten(args[0]);
                return Same(receiver, m.Receiver) && ReferenceEquals(args, m.Args) ? m : m with { Receiver = receiver, Args = args };
            }
            case CallExpr c: return Each(c.Args) is var ca && !ReferenceEquals(ca, c.Args) ? c with { Args = ca } : c;
            case NsCallExpr n: return Each(n.Args) is var na && !ReferenceEquals(na, n.Args) ? n with { Args = na } : n;
            case ImplicitCallExpr ic: return Each(ic.Args) is var ia && !ReferenceEquals(ia, ic.Args) ? ic with { Args = ia } : ic;
            case BinaryExpr b:
            {
                var (l, r) = (PropertyReads(b.Left), PropertyReads(b.Right));
                return Same(l, b.Left) && Same(r, b.Right) ? b : b with { Left = l, Right = r };
            }
            case ChainedComparison cc: return Each(cc.Operands) is var ops && !ReferenceEquals(ops, cc.Operands) ? cc with { Operands = ops } : cc;
            case UnaryExpr u: return PropertyReads(u.Operand) is var o && !Same(o, u.Operand) ? u with { Operand = o } : u;
            case StealExpr st:
            {
                var v = PropertyReads(st.Value);
                NotWritten(v);
                return Same(v, st.Value) ? st : st with { Value = v };
            }
            case GetItemExpr g:
            {
                var (bs, ix) = (PropertyReads(g.Base), PropertyReads(g.Index));
                return Same(bs, g.Base) && Same(ix, g.Index) ? g : g with { Base = bs, Index = ix };
            }
            case IndexExpr ix:
            {
                var (bs, at) = (PropertyReads(ix.Base), PropertyReads(ix.Index));
                return Same(bs, ix.Base) && Same(at, ix.Index) ? ix : ix with { Base = bs, Index = at };
            }
            case RangeExpr rg:
            {
                var (from, to, step) = (PropertyReads(rg.From), PropertyReads(rg.To), rg.Step is null ? null : PropertyReads(rg.Step));
                return Same(from, rg.From) && Same(to, rg.To) && ReferenceEquals(step, rg.Step) ? rg : rg with { From = from, To = to, Step = step };
            }
            case IfExpr i:
            {
                var (c, t, f) = (PropertyReads(i.Cond), PropertyReads(i.Then), PropertyReads(i.Else));
                return Same(c, i.Cond) && Same(t, i.Then) && Same(f, i.Else) ? i : i with { Cond = c, Then = t, Else = f };
            }
            case RecordLit rl:
            {
                var values = rl.Fields.Select(x => PropertyReads(x.Value)).ToList();
                return values.Where((v, k) => !Same(v, rl.Fields[k].Value)).Any()
                    ? rl with { Fields = rl.Fields.Select((x, k) => (x.Name, values[k], x.Pos)).ToList() }
                    : rl;
            }
            case ArrayLit a: return Each(a.Elements) is var el && !ReferenceEquals(el, a.Elements) ? a with { Elements = el } : a;
            case AtExpr at:
            {
                var (v, m) = (PropertyReads(at.Value), PropertyReads(at.Manager));
                return Same(v, at.Value) && Same(m, at.Manager) ? at : at with { Value = v, Manager = m };
            }
            case TempSlotExpr t: return PropertyReads(t.Value) is var tv && !Same(tv, t.Value) ? t with { Value = tv } : t;
            case WorkExpr w: return Each(w.Args) is var wa && !ReferenceEquals(wa, w.Args) ? w with { Args = wa } : w;
            default: return e;
        }
    }

    /// The list with each expression's reads turned, or the list itself when none changed.
    private List<Expr> Each(List<Expr> list)
    {
        List<Expr>? changed = null;
        for (int i = 0; i < list.Count; i++)
        {
            var x = PropertyReads(list[i]);
            if (Same(x, list[i]) && changed is null) continue;
            changed ??= list.Take(i).ToList();
            changed.Add(x);
        }
        return changed ?? list;
    }

    /// The call a read `base.name` stands for when it reads a property, else null: the value (or what a view or a `&T`
    /// shows) has no member variable of the name, and a `@property` routine of it. A value of a type parameter reads the
    /// property even where the type has the member variable that meets it, so a generic body reads one value.
    private MethodCallExpr? PropertyCall(FieldExpr f)
    {
        if (!_c.PropertyNames.Contains(f.Name)) return null;
        var baseType = InferQuiet(f.Base);
        var held = baseType is PtrType { Pointee: { } pointee } ? pointee : baseType;
        if (held is RecordType { Decl.Name: "BorrowedCell", Args: [var boxed] } box && box.Decl.Module == Compiler.SystemModule) held = boxed;
        if (held is null) return null;
        if (held is RecordType r && _c.Fields(r).Any(x => x.Name == f.Name) && !FromTypeParameter(held)
            && !(Dispatch.IsPlaceDecl(r.Decl) && _decl.Owner?.Name != r.Decl.Name))
            return null;
        List<RoutineDecl> candidates;
        try { candidates = _c.MethodCandidates(held, f.Name, _env.File, f.Pos, anyModule: true); }
        catch (CompileError) { return null; }
        return candidates.Any(Properties.Is) ? new MethodCallExpr(f.Base, f.Name, [], [], f.Pos) { PropertyRead = true } : null;
    }

    /// A property only reads: a write into one (`foe.hp.poke(3)`, `steal foe.hp as old`, `foe.hp <- v from HEAP`) is a
    /// build error.
    private void NotWritten(Expr e)
    {
        if (e is not MethodCallExpr { PropertyRead: true } read) return;
        string owner = InferQuiet(read.Receiver) is { } t ? (t is PtrType { Pointee: { } p } ? p : t).Name : "its type";
        throw Err(Li.PropertyWritten, read.Pos, $"{Spelled(read.Receiver)}.{read.Name} is the @property '{owner}.{read.Name}', which gives a value and has no place "
            + $"to write into: change what it reads with a routine of {owner}");
    }
}
