namespace Lapila;

/// The warning for a call inside a pausable routine that puts the whole thread to sleep: a thread ticket's `retrieve()`
/// and `waitfor(d)`. Allowed, since they end by themselves, but every other piece of work of the thread's CoroutineManager
/// waits with them, where `pauseuntil t.finish()` and `pauseuntil Clock.after(d)` stop only this routine.
///
/// A warning, like LoopLint's: `lapila check`, `build`, and `run` print it for the program's own files.
public static class PausableLint
{
    public static List<string> Check(IEnumerable<Decl> decls)
    {
        var warnings = new List<string>();
        foreach (var r in decls.OfType<RoutineDecl>().Where(r => r is { IsPausable: true, Blocks: not null }))
        {
            var types = r.Params.ToDictionary(p => p.Name, p => p.Type);
            foreach (var b in r.Blocks!.SelectMany(b => Bodies.All(b.Stmts)).OfType<BindStmt>()) types.TryAdd(b.Name, b.Type);
            foreach (var s in r.Blocks!.SelectMany(b => Bodies.All(b.Stmts)))
                foreach (var top in Bodies.Exprs(s))
                    foreach (var e in ExprTree.All(top))
                    {
                        if (e is MethodCallExpr { Name: "retrieve" or "retrieve_all" } m
                            && (m.Receiver is MethodCallExpr { Name: "waitfor" } w ? w.Receiver : m.Receiver) is ValueRef v
                            && types.TryGetValue(v.Name, out var t)
                            && (t is { Name: "PointedCell", Args: [TypeArgType inner] } ? inner.Type : t).Name == "Thread")
                            warnings.Add($"{Li.PausableBlocksThread.Head}: {m.Pos}: '{v.Name}.{m.Name}()' puts the whole thread to sleep until the "
                                + $"work is done, and the other work of this thread's CoroutineManager waits with it: wait with pauseuntil "
                                + $"{v.Name}.finish(), which stops only '{r.Name}'");
                        if (e is CallExpr { Name: "waitfor", Path: null or "Hosted" } c)
                            warnings.Add($"{Li.PausableBlocksThread.Head}: {c.Pos}: waitfor puts the whole thread to sleep, and the other work of "
                                + $"this thread's CoroutineManager waits with it: pauseuntil Clock.after(...) stops only '{r.Name}'");
                    }
        }
        return warnings;
    }
}
