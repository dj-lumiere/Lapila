namespace Lapila;

/// What each built routine does with the accesses it takes from the AccessManager, for the memory check across
/// routines: whether it returns an access (one it takes, or one a routine it calls returns), and which parameters'
/// accesses it gives back (itself, or by handing them to a routine that does). FunctionGen notes the facts as it builds
/// each routine, and the deferred memory check asks once every routine is built.
public sealed class AccessFacts
{
    private sealed class Facts
    {
        public bool Returns;
        public readonly HashSet<string> ReturnsFrom = [];
        public readonly HashSet<int> GivesBack = [];
        public readonly HashSet<(int Param, string Callee, int Index)> Passes = [];
    }

    private readonly Dictionary<string, Facts> _facts = [];

    /// One routine's facts, as a summary keeps them (InstanceSummaries.cs).
    public sealed record Snapshot(bool Returns, string[] ReturnsFrom, int[] GivesBack, (int Param, string Callee, int Index)[] Passes);

    public Snapshot? SnapshotOf(string routine)
    {
        lock (_facts)
            return _facts.TryGetValue(routine, out var f) ? new Snapshot(f.Returns, [.. f.ReturnsFrom], [.. f.GivesBack], [.. f.Passes]) : null;
    }

    public void Restore(string routine, Snapshot kept)
    {
        lock (_facts)
        {
            var f = Of(routine);
            f.Returns |= kept.Returns;
            f.ReturnsFrom.UnionWith(kept.ReturnsFrom);
            f.GivesBack.UnionWith(kept.GivesBack);
            f.Passes.UnionWith(kept.Passes);
        }
    }

    private Facts Of(string routine)
    {
        if (!_facts.TryGetValue(routine, out var f)) _facts[routine] = f = new Facts();
        return f;
    }

    /// `routine` returns an access it took.
    public void NoteReturns(string routine)
    {
        lock (_facts) Of(routine).Returns = true;
    }

    /// `routine` returns what a call to `callee` gave.
    public void NoteReturnsFrom(string routine, string callee)
    {
        lock (_facts) Of(routine).ReturnsFrom.Add(callee);
    }

    /// `routine` gives back the access its parameter `param` is.
    public void NoteGivesBack(string routine, int param)
    {
        lock (_facts) Of(routine).GivesBack.Add(param);
    }

    /// `routine` hands its parameter `param` to the parameter `index` of `callee`.
    public void NotePasses(string routine, int param, string callee, int index)
    {
        lock (_facts) Of(routine).Passes.Add((param, callee, index));
    }

    /// The `<-` lines that took an access from a routine of the program: `name` on line `pos` from `routine`.
    private readonly List<(string Routine, string Name, Pos Pos)> _boundFrom = [];

    /// `name` was bound with `<-` to what `routine` returns, as an access whose drop gives it back.
    public void NoteBoundFrom(string routine, string name, Pos pos)
    {
        lock (_facts) _boundFrom.Add((routine, name, pos));
    }

    /// A `<-` line that took an access from a routine that returns a view and no access: the name's drop would give
    /// back an access nobody took.
    public IEnumerable<CompileError> CheckBoundFrom()
    {
        List<(string Routine, string Name, Pos Pos)> lines;
        lock (_facts) lines = [.. _boundFrom];
        foreach (var (routine, name, pos) in lines.Distinct())
            if (!ReturnsAccess(routine))
                yield return new CompileError(Li.BorrowForm, pos, $"'{name}' is bound with '<-' as an access, and the routine on the right returns a "
                    + $"view, not an access it took: bind the view with '=' ({name}: @T = ...)");
    }

    /// Whether `routine` returns an access, itself or through the routines it returns the result of.
    public bool ReturnsAccess(string routine)
    {
        lock (_facts) return Returns(routine, []);
    }

    private bool Returns(string routine, HashSet<string> seen)
    {
        if (!seen.Add(routine) || !_facts.TryGetValue(routine, out var f)) return false;
        return f.Returns || f.ReturnsFrom.Any(callee => Returns(callee, seen));
    }

    /// Whether `routine` gives back the access its parameter `index` is, itself or through the routines it hands it to.
    public bool GivesBack(string routine, int index)
    {
        lock (_facts) return GivesBack(routine, index, []);
    }

    private bool GivesBack(string routine, int index, HashSet<(string, int)> seen)
    {
        if (!seen.Add((routine, index)) || !_facts.TryGetValue(routine, out var f)) return false;
        return f.GivesBack.Contains(index)
               || f.Passes.Any(p => p.Param == index && GivesBack(p.Callee, p.Index, seen));
    }
}
