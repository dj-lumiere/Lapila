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

    /// The parameters of each routine instance that take an access over: a caller hands it with `steal`, and the
    /// parameter's drop (or the end of the routine) gives it back.
    private readonly Dictionary<string, SortedSet<int>> _taken = [];

    /// What each instance's build read of its taken parameters: an instance built before a caller handed it an access
    /// is built again (FinishThrows).
    private readonly Dictionary<string, string> _observedTaken = [];

    /// Every argument a routine of the program got at a view parameter: whether it was an access handed over with
    /// `steal`, where, and the names a message uses.
    private readonly List<(string Routine, int Index, bool Stolen, Pos Pos, string Shown, string Param)> _viewArgs = [];

    /// A call hands an access over to the parameter `index` of `routine` with `steal`.
    public void NoteTaken(string routine, int index)
    {
        lock (_facts)
            if (!_taken.TryGetValue(routine, out var set)) _taken[routine] = [index];
            else set.Add(index);
    }

    /// The parameters of `routine` that take an access over, as its build reads them.
    public IReadOnlySet<int> Taken(string routine)
    {
        lock (_facts)
        {
            var set = _taken.TryGetValue(routine, out var found) ? new SortedSet<int>(found) : [];
            _observedTaken[routine] = string.Join(",", set);
            return set;
        }
    }

    /// The instances whose build read fewer taken parameters than calls hand them now.
    public IEnumerable<string> StaleTaken()
    {
        lock (_facts)
            return _taken.Where(kv => _observedTaken.GetValueOrDefault(kv.Key, "") != string.Join(",", kv.Value)).Select(kv => kv.Key).ToList();
    }

    /// An argument at a view parameter of a routine of the program.
    public void NoteViewArg(string routine, int index, bool stolen, Pos pos, string shown, string param)
    {
        lock (_facts) _viewArgs.Add((routine, index, stolen, pos, shown, param));
    }

    /// A parameter that takes an access over gets one on every call: a view without `steal` there would be given back
    /// by a routine that never took it.
    public IEnumerable<CompileError> CheckTaken()
    {
        List<(string Routine, int Index, bool Stolen, Pos Pos, string Shown, string Param)> args;
        lock (_facts) args = [.. _viewArgs];
        foreach (var bad in args.Where(a => !a.Stolen && _taken.TryGetValue(a.Routine, out var set) && set.Contains(a.Index)).Distinct())
        {
            var by = args.First(a => a.Stolen && a.Routine == bad.Routine && a.Index == bad.Index);
            yield return new CompileError(Li.AccessHandedOver, bad.Pos, $"'{bad.Shown}' takes over the access at '{bad.Param}' (the call on line "
                + $"{by.Pos.Line} hands it one with steal), and gives it back, so every call hands it an access with steal: this one hands a view");
        }
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
        foreach (var e in CheckTaken()) yield return e;
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
