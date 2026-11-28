using System.Text.RegularExpressions;
using Xunit;

namespace Lapila.Tests;

/// <summary>
/// A routine handed a view of a place known to hold one type is built for that type (tests/protocol_place_known.lpa):
/// its instance takes the place with noalias and calls the type's routines without testing the type id, and a place
/// whose type isn't known (an element of a list) reaches the instance that tests it.
/// </summary>
[Collection(WorkingDirectoryCollection.Name)]
public class KnownPlaceIrTests
{
    private static readonly Lazy<string> Ir = new(() => Compile("protocol_place_known.lpa"));

    private static IEnumerable<string> Defines(string symbolPart) =>
        Ir.Value.Split('\n').Where(l => l.StartsWith("define ", StringComparison.Ordinal) && l.Contains(symbolPart, StringComparison.Ordinal));

    [Fact]
    public void EachKnownTypeHasItsOwnRun()
    {
        var known = Defines("@_Z3runB").ToList();
        Assert.Equal(2, known.Count);
        Assert.All(known, l => Assert.Contains("ptr noalias %a.e", l));
        Assert.Single(Defines("@_Z3runN"));
    }

    [Fact]
    public void AKnownDispatchCallsWithoutATest()
    {
        var known = Defines("@_ZN5Enemy6updateB").ToList();
        Assert.Equal(2, known.Count);
        foreach (var line in known)
        {
            string body = Body(line);
            Assert.DoesNotContain("icmp", body);
            Assert.Single(Regex.Matches(body, @"call void @_ZN(5Slime|6Goblin)6update"));
        }
    }

    /// The body of the routine defined on `line`, up to its closing brace.
    private static string Body(string line)
    {
        int start = Ir.Value.IndexOf(line, StringComparison.Ordinal);
        return Ir.Value[start..Ir.Value.IndexOf("\n}", start, StringComparison.Ordinal)];
    }

    private static string Compile(string test)
    {
        string root = FindRoot();
        Directory.SetCurrentDirectory(root);
        return Cli.Compile([Path.Combine(root, "tests", test)], BuildTarget.Host(), lint: false, trace: false);
    }

    private static string FindRoot()
    {
        for (var dir = new DirectoryInfo(AppContext.BaseDirectory); dir is not null; dir = dir.Parent)
            if (File.Exists(Path.Combine(dir.FullName, "Standard", "System", "Prelude.lpa"))
                && Directory.Exists(Path.Combine(dir.FullName, "tests")))
                return dir.FullName;
        throw new InvalidOperationException("can't find the Lapila repository above the test assembly");
    }
}
