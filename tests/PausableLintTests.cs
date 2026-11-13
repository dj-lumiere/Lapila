using Xunit;

namespace Lapila.Tests;

/// <summary>
/// The pausable lint: a thread ticket's retrieve() and waitfor inside a pausable routine put the whole thread to sleep
/// (a warning that points to pauseuntil), and the same calls outside one are clean.
/// </summary>
public class PausableLintTests
{
    [Fact]
    public void WaitforWarnsToPauseInstead()
    {
        string warning = Assert.Single(Lint("""
            pausable routine f() -> None
                waitfor(1ms)
                return
            """));
        Assert.Contains("warning[LP-W1006]: t.lpa:2:5: waitfor puts the whole thread to sleep", warning);
        Assert.Contains("pauseuntil Clock.after", warning);
    }

    [Fact]
    public void ThreadRetrieveWarnsToWaitForItsFinish()
    {
        string warning = Assert.Single(Lint("""
            pausable routine f(t: @Thread[S64]) -> S64
                return t.waitfor(5ms).retrieve()
            """));
        Assert.Contains("pauseuntil t.finish()", warning);
    }

    [Fact]
    public void TheSameCallsOutsideAPausableRoutineAreClean()
    {
        Assert.Empty(Lint("""
            routine f(t: @Thread[S64]) -> S64
                waitfor(1ms)
                return t.retrieve()
            """));
    }

    private static List<string> Lint(string source, string file = "t.lpa") =>
        PausableLint.Check(new Parser(new Lexer(file, source).Lex(), file).ParseModule().Decls);
}
