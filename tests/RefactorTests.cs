using Xunit;

namespace Lapila.Tests;

/// <summary>
/// The language server's refactors that cut indentation: invert an <c>if</c>, turn it into an early exit, merge it
/// with the <c>if</c> it holds. Each test applies the action's edit to the text and compares the result.
/// </summary>
public class RefactorTests
{
    private static string Doc(params string[] lines) => string.Join("\n", lines) + "\n";

    /// <summary>The text after the action called <paramref name="title"/> is applied on the line holding <paramref name="needle"/>, or null when it is not offered.</summary>
    private static string? Apply(string source, string needle, string title)
    {
        string[] lines = source.Split('\n');
        int line = Array.FindIndex(lines, l => l.Contains(needle));
        var action = LanguageServer.Refactors(source, line, line).FirstOrDefault(r => r.Title == title);
        if (action is null) return null;
        return string.Join("\n", lines.Take(action.StartLine).Append(action.NewText).Concat(lines.Skip(action.EndLine + 1)));
    }

    [Fact]
    public void Invert_Integer_FlipsAndKeepsComments()
    {
        string source = Doc("routine start() -> None", "    n: S64 = 5", "    if n < 3", "        Console.show(\"small\")", "",
            "        Console.show(\"still\")", "    else", "        # the big case", "        Console.show(\"big\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    n: S64 = 5", "    if n >= 3", "        # the big case",
            "        Console.show(\"big\")", "    else", "        Console.show(\"small\")", "", "        Console.show(\"still\")", "    return"),
            Apply(source, "if n < 3", "Invert 'if'"));
    }

    [Fact]
    public void Invert_Float_IsWrappedInNot()
    {
        string source = Doc("routine start() -> None", "    x: B64 = 0.5", "    if x < 1.0", "        Console.show(\"low\")", "    else",
            "        Console.show(\"high\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    x: B64 = 0.5", "    if not (x < 1.0)", "        Console.show(\"high\")", "    else",
            "        Console.show(\"low\")", "    return"), Apply(source, "if x < 1.0", "Invert 'if'"));
    }

    [Fact]
    public void Invert_EqualityAndLogic_SwapAndGoThroughDeMorgan()
    {
        string source = Doc("routine start() -> None", "    a: S64 = 1", "    b: S64 = 2", "    if a == 1 and (b != 2 or a > 3)",
            "        Console.show(\"yes\")", "    else", "        Console.show(\"no\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    a: S64 = 1", "    b: S64 = 2", "    if a != 1 or (b == 2 and a <= 3)",
            "        Console.show(\"no\")", "    else", "        Console.show(\"yes\")", "    return"),
            Apply(source, "if a == 1", "Invert 'if'"));
    }

    [Fact]
    public void Invert_NotOffered_WithoutElseOrWithElseif()
    {
        Assert.Null(Apply(Doc("routine start() -> None", "    n: S64 = 5", "    if n < 3", "        Console.show(\"a\")", "    return"),
            "if n < 3", "Invert 'if'"));
        Assert.Null(Apply(Doc("routine start() -> None", "    n: S64 = 5", "    if n < 3", "        Console.show(\"a\")",
            "    elseif n < 6", "        Console.show(\"b\")", "    else", "        Console.show(\"c\")", "    return"),
            "if n < 3", "Invert 'if'"));
    }

    [Fact]
    public void Guard_Return_MovesTheBodyOutOneLevel()
    {
        string source = Doc("routine start() -> None", "    n: S64 = 5", "    if n > 2", "        Console.show(\"big\")",
            "        # note", "        Console.show(\"really\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    n: S64 = 5", "    if n <= 2", "        return", "    Console.show(\"big\")",
            "    # note", "    Console.show(\"really\")", "    return"), Apply(source, "if n > 2", "Exit early with 'return'"));
    }

    [Fact]
    public void Guard_WithResult_MovesTheFinalReturnIntoTheGuard()
    {
        string source = Doc("routine pick(n: S64) -> S64", "    if n > 2", "        Console.show(\"big\")", "        return 1", "    return 0");
        Assert.Equal(Doc("routine pick(n: S64) -> S64", "    if n <= 2", "        return 0", "    Console.show(\"big\")", "    return 1"),
            Apply(source, "if n > 2", "Exit early with 'return'"));
    }

    [Fact]
    public void Guard_Float_IsWrappedInNot()
    {
        string source = Doc("routine start() -> None", "    x: B64 = 0.5", "    if x > 0.25", "        Console.show(\"big\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    x: B64 = 0.5", "    if not (x > 0.25)", "        return", "    Console.show(\"big\")", "    return"),
            Apply(source, "if x > 0.25", "Exit early with 'return'"));
    }

    [Fact]
    public void Guard_InLoop_UsesContinue()
    {
        string source = Doc("routine start() -> None", "    for i: S64 in 0 til 3", "        if i > 0", "            Console.show(\"p\")",
            "            Console.show(\"q\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    for i: S64 in 0 til 3", "        if i <= 0", "            continue",
            "        Console.show(\"p\")", "        Console.show(\"q\")", "    return"), Apply(source, "if i > 0", "Exit early with 'continue'"));
    }

    [Fact]
    public void Guard_NotOffered_WhereCodeFollowsTheIf()
    {
        Assert.Null(Apply(Doc("routine start() -> None", "    n: S64 = 5", "    if n > 2", "        Console.show(\"big\")",
            "    Console.show(\"after\")", "    return"), "if n > 2", "Exit early with 'return'"));
        Assert.Null(Apply(Doc("routine start() -> None", "    for i: S64 in 0 til 3", "        if i > 0", "            Console.show(\"p\")",
            "        Console.show(\"every\")", "    return"), "if i > 0", "Exit early with 'continue'"));
        Assert.Null(Apply(Doc("routine pick(n: S64) -> S64", "    if n > 2", "        return 1", "    # otherwise", "    return 0"),
            "if n > 2", "Exit early with 'return'"));
    }

    [Fact]
    public void Merge_NestedIf_JoinsWithAnd()
    {
        string source = Doc("routine start() -> None", "    a: S64 = 1", "    b: S64 = 2", "    if a > 0 or b > 5", "        if b > 1",
            "            Console.show(\"both\")", "            # kept", "            Console.show(\"still\")", "    return");
        Assert.Equal(Doc("routine start() -> None", "    a: S64 = 1", "    b: S64 = 2", "    if (a > 0 or b > 5) and b > 1",
            "        Console.show(\"both\")", "        # kept", "        Console.show(\"still\")", "    return"),
            Apply(source, "if a > 0", "Merge nested 'if'"));
    }

    [Fact]
    public void Merge_NotOffered_WithElseOrMoreStatements()
    {
        Assert.Null(Apply(Doc("routine start() -> None", "    a: S64 = 1", "    if a > 0", "        if a > 1", "            Console.show(\"x\")",
            "    else", "        Console.show(\"y\")", "    return"), "if a > 0", "Merge nested 'if'"));
        Assert.Null(Apply(Doc("routine start() -> None", "    a: S64 = 1", "    if a > 0", "        if a > 1", "            Console.show(\"x\")",
            "        Console.show(\"z\")", "    return"), "if a > 0", "Merge nested 'if'"));
    }
}
