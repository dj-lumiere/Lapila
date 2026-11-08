using Xunit;

namespace Lapila.Tests;

/// <summary>
/// The language server's doc comment help: the frame `###` fills in above a declaration, and the quick fixes that add
/// the lines a doc comment lacks or remove the ones that name nothing.
/// </summary>
public class DocCommentTests
{
    private static string Doc(params string[] lines) => string.Join("\n", lines) + "\n";

    private static readonly string[] Clamp =
    [
        "routine clamp[T](value: S64, low: S64) -> S64",
        "    if value < low",
        "        throw HardwareFault(description: \"low\")",
        "    return value",
    ];

    /// <summary>The text after the quick fix called <paramref name="title"/> is applied on the line holding
    /// <paramref name="needle"/>, or null when it is not offered.</summary>
    private static string? Fix(string source, string needle, string title)
    {
        string[] lines = source.Split('\n');
        int line = Array.FindIndex(lines, l => l.Contains(needle));
        var fix = LanguageServer.DocFixes(source, line, line).FirstOrDefault(f => f.Title == title);
        if (fix.Title is null) return null;
        return string.Join("\n", lines.Take(fix.StartLine).Append(fix.NewText).Concat(lines.Skip(fix.EndLine + 1)));
    }

    [Fact]
    public void Frame_Routine_HasEveryLine()
    {
        string source = Doc([.. new[] { "###" }, .. Clamp]);
        Assert.Equal(string.Join("\n", "###", "### :typeparam T:", "### :param value:", "### :param low:", "### :returns:",
            "### :throws: {HardwareFault}"), LanguageServer.DocFrame(source, 0, snippet: false));
    }

    [Fact]
    public void Frame_Snippet_PutsTabStops()
    {
        string source = Doc("###", "routine show(text: S64) -> None", "    return");
        Assert.Equal("### $1\n### :param text: $2$0", LanguageServer.DocFrame(source, 0, snippet: true));
    }

    [Fact]
    public void Frame_UnderAnExistingDoc_IsNotOffered()
    {
        string source = Doc([.. new[] { "### Clamps.", "###" }, .. Clamp]);
        Assert.Null(LanguageServer.DocFrame(source, 1, snippet: false));
    }

    [Fact]
    public void Frame_AboveAType_IsTheSummary()
    {
        string source = Doc("###", "record Point", "    x: S64", "    y: S64");
        Assert.Equal("###", LanguageServer.DocFrame(source, 0, snippet: false));
    }

    [Fact]
    public void Fill_AddsMissingLinesInOrder()
    {
        string source = Doc([.. new[] { "### Clamps a value.", "### :param low: The floor.", "###     It is kept." }, .. Clamp]);
        Assert.Equal(Doc([.. new[]
            {
                "### Clamps a value.", "### :typeparam T:", "### :param value:", "### :param low: The floor.",
                "###     It is kept.", "### :returns:", "### :throws: {HardwareFault}",
            }, .. Clamp]), Fix(source, "routine clamp", "Fill in the doc comment"));
    }

    [Fact]
    public void Fill_Complete_IsNotOffered()
    {
        string source = Doc([.. new[]
        {
            "### Clamps.", "### :typeparam T: Unused.", "### :param value: V.", "### :param low: L.", "### :returns: R.",
            "### :throws: {HardwareFault} when low.",
        }, .. Clamp]);
        Assert.Null(Fix(source, "routine clamp", "Fill in the doc comment"));
    }

    [Fact]
    public void Remove_DropsStaleLines()
    {
        string source = Doc("### Shows.", "### :param text: The text.", "### :param gone: Old.", "### :returns: Nothing.",
            "routine show(text: S64) -> None", "    return");
        Assert.Equal(Doc("### Shows.", "### :param text: The text.", "routine show(text: S64) -> None", "    return"),
            Fix(source, "### :param gone", "Remove doc lines that match nothing"));
    }
}
