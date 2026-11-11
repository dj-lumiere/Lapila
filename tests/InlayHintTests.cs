using Xunit;

namespace Lapila.Tests;

/// <summary>
/// The language server's inlay hints for type arguments the builder inferred: a gray <c>[Bool]</c> right after the
/// routine's or the type's name, and nothing where the source wrote them or a generic body still holds parameters.
/// </summary>
[Collection(WorkingDirectoryCollection.Name)]
public class InlayHintTests
{
    private const string Source = """
        ### A box.
        record Box[T]
        needs RecordType T
            value: T

        ### Makes a `Box` from its fields.
        ### :param value: Its `value`.
        ### :returns: The new value.
        common routine Box[T].construct(value: T) -> Me
        needs RecordType T
            return Me(value)

        ### Releases nothing.
        routine @Box[T].destruct() -> None
        needs RecordType T
            return

        ### Gives the value back.
        ### :param value: The value.
        ### :returns: The same value.
        routine same[T](value: T) -> T
        needs RecordType T
            return value

        ### Gives back what it is handed, on a box.
        ### :param other: The value.
        ### :returns: The same value.
        routine Box[T].pass[U](other: U) -> U
        needs RecordType T, RecordType U
            return other

        ### Calls a generic routine inside a generic body.
        ### :param value: The value.
        ### :returns: The same value.
        routine wrap[T](value: T) -> T
        needs RecordType T
            return same(value)

        routine start() -> None
            a: S64 = same(5)
            b: S64 = same[S64](5)
            box: Box[S64] = Box[S64].construct(value: 1)
            c: Bool = box.pass(true)
            d: Bool = box.pass[Bool](true)
            e: S64 = wrap(3)
            return
        """;

    private static List<(int Line, int Col, string Label)> Hints()
    {
        string dir = Path.Combine(Path.GetTempPath(), "lapila-inlay-hints-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        string file = Path.Combine(dir, "boxes.lpa");
        File.WriteAllText(file, Source);
        try
        {
            return LanguageServer.InferredArgumentHints(file, Source, Path.Combine(FindRoot(), "Standard"));
        }
        finally
        {
            Directory.Delete(dir, true);
        }
    }

    private static string FindRoot()
    {
        for (var dir = new DirectoryInfo(AppContext.BaseDirectory); dir is not null; dir = dir.Parent)
            if (File.Exists(Path.Combine(dir.FullName, "Standard", "System", "Prelude.lpa")))
                return dir.FullName;
        throw new InvalidOperationException("no Standard/ above the test assembly");
    }

    [Fact]
    public void InferredRoutineArgumentsShowAfterTheRoutineName()
    {
        var hints = Hints();

        Assert.Contains((40, 18, "[S64]"), hints);
        Assert.Contains((45, 18, "[S64]"), hints);
    }

    [Fact]
    public void InferredMethodArgumentsShowAfterTheMethodName()
    {
        Assert.Contains((43, 23, "[Bool]"), Hints());
    }

    [Fact]
    public void WrittenArgumentsGetNoHint()
    {
        Assert.DoesNotContain(Hints(), h => h.Line is 41 or 42 or 44);
    }

    [Fact]
    public void GenericBodiesGetNoHint()
    {
        Assert.DoesNotContain(Hints(), h => h.Line <= 37);
    }
}
