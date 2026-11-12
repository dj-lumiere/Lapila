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

    private const string ImplicitSource = """
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

        ### A point.
        record Point
            x: S64

        ### The point at zero.
        ### :returns: The point.
        common routine Point.origin() -> Me
            return Me(x: 0)

        ### Reads a box.
        ### :param b: The box.
        ### :returns: Its value.
        routine open(b: Box[S64]) -> S64
            return b.value

        ### Makes a box in a return.
        ### :returns: The box.
        routine five() -> Box[S64]
            return .construct(value: 5)

        routine start() -> None
            a: Box[S64] = .construct(value: 1)
            p: Point = .origin()
            n: S64 = open(b: .construct(value: 2))
            q: &Box[S64] <- .construct(value: 5)
            drop q
            return
        """;

    private static List<(int Line, int Col, string Label)> Hints(string source = Source)
    {
        string dir = Path.Combine(Path.GetTempPath(), "lapila-inlay-hints-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        string file = Path.Combine(dir, "boxes.lpa");
        File.WriteAllText(file, source);
        try
        {
            return LanguageServer.InferredArgumentHints(file, source, Path.Combine(FindRoot(), "Standard"));
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

    [Fact]
    public void LeadingDotCallInAReturnShowsTheResultType()
    {
        Assert.Contains((36, 12, "Box[S64]"), Hints(ImplicitSource));
    }

    [Fact]
    public void LeadingDotCallInABindingWithEqualsShowsTheTypeOfTheGenericAndTheNonGenericOne()
    {
        var hints = Hints(ImplicitSource);

        Assert.Contains((39, 19, "Box[S64]"), hints);
        Assert.Contains((40, 16, "Point"), hints);
    }

    [Fact]
    public void LeadingDotCallInAnArgumentShowsTheParameterType()
    {
        Assert.Contains((41, 22, "Box[S64]"), Hints(ImplicitSource));
    }

    [Fact]
    public void LeadingDotCallInAPlaceBindingShowsTheTypeWithoutThePlaceMark()
    {
        Assert.Contains((42, 21, "Box[S64]"), Hints(ImplicitSource));
    }

    [Fact]
    public void LeadingDotCallHintsAreTheOnlyOnesInTheSource()
    {
        Assert.Equal(5, Hints(ImplicitSource).Count);
    }

    private const string DispatchSource = """
        import Hosted

        entity Slime
        obeys Enemy[Slime]
            hp: S64

        entity Goblin
        obeys Enemy[Goblin]
            hp: S64

        ### Something with hit points.
        ### :typeparam T: The enemy type.
        protocol Enemy[T]
            ### The hit points left.
            ### :returns: The hit points.
            routine @Me.health() -> S64

        ### A slime.
        ### :param hp: The hit points.
        ### :returns: The slime.
        common routine Slime.construct(hp: S64) -> Me
            return Me(hp: hp)

        ### A goblin.
        ### :param hp: The hit points.
        ### :returns: The goblin.
        common routine Goblin.construct(hp: S64) -> Me
            return Me(hp: hp)

        ### The slime's hit points.
        ### :returns: The hit points.
        routine @Slime.health() -> S64
            return me.hp.peek()

        ### The goblin's hit points.
        ### :returns: The hit points.
        routine @Goblin.health() -> S64
            return me.hp.peek()

        ### Reads an enemy whose type is known while the program runs.
        ### :param e: The enemy.
        ### :returns: Its hit points.
        routine read(e: @Enemy) -> S64
            return e.health()

        ### Reads an enemy whose type is known at buildtime.
        ### :typeparam T: The enemy's type.
        ### :param e: The enemy.
        ### :returns: Its hit points.
        routine read_built[T](e: @T) -> S64
        needs T obeys Enemy
            return e.health()

        routine start() -> None
            slime: &Slime <- .construct(hp: 3)
            one: &Enemy <- steal slime
            a: S64 = one.health()
            b: S64 = read(one)
            goblin: &Goblin <- .construct(hp: 5)
            c: S64 = read_built(goblin)
            Console.show("{a} {b} {c}")
            return
        """;

    private static List<(int Line, int Col, string Tooltip)> DispatchHints()
    {
        string dir = Path.Combine(Path.GetTempPath(), "lapila-inlay-hints-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        string file = Path.Combine(dir, "enemies.lpa");
        File.WriteAllText(file, DispatchSource);
        try
        {
            return LanguageServer.DispatchHints(file, DispatchSource, Path.Combine(FindRoot(), "Standard"));
        }
        finally
        {
            Directory.Delete(dir, true);
        }
    }

    [Fact]
    public void CallsOnAStoredProtocolValueShowDispatchAfterTheRoutineName()
    {
        var at = DispatchHints().Select(h => (h.Line, h.Col)).ToList();

        // A `&Enemy` place and a `@Enemy` parameter: the type is known while the program runs. A `needs T obeys Enemy`
        // body is built for each type, so it gets no hint.
        Assert.Equal([(44, 20), (57, 24)], at);
    }

    [Fact]
    public void DispatchTooltipListsTheTypesThatReachTheProtocol()
    {
        string tooltip = DispatchHints()[0].Tooltip;

        Assert.Contains("while the program runs", tooltip);
        Assert.EndsWith("Types the places of Enemy hold in this build: Slime.", tooltip);
    }
}
