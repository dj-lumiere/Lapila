namespace Lapila;

/// `@property routine Foe.alive() -> Bool`: a routine on a type that is read like a member variable, `foe.alive`, and
/// never called with parentheses. It takes nothing but me, gives a value, and doesn't change me: one that takes me by its
/// address takes it as `%Me`, a view that only reads. A type has no member variable of a property's name.
///
/// A protocol may ask for a property, `@property routine Me.hp() -> S64`. A member variable `hp: S64` of a type that
/// obeys it meets it: the builder writes the property that reads the member variable. A plain routine doesn't meet a
/// property's requirement, and a property doesn't meet a plain one.
///
/// FunctionGen turns each read `foe.alive` into the call `foe.alive()` (marked `PropertyRead`) before it builds the line,
/// so every later step sees an ordinary call.
public static class Properties
{
    /// The annotation that marks a property.
    public const string Mark = "property";

    /// Whether a routine is a property.
    public static bool Is(RoutineDecl r) => r.AnnotationNamed(Mark) is not null;

    /// The properties the builder writes for member variables that meet a protocol's property: one per type and name,
    /// for each record that obeys a protocol (on its own `obeys` line or a top-level one) asking for a property it writes
    /// no routine for and holds a member variable of that name.
    public static IEnumerable<Decl> Declarations(List<Decl> decls)
    {
        var concepts = decls.OfType<ConceptDecl>().GroupBy(c => c.Name).ToDictionary(g => g.Key, g => g.ToList());
        if (!concepts.Values.SelectMany(g => g).Any(c => c.Routines.Any(Is))) return [];
        var declared = decls.OfType<RoutineDecl>().Where(r => r.Owner is not null).Select(r => (r.Owner!.Name, r.Name)).ToHashSet();
        var topLevel = decls.OfType<ConformDecl>().SelectMany(c => c.Clauses.Where(cl => cl.Kind == "conform").SelectMany(cl => cl.Concepts))
            .Where(c => c.Args is [TypeArgType, ..]).ToList();
        var made = new List<Decl>();
        foreach (var r in decls.OfType<RecordDecl>())
        {
            if (Dispatch.IsPlaceDecl(r) || r.Fields.Count == 0) continue;
            var obeyed = r.Clauses.Where(c => c.Kind == "conform").SelectMany(c => c.Concepts)
                .Concat(topLevel.Where(c => ((TypeArgType)c.Args[0]).Type.Name == r.Name));
            var done = new HashSet<string>();
            foreach (var concept in obeyed)
            {
                if (Named(concept.Name, r.Module, concepts) is not { } c) continue;
                foreach (var req in WithParents(c, concepts).SelectMany(p => p.Routines).Where(Is))
                {
                    if (r.Fields.FirstOrDefault(f => f.Name == req.Name) is not { } field || declared.Contains((r.Name, req.Name))
                        || !done.Add(req.Name))
                        continue;
                    made.AddRange(Reading(r, field, byAddress: req.TakesAddress || r.IsEntity));
                }
            }
        }
        return made;
    }

    private static ConceptDecl? Named(string name, string module, Dictionary<string, List<ConceptDecl>> byName) =>
        byName.GetValueOrDefault(name) is { } found ? found.FirstOrDefault(c => c.Module == module) ?? found[0] : null;

    /// A protocol and every protocol it obeys, all the way up.
    private static List<ConceptDecl> WithParents(ConceptDecl c, Dictionary<string, List<ConceptDecl>> byName)
    {
        var found = new List<ConceptDecl> { c };
        for (int i = 0; i < found.Count; i++)
            foreach (var parent in found[i].Clauses.Where(cl => cl.Kind == "conform").SelectMany(cl => cl.Concepts))
                if (Named(parent.Name, found[i].Module, byName) is { } p && !found.Contains(p))
                    found.Add(p);
        return found;
    }

    /// The property that reads a member variable: `return me.hp` on a record value, `return me.hp.peek()` through `%Me`.
    private static List<Decl> Reading(RecordDecl r, FieldDecl field, bool byAddress)
    {
        string self = r.TypeParams.Count == 0 ? r.Name : $"{r.Name}[{string.Join(", ", r.TypeParams)}]";
        string source = $"### Reads the member variable '{field.Name}', the property a protocol asks for. The builder writes it.\n"
                        + $"### :returns: The value of '{field.Name}'.\n@{Mark}\nroutine {(byAddress ? "@" : "")}{self}.{field.Name}() -> None\n"
                        + $"    return me.{field.Name}{(byAddress ? ".peek()" : "")}\n";
        return Derive.Parse(r, source, implicitly: true)
            .Select(d => d is RoutineDecl routine ? routine with { ReturnType = field.Type } : d)
            .ToList();
    }

    /// The shape a property has: a routine on a type that takes nothing but me and gives a value.
    public static void CheckShape(RoutineDecl r)
    {
        if (Is(r) is false) return;
        var at = r.AnnotationNamed(Mark)!.Pos;
        if (r.Owner is null)
            throw new CompileError(Li.PropertyShape, at, $"@property marks a routine on a type that is read like a member variable, x.{r.Name}, "
                + $"and '{r.Name}' is on no type: put it on one, routine Type.{r.Name}() -> T, or drop @property");
        if (r.IsCommon)
            throw new CompileError(Li.PropertyShape, at, $"'{r.DisplayName}' is common and takes no me, and a @property is read from a value, "
                + $"x.{r.Name}: drop common, or drop @property");
        if (r.Params.Skip(1).FirstOrDefault() is { } extra)
            throw new CompileError(Li.PropertyShape, extra.Pos, $"'{r.DisplayName}' is @property and takes '{extra.Name}': a property is read "
                + $"without parentheses, x.{r.Name}, so it takes nothing but me. Drop the parameter, or drop @property and call it with it");
        if (r.TypeParams.Count > 0)
            throw new CompileError(Li.PropertyShape, at, $"'{r.DisplayName}' is @property and takes type parameter(s) "
                + $"({string.Join(", ", r.TypeParams)}): a read x.{r.Name} has nowhere to write them. Drop them, or drop @property");
        if (r.ReturnType is { Name: "None", Args.Count: 0 })
            throw new CompileError(Li.PropertyShape, at, $"'{r.DisplayName}' is @property and gives nothing (-> None): a property is read as a "
                + "value, so give the value it reads, or drop @property for a routine that only does something");
    }
}

public sealed partial class Compiler
{
    /// The names of every property the build knows: a read `x.name` is looked at as a property only for these.
    public HashSet<string> PropertyNames { get; } = [];

    /// The checks of the program's properties that need no use: each one's shape, and no member variable of its name on its
    /// type.
    private void CheckProperties()
    {
        foreach (var r in _allRoutines.Where(Properties.Is)) PropertyNames.Add(r.Name);
        foreach (var r in _conceptDecls.Values.SelectMany(g => g).SelectMany(c => c.Routines).Where(Properties.Is)) PropertyNames.Add(r.Name);
        foreach (var r in _allRoutines.Where(r => !r.IsLibrary && Properties.Is(r))) Properties.CheckShape(r);
        foreach (var r in _conceptDecls.Values.SelectMany(g => g).Where(c => !c.IsLibrary).SelectMany(c => c.Routines)) Properties.CheckShape(r);
        foreach (var r in _allRoutines.Where(r => !r.IsLibrary && Properties.Is(r) && !Derive.IsImplicit(r)))
        {
            if (OwnerDeclQuiet(r) is not RecordDecl owner || Dispatch.IsPlaceDecl(owner)) continue;
            if (owner.Fields.FirstOrDefault(f => f.Name == r.Name) is { } field)
                throw new CompileError(Li.PropertyNameTaken, r.Pos, $"{(owner.IsEntity ? "entity" : "record")} '{owner.Name}' has a member variable "
                    + $"'{field.Name}' (at {field.Pos}) and the @property '{r.DisplayName}': x.{r.Name} would read either. Rename one, or drop "
                    + "the routine: a member variable meets a protocol's @property of its name by itself");
        }
    }
}
