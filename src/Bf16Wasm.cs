using System.Text;
using System.Text.RegularExpressions;

namespace Lapila;

/// Works out BF16 arithmetic in B32 on wasm32. LLVM's WebAssembly backend can't convert between bfloat and float (it
/// stops with "Cannot select: bf16_to_fp"), and every bfloat operation but a load, a store and a bitcast needs one. So
/// each such instruction becomes the same operation on floats: an operand widens exactly through its bits (a bfloat
/// is the top half of a float), and a result narrows to the nearest bfloat, ties to even, a NaN kept quiet with its
/// sign and top payload bits, as `B32.to_unchecked[BF16]()` does. One rounding of an exact float sum, difference,
/// product or quotient of two bfloats is the bfloat result, since a float's 24 bits are more than twice a bfloat's 8
/// and 2 more. The rewrite works on the text of the functions, one line at a time. The backend holds a bfloat it
/// loads, stores or passes as a float too, so once the arithmetic is floats every other bfloat becomes the i16 of its
/// bits (AsBits): a bitcast between the two is then from i16 to i16, which LLVM drops.
public static partial class Bf16Wasm
{
    /// An instruction that names its result, its text after `=`, and its `!dbg` (or other metadata) at the end.
    [GeneratedRegex("""^(\s+)(%(?:[-A-Za-z$._][-\w$.]*|"[^"]*"|\d+)) = (.*?)((?:, ![\w.]+ ![\w.]+)*)$""")]
    private static partial Regex Definition();

    /// `fadd bfloat %a, %b` and the other arithmetic, with any fast-math flags.
    [GeneratedRegex("""^(fadd|fsub|fmul|fdiv|frem)((?: (?:fast|nnan|ninf|nsz|arcp|contract|afn|reassoc))*) bfloat (\S+), (\S+)$""")]
    private static partial Regex Arithmetic();

    /// `fneg bfloat %a`.
    [GeneratedRegex("""^fneg(?: (?:fast|nnan|ninf|nsz|arcp|contract|afn|reassoc))* bfloat (\S+)$""")]
    private static partial Regex Negation();

    /// `fcmp olt bfloat %a, %b`.
    [GeneratedRegex("""^fcmp((?: (?:fast|nnan|ninf|nsz|arcp|contract|afn|reassoc))*) (\w+) bfloat (\S+), (\S+)$""")]
    private static partial Regex Comparison();

    /// `fpext bfloat %a to double`.
    [GeneratedRegex("""^fpext bfloat (\S+) to (\w+)$""")]
    private static partial Regex Widening();

    /// `fptrunc float %a to bfloat`.
    [GeneratedRegex("""^fptrunc float (\S+) to bfloat$""")]
    private static partial Regex Narrowing();

    /// `fptosi bfloat %a to i32` and the other conversions to an integer.
    [GeneratedRegex("""^(fptosi|fptoui) bfloat (\S+) to (\w+)$""")]
    private static partial Regex ToInteger();

    /// `sitofp i32 %a to bfloat`: through a float, which holds every 24-bit integer and rounds a wider one once more.
    [GeneratedRegex("""^(sitofp|uitofp) (\w+) (\S+) to bfloat$""")]
    private static partial Regex FromInteger();

    /// A call of an LLVM intrinsic on bfloats, `call i32 @llvm.fptosi.sat.i32.bf16(bfloat %a)`.
    [GeneratedRegex("""^call (\w+) @llvm\.([\w.]+)\.(?:bf16|bfloat)\((.*)\)$""")]
    private static partial Regex Intrinsic();

    /// A bfloat constant written in hex, `0xR7F81`.
    [GeneratedRegex("""0xR([0-9A-Fa-f]{4})""")]
    private static partial Regex HexConstant();

    /// The bfloat type as a word of its own.
    [GeneratedRegex("""\bbfloat\b""")]
    private static partial Regex Bf16Type();

    /// The module with every bfloat an i16 of its bits, and every bfloat constant its bits as a number. Metadata lines
    /// and the text of string constants stay as they are.
    public static string AsBits(string module)
    {
        if (!module.Contains("bfloat", StringComparison.Ordinal)) return module;
        var lines = module.Split('\n');
        for (int i = 0; i < lines.Length; i++)
        {
            string line = lines[i];
            if (line.StartsWith('!') || !line.Contains("bfloat", StringComparison.Ordinal)) continue;
            // A string constant (c"...") keeps its text.
            int quote = line.IndexOf("c\"", StringComparison.Ordinal);
            string code = quote < 0 ? line : line[..quote];
            code = HexConstant().Replace(Bf16Type().Replace(code, "i16"),
                h => ((short)Convert.ToUInt16(h.Groups[1].Value, 16)).ToString(System.Globalization.CultureInfo.InvariantCulture));
            lines[i] = quote < 0 ? code : code + line[quote..];
        }
        return string.Join('\n', lines);
    }

    public static string Rewrite(string functions)
    {
        if (!functions.Contains("bfloat", StringComparison.Ordinal)) return functions;
        var lines = functions.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n');
        var o = new StringBuilder(functions.Length + 1024);
        int next = 0;
        for (int i = 0; i < lines.Length; i++)
        {
            string line = lines[i];
            var d = line.Contains("bfloat", StringComparison.Ordinal) ? Definition().Match(line) : Match.Empty;
            string? done = d.Success ? Lowered(d.Groups[1].Value, d.Groups[2].Value, d.Groups[3].Value, d.Groups[4].Value, ref next) : null;
            o.Append(done ?? line);
            if (i < lines.Length - 1) o.Append('\n');
        }
        return o.ToString();
    }

    /// The lines that do what `text` does with floats, or null when it needs no conversion.
    private static string? Lowered(string indent, string result, string text, string meta, ref int next)
    {
        var lines = new List<string>();
        int n = next;
        string Fresh() => $"%bf16.wasm.{n++}";
        string Widen(string operand, string? into = null)
        {
            string bits = Fresh(), wide = Fresh(), shifted = Fresh(), value = into ?? Fresh();
            lines.Add($"{bits} = bitcast bfloat {operand} to i16");
            lines.Add($"{wide} = zext i16 {bits} to i32");
            lines.Add($"{shifted} = shl i32 {wide}, 16");
            lines.Add($"{value} = bitcast i32 {shifted} to float");
            return value;
        }
        void Narrow(string value, string into)
        {
            string bits = Fresh(), low = Fresh(), odd = Fresh(), bias = Fresh(), rounded = Fresh(), top = Fresh();
            string nan = Fresh(), quiet = Fresh(), chosen = Fresh(), half = Fresh();
            lines.Add($"{bits} = bitcast float {value} to i32");
            lines.Add($"{low} = lshr i32 {bits}, 16");
            lines.Add($"{odd} = and i32 {low}, 1");
            lines.Add($"{bias} = add i32 {odd}, 32767");
            lines.Add($"{rounded} = add i32 {bits}, {bias}");
            lines.Add($"{top} = lshr i32 {rounded}, 16");
            lines.Add($"{nan} = fcmp uno float {value}, {value}");
            lines.Add($"{quiet} = or i32 {low}, 64");
            lines.Add($"{chosen} = select i1 {nan}, i32 {quiet}, i32 {top}");
            lines.Add($"{half} = trunc i32 {chosen} to i16");
            lines.Add($"{into} = bitcast i16 {half} to bfloat");
        }
        Match m;
        if ((m = Arithmetic().Match(text)).Success)
        {
            string a = Widen(m.Groups[3].Value), b = Widen(m.Groups[4].Value), r = Fresh();
            lines.Add($"{r} = {m.Groups[1].Value}{m.Groups[2].Value} float {a}, {b}");
            Narrow(r, result);
        }
        else if ((m = Negation().Match(text)).Success)
        {
            string bits = Fresh(), flipped = Fresh();
            lines.Add($"{bits} = bitcast bfloat {m.Groups[1].Value} to i16");
            lines.Add($"{flipped} = xor i16 {bits}, -32768");
            lines.Add($"{result} = bitcast i16 {flipped} to bfloat");
        }
        else if ((m = Comparison().Match(text)).Success)
        {
            string a = Widen(m.Groups[3].Value), b = Widen(m.Groups[4].Value);
            lines.Add($"{result} = fcmp{m.Groups[1].Value} {m.Groups[2].Value} float {a}, {b}");
        }
        else if ((m = Widening().Match(text)).Success)
        {
            // A widening to float is the widened value itself, so a signaling NaN stays one.
            if (m.Groups[2].Value == "float") Widen(m.Groups[1].Value, into: result);
            else lines.Add($"{result} = fpext float {Widen(m.Groups[1].Value)} to {m.Groups[2].Value}");
        }
        else if ((m = Narrowing().Match(text)).Success) Narrow(m.Groups[1].Value, result);
        else if ((m = ToInteger().Match(text)).Success)
            lines.Add($"{result} = {m.Groups[1].Value} float {Widen(m.Groups[2].Value)} to {m.Groups[3].Value}");
        else if ((m = FromInteger().Match(text)).Success)
        {
            string r = Fresh();
            lines.Add($"{r} = {m.Groups[1].Value} {m.Groups[2].Value} {m.Groups[3].Value} to float");
            Narrow(r, result);
        }
        else if ((m = Intrinsic().Match(text)).Success && m.Groups[2].Value is "fabs" or "copysign")
        {
            // The sign bit alone changes, so a NaN's payload stays as it is.
            var args = m.Groups[3].Value.Split(", ").Select(arg => arg["bfloat ".Length..]).ToList();
            string bits = Fresh(), kept = Fresh();
            lines.Add($"{bits} = bitcast bfloat {args[0]} to i16");
            lines.Add($"{kept} = and i16 {bits}, 32767");
            string made = kept;
            if (m.Groups[2].Value == "copysign")
            {
                string signBits = Fresh(), sign = Fresh(), both = Fresh();
                lines.Add($"{signBits} = bitcast bfloat {args[1]} to i16");
                lines.Add($"{sign} = and i16 {signBits}, -32768");
                lines.Add($"{both} = or i16 {kept}, {sign}");
                made = both;
            }
            lines.Add($"{result} = bitcast i16 {made} to bfloat");
        }
        else if ((m = Intrinsic().Match(text)).Success)
        {
            // Each bfloat argument widens, and a bfloat result narrows.
            var args = m.Groups[3].Value.Split(", ").Select(arg =>
                arg.StartsWith("bfloat ", StringComparison.Ordinal) ? "float " + Widen(arg["bfloat ".Length..]) : arg).ToList();
            string call = $"call {(m.Groups[1].Value == "bfloat" ? "float" : m.Groups[1].Value)} @llvm.{m.Groups[2].Value}.f32({string.Join(", ", args)})";
            if (m.Groups[1].Value == "bfloat")
            {
                string r = Fresh();
                lines.Add($"{r} = {call}");
                Narrow(r, result);
            }
            else lines.Add($"{result} = {call}");
        }
        else return null;
        next = n;
        // The source line's metadata stays on the line that makes the result.
        int last = lines.FindLastIndex(l => l.StartsWith(result + " = ", StringComparison.Ordinal));
        return string.Join("\n", lines.Select((l, i) => indent + l + (i == last ? meta : "")));
    }
}
