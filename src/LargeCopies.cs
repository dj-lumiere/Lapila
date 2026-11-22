using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace Lapila;

/// Moves a large record or array from one place to another with one memcpy instead of as a value.
///
/// LLVM splits a load or store of an aggregate value into one instruction per element. A record of a hundred
/// thousand places copied as a value becomes a hundred thousand loads and stores, and the backend can run out of
/// memory turning that into machine code. This rewrites a finished routine's IR in two shapes:
/// - a large value loaded and stored once somewhere else becomes a memcpy between the two places,
/// - a large record put together with `insertvalue` and stored once is written field by field into the place.
public static class LargeCopies
{
    /// Records and arrays at least this many bytes long are copied in memory.
    public const long Threshold = 256;

    private static readonly Regex Name = new(@"^\s*(%[^\s=,()]+) = ", RegexOptions.Compiled);

    private sealed class Line(string text)
    {
        public string Text = text;
        public bool Removed;
    }

    /// Rewrites the routine at `text` (from `define` to the closing brace). `sizes` maps a large type's LLVM spelling
    /// to its size in bytes. Returns the text unchanged when nothing applies.
    public static string Rewrite(string text, IReadOnlyDictionary<string, long> sizes, Action declareMemcpy)
    {
        if (sizes.Count == 0) return text;
        bool any = false;
        foreach (var key in sizes.Keys)
            if (text.Contains($"load {key}, ptr ", StringComparison.Ordinal) || text.Contains($"insertvalue {key} ", StringComparison.Ordinal))
            {
                any = true;
                break;
            }
        if (!any) return text;

        var lines = text.Split('\n').Select(l => new Line(l)).ToList();
        var defs = new Dictionary<string, int>(StringComparer.Ordinal);
        for (int i = 0; i < lines.Count; i++)
            if (Name.Match(lines[i].Text) is { Success: true } m) defs[m.Groups[1].Value] = i;

        int fresh = 0;
        bool changed = false;
        for (int j = 0; j < lines.Count; j++)
        {
            var store = ParseStore(lines[j].Text, sizes);
            if (store is null) continue;
            var (type, value, place, tail) = store.Value;
            if (!defs.TryGetValue(value, out int d) || Uses(lines, value) != 1) continue;
            var replacement = new List<string>();
            string indent = Indent(lines[j].Text);

            if (ParseLoad(lines[d].Text, type) is { } from && d < j && WritesNothingBetween(lines, d, j))
            {
                replacement.Add($"{indent}call void @llvm.memcpy.p0.p0.i64(ptr {place}, ptr {from}, i64 {Size(sizes, type)}, i1 false){tail}");
                lines[d].Removed = true;
            }
            else if (Chain(lines, defs, value, type) is { } chain)
            {
                // Every field is written where the record was stored. A large field that was loaded just for this is
                // copied from its place, before the other fields, while that place still holds what was loaded.
                var large = new List<string>();
                var small = new List<string>();
                foreach (var (index, fieldType, fieldValue) in chain.Fields)
                {
                    string at = $"%large.copy.{fresh++}";
                    string gep = $"{indent}{at} = getelementptr inbounds {type}, ptr {place}, i32 0, {GepIndices(index)}";
                    if (sizes.ContainsKey(fieldType) && defs.TryGetValue(fieldValue, out int fd) && fd < j
                        && Uses(lines, fieldValue) == 1 && ParseLoad(lines[fd].Text, fieldType) is { } fieldFrom
                        && WritesNothingBetween(lines, fd, j))
                    {
                        large.Add(gep);
                        large.Add($"{indent}call void @llvm.memcpy.p0.p0.i64(ptr {at}, ptr {fieldFrom}, i64 {Size(sizes, fieldType)}, i1 false){tail}");
                        lines[fd].Removed = true;
                    }
                    else
                    {
                        small.Add(gep);
                        small.Add($"{indent}store {fieldType} {fieldValue}, ptr {at}{tail}");
                    }
                }
                replacement.AddRange(large);
                replacement.AddRange(small);
                foreach (int k in chain.Lines) lines[k].Removed = true;
            }
            else continue;

            lines[j].Text = string.Join("\n", replacement);
            changed = true;
        }
        if (!changed) return text;
        declareMemcpy();
        var sb = new StringBuilder(text.Length);
        for (int i = 0; i < lines.Count; i++)
        {
            if (lines[i].Removed) continue;
            sb.Append(lines[i].Text);
            if (i < lines.Count - 1) sb.Append('\n');
        }
        return sb.ToString();
    }

    private static string Indent(string line) => line[..(line.Length - line.TrimStart().Length)];

    private static string Size(IReadOnlyDictionary<string, long> sizes, string type) =>
        sizes[type].ToString(CultureInfo.InvariantCulture);

    private static string GepIndices(string index) =>
        string.Join(", ", index.Split(',').Select(i => $"i32 {i.Trim()}"));

    /// `store T %v, ptr %q[, align n][, !dbg !k]` with T large: the type, the value, the place and what follows it.
    private static (string Type, string Value, string Place, string Tail)? ParseStore(string line, IReadOnlyDictionary<string, long> sizes)
    {
        string s = line.TrimStart();
        if (!s.StartsWith("store ", StringComparison.Ordinal)) return null;
        foreach (var type in sizes.Keys)
        {
            string head = $"store {type} ";
            if (!s.StartsWith(head, StringComparison.Ordinal)) continue;
            string rest = s[head.Length..];
            int comma = rest.IndexOf(", ptr ", StringComparison.Ordinal);
            if (comma < 0) return null;
            string value = rest[..comma];
            if (!value.StartsWith('%')) return null;
            string after = rest[(comma + ", ptr ".Length)..];
            int end = after.IndexOf(',');
            string place = end < 0 ? after : after[..end];
            return (type, value, place.Trim(), DebugTail(after));
        }
        return null;
    }

    /// The place `%p` of `%v = load T, ptr %p[, ...]`, or null.
    private static string? ParseLoad(string line, string type)
    {
        int eq = line.IndexOf(" = ", StringComparison.Ordinal);
        if (eq < 0) return null;
        string head = $"load {type}, ptr ";
        string rest = line[(eq + 3)..];
        if (!rest.StartsWith(head, StringComparison.Ordinal)) return null;
        string after = rest[head.Length..];
        int end = after.IndexOf(',');
        return (end < 0 ? after : after[..end]).Trim();
    }

    /// The `, !dbg !n` a line ends with, kept on its replacement.
    private static string DebugTail(string s)
    {
        int at = s.IndexOf(", !dbg ", StringComparison.Ordinal);
        return at < 0 ? "" : s[at..];
    }

    /// The fields an `insertvalue` chain ending in `value` writes, when it starts from `poison` or `undef` and each
    /// step is used only by the next.
    private static (List<(string Index, string Type, string Value)> Fields, List<int> Lines)? Chain(
        List<Line> lines, Dictionary<string, int> defs, string value, string type)
    {
        var fields = new List<(string, string, string)>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var used = new List<int>();
        string current = value;
        while (true)
        {
            if (!defs.TryGetValue(current, out int d)) return null;
            string line = lines[d].Text;
            string head = $"insertvalue {type} ";
            int eq = line.IndexOf(" = ", StringComparison.Ordinal);
            string rest = line[(eq + 3)..];
            if (!rest.StartsWith(head, StringComparison.Ordinal)) return null;
            rest = rest[head.Length..];
            int dbg = rest.IndexOf(", !dbg ", StringComparison.Ordinal);
            if (dbg >= 0) rest = rest[..dbg];
            int comma = rest.IndexOf(", ", StringComparison.Ordinal);
            if (comma < 0) return null;
            string from = rest[..comma];
            string field = rest[(comma + 2)..];
            // The field part is `FT %f, i[, j]`: the type may hold spaces, the indices are the trailing numbers.
            var m = Regex.Match(field, @"^(.*) (\S+), ([0-9]+(?:, [0-9]+)*)$");
            if (!m.Success) return null;
            used.Add(d);
            if (seen.Add(m.Groups[3].Value)) fields.Add((m.Groups[3].Value, m.Groups[1].Value, m.Groups[2].Value));
            if (from is "poison" or "undef") break;
            if (!from.StartsWith('%') || Uses(lines, from) != 1) return null;
            current = from;
        }
        fields.Reverse();
        return (fields, used);
    }

    /// Whether no line from `from` to `to` (exclusive) can write memory or leave the block.
    private static bool WritesNothingBetween(List<Line> lines, int from, int to)
    {
        for (int k = from + 1; k < to; k++)
        {
            if (lines[k].Removed) continue;
            string s = lines[k].Text.TrimStart();
            int eq = s.IndexOf(" = ", StringComparison.Ordinal);
            string op = eq >= 0 && s.StartsWith('%') ? s[(eq + 3)..] : s;
            if (s.Length == 0) return false;
            if (s.EndsWith(':')) return false;
            if (op.StartsWith("store ", StringComparison.Ordinal) || op.StartsWith("call ", StringComparison.Ordinal)
                || op.StartsWith("tail call ", StringComparison.Ordinal) || op.StartsWith("invoke ", StringComparison.Ordinal)
                || op.StartsWith("atomicrmw ", StringComparison.Ordinal) || op.StartsWith("cmpxchg ", StringComparison.Ordinal)
                || op.StartsWith("fence", StringComparison.Ordinal) || op.StartsWith("br ", StringComparison.Ordinal)
                || op.StartsWith("ret", StringComparison.Ordinal) || op.StartsWith("switch ", StringComparison.Ordinal)
                || op.StartsWith("unreachable", StringComparison.Ordinal) || op.StartsWith("load volatile", StringComparison.Ordinal))
                return false;
        }
        return true;
    }

    /// How many times `name` appears as an operand in the routine (its definition not counted).
    private static int Uses(List<Line> lines, string name)
    {
        var pattern = new Regex($@"(?<![\w.$""%-]){Regex.Escape(name)}(?![\w.$-])");
        int count = 0;
        foreach (var line in lines)
        {
            if (line.Removed) continue;
            var m = Name.Match(line.Text);
            int start = m.Success && m.Groups[1].Value == name ? m.Length : 0;
            count += pattern.Matches(line.Text[start..]).Count;
            if (count > 1) return count;
        }
        return count;
    }
}
