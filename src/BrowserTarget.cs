namespace Lapila;

/// What clang answers for WebAssembly under WASI (LLVM 22, the triple's default CPU), for the builder running in a
/// browser page: no process can be started there, so the questions DataLayout and CpuModel put to clang get these
/// answers instead. A build anywhere else still asks clang.
internal static class BrowserTarget
{
    /// The data layout clang prints for wasm32-unknown-wasip1.
    internal const string WasiLayout = "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-i128:128-n32:64-S128-ni:1:10:20";

    /// The routine attributes clang gives wasm32-unknown-wasip1's default CPU, as its IR prints them.
    internal const string WasiCpuIr = "target datalayout = \"" + WasiLayout + "\"\n" +
        "attributes #0 = { \"target-cpu\"=\"generic\" \"target-features\"=\"+bulk-memory,+bulk-memory-opt," +
        "+call-indirect-overlong,+multivalue,+mutable-globals,+nontrapping-fptoint,+reference-types,+sign-ext\" }\n";

    /// Whether the builder runs in a browser page.
    internal static bool Active => OperatingSystem.IsBrowser();

    /// The data layout of the LLVM triple, null for a triple other than WASI's.
    internal static string? Layout(string llvmTriple) => llvmTriple.EndsWith("-" + BuildTarget.WasiOs, StringComparison.Ordinal)
        ? WasiLayout
        : null;

    /// The message of a question only clang can answer.
    internal static string NeedsClang(string question) =>
        $"the builder in a browser page knows {question} only for {BuildTarget.WasiTriple} with its default CPU and features";
}
