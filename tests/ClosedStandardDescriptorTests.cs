using System.Diagnostics;
using Xunit;

namespace Lapila.Tests;

/// <summary>
/// A program started with descriptor 0, 1 or 2 closed. On Linux and macOS <c>open</c> hands out the lowest free
/// descriptor, so without the program start's check the first file a program opens would become its standard output.
/// POSIX only: the tests start a shell that closes the descriptor and are left out on Windows.
/// </summary>
[Collection(WorkingDirectoryCollection.Name)]
public class ClosedStandardDescriptorTests
{
    /// Opens a file, writes "file", prints "console", then closes the file. The file must keep only "file".
    private const string Program = """
        import Hosted

        routine start() -> None
            target: &File <- File.at("OUT_PATH")
            OsFileManager.make_file(at: target, replacing: true)
            out: &FileHandle <- OsFileManager.open_write(at: target)
            out.write("file")
            Console.show("console")
            Console.alert("alert")
            out.close()
            return
        """;

    [Theory]
    [InlineData(">&-")]
    [InlineData("2>&-")]
    [InlineData("<&-")]
    [InlineData("<&- >&- 2>&-")]
    public void ClosedStandardDescriptorDoesNotBecomeTheFile(string redirect)
    {
        if (!(OperatingSystem.IsLinux() || OperatingSystem.IsMacOS())) return;
        string dir = Path.Combine(Path.GetTempPath(), "lapila_closed_fd_" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        try
        {
            string output = Path.Combine(dir, "out.txt");
            File.WriteAllText(Path.Combine(dir, "main.lpa"), Program.Replace("OUT_PATH", output));
            string lapila = Path.Combine(AppContext.BaseDirectory, "lapila.dll");
            var (buildCode, buildText) = Shell(dir, $"dotnet \"{lapila}\" build main.lpa");
            Assert.True(buildCode == 0, buildText);
            var (code, text) = Shell(dir, $"./main {redirect}");
            Assert.True(code == 0, text);
            Assert.Equal("file", File.ReadAllText(output));
        }
        finally
        {
            Directory.Delete(dir, recursive: true);
        }
    }

    /// Runs a command line in a POSIX shell and returns its exit code and the text it printed.
    private static (int Code, string Text) Shell(string dir, string command)
    {
        var info = new ProcessStartInfo("/bin/sh") { WorkingDirectory = dir, RedirectStandardOutput = true, RedirectStandardError = true };
        info.ArgumentList.Add("-c");
        info.ArgumentList.Add(command);
        using var process = Process.Start(info)!;
        string stdout = process.StandardOutput.ReadToEnd();
        string stderr = process.StandardError.ReadToEnd();
        process.WaitForExit();
        return (process.ExitCode, stdout + stderr);
    }
}
