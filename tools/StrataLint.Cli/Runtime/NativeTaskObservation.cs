using System.Globalization;
using System.Text.Json;

namespace StrataLint.Cli;

// Disposable observation only. Never read child output or change runner policy.
internal static class NativeTaskObservation
{
    internal enum Phase { Ensure, DependencyCacheGet, ArchiveFetch, NativeCommand }

    internal static T Run<T>(Phase phase, Func<T> action, Func<T, int> exitStatus)
    {
        if (Environment.GetEnvironmentVariable("STRATALINT_NATIVE_TASK_OBSERVATION") != "1")
            return action();

        Emit(phase, "begin", null);
        T result;
        try { result = action(); }
        catch
        {
            Emit(phase, "aborted", null);
            throw;
        }
        // A return describes this call only, never the outer shell or CI job.
        Emit(phase, "returned", exitStatus(result));
        return result;
    }

    private static void Emit(Phase phase, string eventName, int? status)
    {
        try
        {
            var birth = "UNAVAILABLE";
            var parent = "UNAVAILABLE";
            if (OperatingSystem.IsLinux())
            {
                try
                {
                    var stat = File.ReadAllText("/proc/self/stat");
                    var fields = stat[(stat.LastIndexOf(')') + 2)..].Split(' ');
                    if (fields.Length > 19
                        && ulong.TryParse(fields[19], NumberStyles.None, CultureInfo.InvariantCulture, out _)
                        && int.TryParse(fields[1], NumberStyles.None, CultureInfo.InvariantCulture, out _))
                    {
                        birth = fields[19];
                        parent = fields[1];
                    }
                }
                catch (Exception exception) when (exception is IOException
                    or UnauthorizedAccessException or ArgumentException) { }
            }
            Console.Error.WriteLine("NATIVE_TASK_PHASE " + JsonSerializer.Serialize(new
            {
                schema = 1,
                phase = phase switch
                {
                    Phase.Ensure => "ensure",
                    Phase.DependencyCacheGet => "dependency-cache-get",
                    Phase.ArchiveFetch => "archive-fetch",
                    _ => "native-command",
                },
                @event = eventName,
                pid = Environment.ProcessId,
                birth_ticks = birth,
                ppid = parent,
                utc = TimeProvider.System.GetUtcNow().ToString("O", CultureInfo.InvariantCulture),
                monotonic_ticks = TimeProvider.System.GetTimestamp(),
                monotonic_frequency = TimeProvider.System.TimestampFrequency,
                status,
            }));
            Console.Error.Flush();
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException or ArgumentException)
        {
            // Observation failure cannot replace the command's status/exception.
        }
    }
}
