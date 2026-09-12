namespace StrataLint.Tests;

public sealed partial class NativeSharedLakeCacheTests
{
    private const string RepairScenarios = """
if scenario == 'hardlinks':
    command(main, 'warm-cache')
    before = snapshot(shared_root)
    hit = build(reader)
    assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
    unchanged(shared_root, before)
    artifact = next((shared / 'artifacts').glob('*.olean'))
    private = reader / '.lake/build/lib/lean/Fixture.olean'
    # Inject stale topology explicitly; fresh native reads above never make this alias.
    private.unlink()
    os.link(artifact, private)
    before = snapshot(shared_root)
    result = command(reader, 'with-cache-reader', '--', 'lake', 'clean', expected=None)
    after = snapshot(shared_root)
    changes = [p for p in before.keys() | after.keys() if before.get(p) != after.get(p)]
    records.append(dict(stale_hardlink_injected=True, supported_action='lake clean',
        exit=result.returncode, changed=changes, private_alias_exists=private.exists()))
    print(json.dumps(records[-1]))
    assert result.returncode == 2 and 'hardlink' in result.stderr, result
    unchanged(shared_root, before)
    assert private.exists() and private.stat().st_nlink == 2
    # Maintenance belongs to the fixture owner, outside the reader boundary.
    private.unlink()
    before = snapshot(shared_root)
    command(reader, 'with-cache-reader', '--', 'lake', 'clean')
    hit = build(reader)
    assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
    unchanged(shared_root, before)
    # An alias outside the active partition is equally unsafe for private commands.
    inactive = shared_root / 'inactive'
    inactive.mkdir()
    (inactive / 'blob').write_text('inactive artifact')
    os.link(inactive / 'blob', reader / '.lake/stale')
    before = snapshot(shared_root)
    assert 'hardlink' in command(reader, 'ensure-cache', expected=2).stderr
    unchanged(shared_root, before)
elif scenario == 'traces':
    command(main, 'warm-cache')
    trace_directory = shared_root / 'diagnostics'
    trace_directory.mkdir()
    destinations = ['GIT_TRACE', 'GIT_TRACE_SETUP', 'GIT_TRACE_PERFORMANCE',
        'GIT_TRACE2', 'GIT_TRACE2_EVENT', 'GIT_TRACE2_PERF']
    for verb in ['ensure-cache', 'with-cache-reader', 'warm-cache']:
        for name in destinations + ['config:trace2.normalTarget', 'config:trace2.eventTarget', 'config:trace2.perfTarget']:
            for preexisting in [False, True]:
                trace = trace_directory / 'trace'
                if preexisting: trace.write_text('existing diagnostic\n')
                elif trace.exists(): trace.unlink()
                extra = {}
                if name.startswith('config:'):
                    git(main, 'config', name[7:], str(trace))
                else:
                    extra[name] = str(trace)
                before = snapshot(shared_root)
                try:
                    args = ['--', '/usr/bin/true'] if verb == 'with-cache-reader' else []
                    result = command(reader, verb, *args, extra=extra, expected=2 if verb == 'warm-cache' else 0)
                    after = snapshot(shared_root)
                    changes = [p for p in before.keys() | after.keys() if before.get(p) != after.get(p)]
                    print(json.dumps(dict(trace=name, verb=verb, preexisting=preexisting, exit=result.returncode, changed=changes)))
                    unchanged(shared_root, before)
                finally:
                    if name.startswith('config:'): git(main, 'config', '--unset', name[7:])
    keys = ['GIT_SSH_COMMAND', 'GIT_ASKPASS', 'SSH_AUTH_SOCK', 'GIT_TERMINAL_PROMPT', 'GIT_OPTIONAL_LOCKS']
    values = dict(zip(keys, ['ssh -o BatchMode=yes', '/fixture/askpass', '/fixture/agent', '0', '0']))
    probe = 'import os,json; print(json.dumps({k:os.environ.get(k) for k in ' + repr(keys) + '}))'
    result = command(reader, 'with-cache-reader', '--', sys.executable, '-c', probe, extra=values)
    assert json.loads(result.stdout.splitlines()[-1]) == values
elif scenario == 'dependencies':
    dependency = P / 'dependency'
    dependency.mkdir()
    git(dependency, 'init', '-b', 'dev')
    git(dependency, 'config', 'user.email', 'fixture@example.invalid')
    git(dependency, 'config', 'user.name', 'Fixture')
    (dependency / 'lakefile.toml').write_text('name = "dependency"\n')
    (dependency / 'Dependency.lean').write_text('def dependencyAnswer : Nat := 7\n')
    git(dependency, 'add', '.')
    git(dependency, 'commit', '-m', 'genuine Git dependency')
    rev = git(dependency, 'rev-parse', 'HEAD')
    with (main / 'lakefile.toml').open('a') as f:
        f.write('\n[[require]]\nname = "dependency"\ngit = ' + json.dumps(str(dependency)) + '\nrev = "' + rev + '"\n')
    run([lake, 'update'], main)
    commit()
    command(main, 'warm-cache')
    target = fresh('dependency-reader')
    command(target, 'ensure-cache')
    stamp = target / '.lake/.stratalint-lean-cache-stamp.json'
    saved_stamp = stamp.read_bytes()
    package = target / '.lake/packages/dependency'
    assert git(package, 'rev-parse', 'HEAD') == rev
    output = target / '.lake/build/unrelated.olean'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('unrelated private output')
    saved_output = snapshot(output.parent)
    shutil.rmtree(package)
    before = snapshot(shared_root)
    result = command(target, 'ensure-cache')
    print(json.dumps(dict(standalone_exit=result.returncode, source_restored=package.exists(), stamp_retained=stamp.read_bytes() == saved_stamp)))
    assert package.exists(), 'matching stamp suppressed live materialization'
    assert git(package, 'rev-parse', 'HEAD') == rev
    assert stamp.read_bytes() == saved_stamp
    assert snapshot(output.parent) == saved_output
    unchanged(shared_root, before)
    shutil.rmtree(package)
    dependency.rename(P / 'dependency-unavailable')
    failed = command(target, 'ensure-cache', expected=2)
    assert 'Lake dependency materialization failed' in failed.stderr
    assert snapshot(output.parent) == saved_output
    unchanged(shared_root, before)
elif scenario == 'stale-session':
    command(reader, 'ensure-cache')
    lock = next((main / '.git/stratalint-lake-locks').glob('*.lock'))
    unrelated = subprocess.Popen(['/bin/sleep', '120'], start_new_session=True, env=ENV)
    try:
        # Deterministic stale-record fixture, not a forced kernel PID wrap.
        lock.write_text(str(unrelated.pid) + '\n')
        result = command(reader, 'ensure-cache', expected=None)
        print(json.dumps(dict(numeric_stale_record=True, unrelated_pid=unrelated.pid, exit=result.returncode)))
        # Old identity-free records must fail truthfully, not masquerade as live writers.
        assert result.returncode == 2 and 'identity' in result.stderr
        lock.write_text('')
        # Obtain a real reservation, then simulate numeric ID reuse after its writer exits.
        reservation = P / 'reservation'
        probe = 'import pathlib; pathlib.Path(' + repr(str(reservation)) + ').write_bytes(pathlib.Path(' + repr(str(lock)) + ').read_bytes())'
        command(reader, 'with-cache-reader', '--', sys.executable, '-c', probe)
        record = reservation.read_text().split()
        assert len(record) == 2
        record[0] = str(unrelated.pid)
        lock.write_text(' '.join(record) + '\n')
        command(reader, 'ensure-cache')
        assert unrelated.poll() is None
        # Same stale session number with an old boot identity is also recoverable.
        identity = record[1].split(':')
        identity[0] = '00000000-0000-0000-0000-000000000000'
        lock.write_text(record[0] + ' ' + ':'.join(identity) + '\n')
        command(reader, 'ensure-cache')
        assert unrelated.poll() is None
        records.append(dict(simulated_pid_reuse=True, stale_boot=True, recovered=True, unrelated_still_live=True))
    finally:
        unrelated.kill()
        unrelated.wait(timeout=10)
""";
}
