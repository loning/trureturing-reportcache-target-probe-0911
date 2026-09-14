"""Behavioral Linux proc fixtures; no workflow-text assertions or repo builds.

STRATALINT_NATIVE_TMPDIR optionally selects the external fixture directory.
"""
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('observer', ROOT / 'tools/scripts/lib/native-task-observation.py')
observer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(observer)


class NativeObservationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ.get('STRATALINT_NATIVE_TMPDIR'))
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / 'repository with spaces λ'
        self.root.mkdir()
        self.proc = self.root / 'proc'
        for pid, parent, birth, exe in ((100, 50, 1000, 'lean'), (50, 1, 500, 'lake')):
            directory = self.proc / str(pid)
            directory.mkdir(parents=True)
            self.stat(pid, parent, birth)
            (directory / 'exe').symlink_to('/toolchain/bin/' + exe)
            (directory / 'cwd').symlink_to(self.root)
        self.tail = 'D5/Δοκιμή'
        self.source = self.root / (self.tail + '.lean')
        self.setup = self.root / ('.lake/build/ir/' + self.tail + '.setup.json')
        self.output = self.root / ('.lake/build/lib/lean/' + self.tail + '.olean')
        for p in (self.source, self.setup, self.output):
            p.parent.mkdir(parents=True, exist_ok=True)
        self.source.write_bytes(b'def value : Nat := 1\n')
        self.setup.write_text(json.dumps({'name': self.tail.replace('/', '.')}))
        self.argv = ['/toolchain/bin/lean', '-DmaxRecDepth=1024', str(self.source),
                     '-o', str(self.output), '--setup', str(self.setup), '--json']
        self.command()

    def stat(self, pid, parent, birth, rss=7):
        fields = ['S', str(parent)] + ['0'] * 17 + [str(birth), '0', str(rss)]
        (self.proc / str(pid) / 'stat').write_text(str(pid) + ' (name with ) space) ' + ' '.join(fields))

    def command(self, argv=None):
        data = ('\0'.join(argv or self.argv) + '\0').encode()
        (self.proc / '100/cmdline').write_bytes(data)
        return data

    def annotation(self):
        return observer.annotate(self.proc, self.root, 100, 50)

    def assert_failure(self, record, stage, reason):
        self.assertIn({'stage': stage, 'reason': reason}, record['diagnostic']['failures'])
        self.assertEqual('unavailable', record['identity_status'])

    def test_exact_full_identity_and_unicode_spaced_paths(self):
        record = self.annotation()
        self.assertEqual('native-file', record['identity_status'])
        self.assertEqual('D5.Δοκιμή', record['module'])
        self.assertEqual(self.tail + '.lean', record['file'])
        self.assertEqual(hashlib.sha256(self.source.read_bytes()).hexdigest(), record['source_sha256_at_sample'])
        self.assertEqual('operand-only', record['diagnostic']['operand_status'])
        self.assertEqual('stable', record['diagnostic']['stability'])
        self.assertEqual('UNAVAILABLE', record['facet'])

    def test_old_ps_rss_is_not_attributed_after_pid_reuse(self):
        # Resource capture precedes the first annotation stat; the same live
        # Lake parent then has a different Lean child at this reused PID.
        self.stat(100, 50, 1000, rss=900000 * 1024 // os.sysconf('SC_PAGE_SIZE'))
        old_tree = 'pid:100,ppid:50,rss_kb:900000'
        self.stat(100, 50, 1001, rss=3)
        self.source = self.root / 'D5/New.lean'
        self.setup = self.root / '.lake/build/ir/D5/New.setup.json'
        self.output = self.root / '.lake/build/lib/lean/D5/New.olean'
        self.source.write_text('def replacement := 2\n')
        self.setup.write_text('{"name":"D5.New"}')
        self.argv = ['/toolchain/bin/lean', str(self.source), '-o', str(self.output),
                     '--setup', str(self.setup), '--json']
        self.command()
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'tools/scripts/lib/native-task-observation.py'),
            '--repository', str(self.root), '--proc-root', str(self.proc), '--sample-id', 'a' * 32],
            input=old_tree, capture_output=True, text=True, timeout=30)
        self.assertEqual(0, result.returncode, result.stderr)
        record = json.loads(result.stdout.split(' ', 1)[1])
        self.assertEqual('unverified', record['resource_tree_rss_association'])
        self.assertEqual('D5.New', record['module'])
        self.assertEqual(1001, record['birth_ticks'])
        self.assertEqual('process-lifetime', record['memory']['association'])
        self.assertEqual(3 * os.sysconf('SC_PAGE_SIZE'), record['memory']['rss_bytes'])
        self.assertNotEqual(900000 * 1024, record['memory']['rss_bytes'])

    def test_stat_memory_is_independent_and_fails_closed(self):
        with patch.object(observer.time, 'time_ns', side_effect=[100, 200, 300]):
            stable = self.annotation()
        self.assertEqual('proc-stat-rss', stable['memory']['kind'])
        self.assertEqual(7, stable['memory']['rss_pages'])
        self.assertEqual((200, 300), (stable['memory']['read_started_utc_epoch_ns'], stable['memory']['read_finished_utc_epoch_ns']))
        original = observer.read_bounded
        def changing_rss(path, limit, measurement=None):
            data = original(path, limit, measurement)
            if path == self.proc / '100/stat':
                self.stat(100, 50, 1000, rss=11)
            return data
        with patch.object(observer, 'read_bounded', changing_rss):
            record = self.annotation()
        self.assertEqual(11, record['memory']['rss_pages'])
        for value in ('invalid', -1, 2 ** 64):
            self.stat(100, 50, 1000, rss=value)
            record = self.annotation()
            self.assertEqual('native-file', record['identity_status'])
            self.assertEqual('unavailable', record['memory']['association'])
            self.assertNotIn('rss_bytes', record['memory'])
        path = self.proc / '100/stat'
        path.write_text(path.read_text().rsplit(' ', 2)[0])
        self.assertEqual('native-file', self.annotation()['identity_status'])
        self.assertEqual('unavailable', self.annotation()['memory']['association'])

    def test_entropy_exception_is_contained_and_command_status_preserved(self):
        script = r'''
source "$1/tools/scripts/lib/resource-observation-lib.sh"
resource_observation_process_values() { printf '1\t2\tpid:100,ppid:50,rss_kb:456\n'; }
resource_observation_cgroup_path() { printf 'UNAVAILABLE'; }
resource_observation_cgroup_root() { printf 'UNAVAILABLE'; }
resource_observation_mount_values() { printf 'mount\t100\t200\n'; }
source "$1/tools/scripts/lib/native-task-observation.sh" "$1" "$3"
observation_python="$2"
python3() {
  "$observation_python" -B -c 'import errno, os, sys, uuid
from unittest.mock import patch
with patch.object(os, "urandom", side_effect=OSError(errno.EIO, "QUALITY_ENTROPY_IO_ERROR")):
    exec(sys.argv[1])' "$2"
}
resource_observe_run_periodic /bin/bash -c 'exit 37'
'''
        result = subprocess.run(['/bin/bash', '--noprofile', '--norc', '-c', script,
            'entropy', str(ROOT), sys.executable, str(self.proc)], cwd=self.root,
            capture_output=True, text=True, timeout=30)
        self.assertEqual(37, result.returncode, result.stderr)
        resources = [dict(word.split('=', 1) for word in x.split()[1:]) for x in result.stdout.splitlines() if x.startswith('RESOURCE_SAMPLE ')]
        self.assertEqual('37', resources[-1]['command_exit_status'])
        self.assertTrue(all('rss_kb:456' in x['process_tree'] and 'sample_id' not in x for x in resources))
        lines = result.stderr.splitlines()
        self.assertTrue(lines)
        for line in lines:
            self.assertLessEqual(len((line + '\n').encode()), 4096)
            self.assertTrue(line.startswith('NATIVE_TASK_SAMPLE '), line)
            record = json.loads(line.split(' ', 1)[1])
            self.assertEqual([{'stage': 'sample-id', 'reason': 'unavailable'}], record['diagnostic']['failures'])

    def test_setup_source_exact_limits(self):
        original = self.setup.read_bytes()
        for size in (2097151, 2097152, 2097153):
            with self.subTest(setup_size=size):
                self.setup.write_bytes(original + b' ' * (size - len(original)))
                record = self.annotation()
                self.assertEqual('native-file' if size <= 2097152 else 'unavailable', record['identity_status'])
                self.assertEqual('operand-only', record['diagnostic']['operand_status'])
                self.assertEqual(hashlib.sha256(self.source.read_bytes()).hexdigest(), record['diagnostic']['source_sha256_at_sample'])
                if size > 2097152:
                    self.assert_failure(record, 'setup-read', 'limit-exceeded')
                    self.assertEqual(size, record['diagnostic']['reads']['setup-read']['stat_size_bytes'])
                    self.assertEqual('lower-bound', record['diagnostic']['reads']['setup-read']['length_kind'])
        self.setup.write_bytes(original)
        for size in (16777215, 16777216, 16777217):
            with self.subTest(source_size=size):
                self.source.write_bytes(b'x' * size)
                record = self.annotation()
                self.assertEqual('native-file' if size <= 16777216 else 'unavailable', record['identity_status'])
                self.assertEqual('operand-only', record['diagnostic']['operand_status'])
                if size > 16777216:
                    self.assert_failure(record, 'source-read', 'limit-exceeded')
                    self.assertNotIn('source_sha256_at_sample', record['diagnostic'])

    def test_cmdline_boundaries_nul_and_encoding(self):
        for size in (65535, 65536, 65537):
            words = list(self.argv)
            words.insert(1, '-D')
            current = len(('\0'.join(words) + '\0').encode())
            words[1] += 'x' * (size - current)
            data = self.command(words)
            self.assertEqual(size, len(data))
            record = self.annotation()
            if size <= 65536:
                self.assertEqual('native-file', record['identity_status'])
                self.assertTrue(record['diagnostic']['reads']['cmdline-before']['nul_complete'])
            else:
                self.assert_failure(record, 'cmdline-before', 'limit-exceeded')
                self.assertEqual('UNAVAILABLE', record['diagnostic']['reads']['cmdline-before']['nul_complete'])
        for data, reason in ((self.command()[:-1], 'nul-incomplete'), (b'\xff\0', 'invalid-utf8')):
            (self.proc / '100/cmdline').write_bytes(data)
            self.assert_failure(self.annotation(), 'cmdline-before', reason)

    def test_rejected_invocations_and_paths(self):
        cases = []
        def change(index, value):
            words = list(self.argv); words[index] = value; return words
        cases.extend([(change(1, '--unsupported'), 'unsupported-prefix'),
                      (change(-1, '--server'), 'unsupported-suffix'),
                      (change(3, '-i'), 'missing-output'),
                      (change(2, str(self.root.parent / 'outside.lean')), 'outside-repository'),
                      (change(2, str(self.root / 'Wrong.lean')), 'source-tail-mismatch'),
                      (change(4, str(self.root / 'Wrong.olean')), 'output-path-shape'),
                      (change(-2, str(self.root / '.lake/build/ir/Wrong.setup.json')), 'setup-tail-mismatch')])
        words = list(self.argv); words[5:5] = ['-o', str(self.output)]
        cases.append((words, 'duplicate-output'))
        for words, reason in cases:
            with self.subTest(reason=reason):
                self.command(words)
                record = self.annotation()
                self.assert_failure(record, 'operands', reason)
                self.assertNotIn('operands', record['diagnostic'])
        self.command()
        for data, reason in ((b'{', 'invalid-json'), (b'{}', 'invalid-module-name'),
                             (b'{"name":"Wrong"}', 'module-tail-mismatch')):
            self.setup.write_bytes(data)
            record = self.annotation()
            self.assert_failure(record, 'setup-name', reason)
            self.assertEqual('operand-only', record['diagnostic']['operand_status'])

    def test_access_errno_and_no_error_text(self):
        original = Path.open
        for target in (self.source, self.setup, self.proc / '100/cmdline', self.proc / '100/stat'):
            for number in (errno.EACCES, errno.ENOENT):
                def inaccessible(path, *args, **kwargs):
                    if path == target:
                        raise OSError(number, 'SECRET arbitrary error text', str(target))
                    return original(path, *args, **kwargs)
                with patch.object(Path, 'open', inaccessible):
                    record = self.annotation()
                self.assertTrue(any(f.get('errno') == number for f in record['diagnostic']['failures']))
                self.assertNotIn('SECRET', json.dumps(record))
                self.assertEqual('unavailable', record['identity_status'])

    def test_process_parent_cwd_cmdline_and_file_races(self):
        original = observer.read_bounded
        cases = ['process', 'parent', 'cwd', 'cmdline', 'executable', 'parent-executable', 'source', 'setup']
        for case in cases:
            with self.subTest(case=case):
                # Run each race in an independent fixture.
                fixture = NativeObservationTests(); fixture.setUp()
                try:
                    changed = False
                    def changing(path, limit, measurement=None):
                        nonlocal changed
                        data = original(path, limit, measurement)
                        if path == fixture.source and not changed:
                            changed = True
                            if case == 'process': fixture.stat(100, 50, 1001)
                            elif case == 'parent': fixture.stat(50, 1, 501)
                            elif case in ('source', 'setup'): path_to_change = getattr(fixture, case); path_to_change.write_bytes(b'changed')
                            elif case == 'cmdline': fixture.command(['/other'])
                            else:
                                link = fixture.proc / ('50' if case == 'parent-executable' else '100') / ('cwd' if case == 'cwd' else 'exe')
                                link.unlink(); link.symlink_to('/changed')
                        return data
                    with patch.object(observer, 'read_bounded', changing):
                        record = fixture.annotation()
                    self.assertEqual('unavailable', record['identity_status'])
                    self.assertNotIn('source_sha256_at_sample', record['diagnostic'])
                    # A changed source read can preserve stable operand association,
                    # but its bytes must not become a certified observation hash.
                    if case != 'source':
                        self.assertEqual('unverified', record['diagnostic']['stability'])
                        self.assertNotIn('operands', record['diagnostic'])
                        self.assertEqual('unavailable', record['memory']['association'])
                        self.assertNotIn('rss_bytes', record['memory'])
                finally:
                    fixture.doCleanups()

    def test_sampled_parent_and_toolchain_mismatch(self):
        record = observer.annotate(self.proc, self.root, 100, 51)
        self.assert_failure(record, 'process-before', 'sampled-parent-mismatch')
        link = self.proc / '50/exe'; link.unlink(); link.symlink_to('/different/bin/lake')
        self.assert_failure(self.annotation(), 'parent-executable-before', 'parent-toolchain-mismatch')

    def test_changed_during_read_is_measured_without_hash(self):
        original = Path.open
        for target, stage in ((self.source, 'source-read'), (self.setup, 'setup-read'),
                              (self.proc / '100/cmdline', 'cmdline-before')):
            data = target.read_bytes()
            class ChangingStream:
                def __init__(self, stream): self.stream = stream
                def __enter__(self): return self
                def __exit__(self, *args): self.stream.close()
                def fileno(self): return self.stream.fileno()
                def read(self, bound):
                    value = self.stream.read(bound)
                    with original(target, 'wb') as changed: changed.write(b'changed')
                    return value
            def changing(path, *args, **kwargs):
                stream = original(path, *args, **kwargs)
                return ChangingStream(stream) if path == target and args == ('rb',) else stream
            with patch.object(Path, 'open', changing):
                record = self.annotation()
            self.assert_failure(record, stage, 'read-changed')
            self.assertEqual('read-changed', record['diagnostic']['reads'][stage]['status'])
            if target != self.setup:
                self.assertNotIn('source_sha256_at_sample', record['diagnostic'])
            target.write_bytes(data)

    def test_stat_boundary_and_readlink_access(self):
        path = self.proc / '100/stat'; data = path.read_bytes()
        for size in (4096, 4097):
            path.write_bytes(data + b' ' * (size - len(data)))
            record = self.annotation()
            if size == 4096: self.assertEqual('native-file', record['identity_status'])
            else: self.assert_failure(record, 'process-before', 'limit-exceeded')
        path.write_bytes(data)
        original = os.readlink
        for target in (self.proc / '100/cwd', self.proc / '100/exe', self.proc / '50/exe'):
            def inaccessible(path, *args, **kwargs):
                if path == target: raise PermissionError(errno.EACCES, 'SECRET')
                return original(path, *args, **kwargs)
            with patch.object(os, 'readlink', inaccessible): record = self.annotation()
            self.assertEqual('unavailable', record['identity_status'])
            self.assertTrue(any(f.get('errno') == errno.EACCES for f in record['diagnostic']['failures']))
            self.assertNotIn('SECRET', json.dumps(record))

    def test_record_and_process_tree_bounds(self):
        record = self.annotation()
        record['diagnostic']['operands'] = {k: 'λ\\"' * 4000 for k in ('source', 'output', 'setup')}
        encoded = observer.encode_record(record, 'f' * 32)
        extra = {k: json.loads(encoded)[k] for k in ('diagnostic', 'sample_id')}
        self.assertLessEqual(len(json.dumps(extra, separators=(',', ':')).encode()), 4096)
        self.assertLessEqual(len(('NATIVE_TASK_SAMPLE ' + encoded + '\n').encode()), 4096)
        self.assertEqual('truncated', extra['diagnostic']['operand_status'])
        record['file'] = 'λ' * 4096
        encoded = observer.encode_record(record, 'f' * 32)
        self.assertLessEqual(len(('NATIVE_TASK_SAMPLE ' + encoded + '\n').encode()), 4096)
        self.assertEqual('unavailable', json.loads(encoded)['identity_status'])
        self.assertEqual('identity-omitted', json.loads(encoded)['diagnostic']['truncation'])
        cmd = [sys.executable, '-B', str(ROOT / 'tools/scripts/lib/native-task-observation.py'),
               '--proc-root', str(self.proc), '--repository', str(self.root), '--sample-id', 'a' * 32]
        for data, count in ((b'pid:100,ppid:50,rss_kb:1;' * 65, 64), (b'x' * 1048577, 1)):
            result = subprocess.run(cmd, input=data, capture_output=True, timeout=30)
            self.assertEqual(0, result.returncode, result.stderr)
            rows = [json.loads(x.split(b' ', 1)[1]) for x in result.stdout.splitlines()]
            self.assertEqual(count, len(rows))
            self.assertTrue(all(x['sample_id'] == 'a' * 32 for x in rows))
            self.assertLessEqual(sum(len(json.dumps({k: x[k] for k in ('diagnostic', 'sample_id')}, separators=(',', ':')).encode()) for x in rows), 262144)

    def test_sample_join_across_lifetimes_and_stream_interleaving(self):
        observer_path = self.root / 'tools/scripts/lib/native-task-observation.py'
        observer_path.parent.mkdir(parents=True)
        observer_path.write_bytes((ROOT / 'tools/scripts/lib/native-task-observation.py').read_bytes())
        script = r'''
source "$1/tools/scripts/lib/resource-observation-lib.sh"
resource_observation_process_values() { printf '1\t0\tpid:100,ppid:50,rss_kb:1\n'; }
source "$1/tools/scripts/lib/native-task-observation.sh" "$3" "$2"
resource_observe_sample 0 100 "$3" "$3" baseline || true
(resource_observe_sample 1 100 "$3" "$3" periodic || true)
(resource_observe_sample 0 100 "$3" "$3" signal || true)
resource_observe_sample 0 100 "$3" "$3" final '' 143 TERM || true
'''
        result = subprocess.run(['/bin/bash', '--noprofile', '--norc', '-c', script, 'join', str(ROOT), str(self.proc), str(self.root)],
                                cwd=self.root, capture_output=True, text=True, timeout=30)
        self.assertEqual(0, result.returncode, result.stderr)
        resources = [dict(word.split('=', 1) for word in x.split()[1:]) for x in result.stdout.splitlines() if x.startswith('RESOURCE_SAMPLE ')]
        annotations = [json.loads(x.split(' ', 1)[1]) for x in result.stderr.splitlines() if x.startswith('NATIVE_TASK_SAMPLE ')]
        # Deliberately reverse one stream: joining cannot depend on adjacency/order.
        by_id = {x['sample_id']: x for x in reversed(annotations)}
        self.assertEqual(4, len(by_id))
        self.assertEqual({'baseline', 'periodic', 'signal', 'final'}, {x['phase'] for x in resources})
        self.assertEqual(4, len({x['sample_id'] for x in resources}))
        for row in resources:
            self.assertEqual(100, by_id[row['sample_id']]['pid'])
            self.assertEqual('native-file', by_id[row['sample_id']]['identity_status'])
            self.assertEqual('unverified', by_id[row['sample_id']]['resource_tree_rss_association'])
            self.assertEqual(7, by_id[row['sample_id']]['memory']['rss_pages'])
            self.assertEqual('process-lifetime', by_id[row['sample_id']]['memory']['association'])
        self.assertEqual('143', resources[-1]['command_exit_status'])
        self.assertEqual('TERM', resources[-1]['termination_signal'])


if __name__ == '__main__':
    unittest.main()
