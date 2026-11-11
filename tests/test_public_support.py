"""Registration checks for shared verification infrastructure."""

from pathlib import Path
from contextlib import ExitStack, redirect_stderr, redirect_stdout
import json
import io
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import public
import check_public
import process_supervisor as supervisor
import ci_check_cache
import ci_shards
from offline import disable_network


WORKER_SOURCE='from pathlib import Path\nimport json,os,subprocess,sys,time\nmarker=Path(sys.argv[1])\nchild=subprocess.Popen([sys.executable,\'-c\',"from pathlib import Path;import sys,time;time.sleep(1.2);Path(sys.argv[1]).write_text(\'late\')",str(marker)],start_new_session=sys.argv[2]==\'escape\')\nPath(str(marker)+\'.ready\').write_text(json.dumps([os.getpid(),child.pid,os.getppid()]))\nif len(sys.argv)>3 and sys.argv[3]==\'finish\':raise SystemExit(0)\ntime.sleep(2)\n'


class SupportTests(unittest.TestCase):
    def test_ci_checkpoint_revalidates_inputs_and_never_restores_the_final_audit(self):
        with tempfile.TemporaryDirectory(prefix='ci-checkpoint-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'
            source.write_text('first input')
            results, snapshot = scratch/'results.json', scratch/'snapshot.json'
            with patch.object(check_public.check_cache, 'ROOT', scratch), \
                 patch.object(check_public.check_cache, 'CACHE_FILE', results), \
                 patch.object(check_public.check_cache, '_environment', return_value='fixed-toolchain'), \
                 patch.object(check_public.check_cache, 'enabled', True):
                calls = []
                check_public.check_cache.cached_call('cpp:example', [source], lambda: calls.append('first'))
                check_public.check_cache.cached_call('proof-security', [source], lambda: calls.append('audit'))
                self.assertEqual(ci_check_cache.transfer(results, snapshot), 1)
                # Also reject an audit entry in an incorrectly populated snapshot.
                data = json.loads(snapshot.read_text())
                data['proof-security'] = json.loads(results.read_text())['proof-security']
                snapshot.write_text(json.dumps(data))
                self.assertEqual(ci_check_cache.transfer(snapshot, results), 1)
                check_public.check_cache.cached_call('cpp:example', [source], lambda: calls.append('unexpected'))
                check_public.check_cache.cached_call('proof-security', [source], lambda: calls.append('fresh audit'))
                source.write_text('changed input')
                check_public.check_cache.cached_call('cpp:example', [source], lambda: calls.append('changed'))
                self.assertEqual(calls, ['first', 'audit', 'fresh audit', 'changed'])
            self.assertEqual(ci_check_cache.transfer(scratch/'missing', snapshot), 0)
            self.assertEqual(json.loads(snapshot.read_text()), {})
            malformed = scratch/'malformed.json'
            malformed.write_text('[]')
            with self.assertRaisesRegex(ValueError, 'must be an object'):
                ci_check_cache.transfer(malformed, results)

    def test_supervised_commands_and_traced_cache(self):
        out=Path(supervisor.__file__).resolve().parent
        rows=[]
        def absent(pid):
            try:return Path('/proc',str(pid),'stat').read_text().split()[2]=='Z'
            except FileNotFoundError:return True
        with tempfile.TemporaryDirectory(prefix='supervisor-cases-') as directory:
            scratch=Path(directory)
            worker=scratch/'worker.py';worker.write_text('from pathlib import Path\nimport json,os,subprocess,sys,time\nmarker=Path(sys.argv[1])\nchild=subprocess.Popen([sys.executable,\'-c\',"from pathlib import Path;import sys,time;time.sleep(1.2);Path(sys.argv[1]).write_text(\'late\')",str(marker)],start_new_session=sys.argv[2]==\'escape\')\nPath(str(marker)+\'.ready\').write_text(json.dumps([os.getpid(),child.pid,os.getppid()]))\nif len(sys.argv)>3 and sys.argv[3]==\'finish\':raise SystemExit(0)\ntime.sleep(2)\n')
            r=supervisor.capture([sys.executable,'-c','import sys;print(sys.stdin.read())'],input='in',text=True,timeout=2)
            assert r.stdout=='in\n' and r.stderr==''
            rows.append(dict(case='stdin_stdout',passed=True))
            for code in (17,-signal.SIGTERM):
                script='import sys;print("out");print("err",file=sys.stderr);raise SystemExit(17)' if code==17 else 'import os,signal;os.kill(os.getpid(),signal.SIGTERM)'
                try:supervisor.capture([sys.executable,'-c',script],text=True,timeout=2)
                except subprocess.CalledProcessError as e:
                    assert e.returncode==code
                    if code==17:assert (e.stdout,e.stderr)==('out\n','err\n')
                else:raise AssertionError('failure swallowed')
                rows.append(dict(case='exit_'+str(code),passed=True))
            for kind in ('ordinary','escape'):
                marker=scratch/kind;ready=Path(str(marker)+'.ready')
                try:supervisor.capture([sys.executable,str(worker),str(marker),kind],text=True,timeout=.5)
                except subprocess.TimeoutExpired:pass
                else:raise AssertionError('timeout not raised')
                assert ready.exists(),'worker did not start before deadline'
                pids=json.loads(ready.read_text());assert all(absent(pid) for pid in pids[:2])
                assert not marker.exists()
                rows.append(dict(case='timeout_'+kind,passed=True))
            marker=scratch/'background';ready=Path(str(marker)+'.ready')
            r=supervisor.capture([sys.executable,str(worker),str(marker),'escape','finish'],text=True,timeout=2)
            assert r.returncode==0 and ready.exists() and not marker.exists()
            assert all(absent(pid) for pid in json.loads(ready.read_text())[:2])
            rows.append(dict(case='reap_after_success',passed=True))
            marker=scratch/'interrupt';ready=Path(str(marker)+'.ready');original=subprocess.Popen.communicate;seen=[]
            def interrupt(child,*args,**kwargs):
                if not seen:
                    seen.append(child);end=time.monotonic()+1
                    while not ready.exists():
                        assert time.monotonic()<end
                        time.sleep(.01)
                    raise KeyboardInterrupt
                return original(child,*args,**kwargs)
            with patch.object(subprocess.Popen,'communicate',new=interrupt):
                try:supervisor.capture([sys.executable,str(worker),str(marker),'escape'],text=True,timeout=2)
                except KeyboardInterrupt:pass
                else:raise AssertionError('interrupt swallowed')
            assert seen[0].returncode==0 and not marker.exists()
            assert all(absent(pid) for pid in json.loads(ready.read_text())[:2])
            rows.append(dict(case='interrupt_escape',passed=True))
            marker=scratch/'parentdeath';ready=Path(str(marker)+'.ready');driver=scratch/'driver.py'
            driver.write_text('import sys\nsys.path.insert(0,'+repr(str(out))+')\nfrom process_supervisor import capture\ncapture(sys.argv[1:],timeout=5,text=True)\n')
            parent=subprocess.Popen([sys.executable,str(driver),sys.executable,str(worker),str(marker),'escape'],start_new_session=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            end=time.monotonic()+2
            while not ready.exists():
                assert time.monotonic()<end
                time.sleep(.01)
            os.killpg(parent.pid,signal.SIGKILL);parent.communicate(timeout=3)
            assert parent.returncode==-signal.SIGKILL and not marker.exists()
            pids=json.loads(ready.read_text());end=time.monotonic()+1
            while not all(absent(pid) for pid in pids):
                assert time.monotonic()<end
                time.sleep(.01)
            rows.append(dict(case='parent_group_sigkill_escape',passed=True))
        print(json.dumps(rows))

        import check_cache as cache
        root=cache.ROOT
        with tempfile.TemporaryDirectory(prefix='supervised-trace-cache-') as directory:
            scratch=Path(directory);worker=scratch/'worker.py'
            worker.write_text(WORKER_SOURCE)
            with patch.object(cache,'CACHE_FILE',scratch/'cache.json'), patch.object(cache,'enabled',True):
                success=[sys.executable,'-c','print("ok")']
                cache.run_traced('probe_success',success,cwd=root,timeout=2)
                assert 'probe_success' in json.loads(cache.CACHE_FILE.read_text())
                buffer=io.StringIO()
                with redirect_stdout(buffer):cache.run_traced('probe_success',success,cwd=root,timeout=2)
                assert buffer.getvalue()=='(cached) probe_success\n'
                failed=[sys.executable,'-c','import sys;print("out");print("err",file=sys.stderr);raise SystemExit(17)']
                errors=io.StringIO()
                with redirect_stderr(errors):
                    try:cache.run_traced('probe_failure',failed,cwd=root,timeout=2)
                    except subprocess.CalledProcessError as e:assert (e.returncode,e.stdout,e.stderr)==(17,'out\n','err\n')
                    else:raise AssertionError('failure accepted')
                assert errors.getvalue()=='out\nerr\n'
                assert 'probe_failure' not in json.loads(cache.CACHE_FILE.read_text())
                marker=scratch/'timeout'
                try:cache.run_traced('probe_timeout',[sys.executable,str(worker),str(marker),'escape'],cwd=root,timeout=.5)
                except subprocess.TimeoutExpired:pass
                else:raise AssertionError('timeout accepted')
                assert not marker.exists() and 'probe_timeout' not in json.loads(cache.CACHE_FILE.read_text())
                with self.assertRaisesRegex(RuntimeError, 'FileNotFoundError'):
                    supervisor.capture([str(scratch/'missing-command')], text=True, timeout=2)

    def test_expired_budget_does_not_start_or_accept_cached_proof_audit(self):
        with patch.object(check_public, 'deadline', 0), \
                patch.object(check_public.check_cache, 'cached_call') as cache, \
                self.assertRaisesRegex(RuntimeError, 'exceeded its time limit'):
            check_public.check_lean()
        cache.assert_not_called()

    def test_proof_audit_rechecks_budget_after_cache_lookup(self):
        def lookup(name, inputs, function):
            check_public.deadline = 0
            function()
        with patch.object(check_public, 'deadline', time.monotonic() + 60), \
                patch.object(check_public.check_cache, 'cached_call', side_effect=lookup), \
                patch.object(check_public.subprocess, 'Popen') as start, \
                self.assertRaisesRegex(RuntimeError, 'exceeded its time limit'):
            check_public.check_lean()
        start.assert_not_called()

    def test_cached_audit_still_checks_budget_on_return(self):
        def lookup(name, inputs, function):
            check_public.deadline = 0
        with patch.object(check_public, 'deadline', time.monotonic() + 60), \
                patch.object(check_public.check_cache, 'cached_call', side_effect=lookup), \
                self.assertRaisesRegex(RuntimeError, 'exceeded its time limit'):
            check_public.check_lean()

    def test_proof_audit_uses_the_bounded_command_runner(self):
        def lookup(name, inputs, function):
            self.assertEqual(name, 'proof-security')
            function()
        with patch.object(check_public, 'deadline', time.monotonic() + 60), \
                patch.object(check_public.check_cache, 'cached_call', side_effect=lookup), \
                patch.object(check_public, 'run') as run:
            check_public.check_lean()
        run.assert_called_once_with([sys.executable, str(ROOT / 'tools/check_proof_security.py')])

    def test_timeout_stops_the_command_and_its_child(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            record = scratch / 'pids.json'
            script = scratch / 'parent.py'
            script.write_text('import json,os,subprocess,sys,time\n'
                              'from pathlib import Path\n'
                              'child=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"])\n'
                              'Path(sys.argv[1]).write_text(json.dumps([os.getpid(),child.pid]))\n'
                              'time.sleep(60)\n')
            with patch.object(check_public, 'deadline', time.monotonic() + 1), \
                    self.assertRaisesRegex(RuntimeError, 'exceeded its time limit'):
                check_public.run([sys.executable, str(script), str(record)])
            parent_pid, child_pid = json.loads(record.read_text())
            try:
                with self.assertRaises(ProcessLookupError):
                    os.kill(parent_pid, 0)
                end = time.monotonic() + 1
                while True:
                    stat = Path(f'/proc/{child_pid}/stat')
                    try:
                        state = stat.read_text().split()[2]
                    except FileNotFoundError:
                        break
                    if state == 'Z':
                        break
                    self.assertLess(time.monotonic(), end, 'timed-out child is still running')
                    time.sleep(.01)
            finally:
                try:
                    os.kill(child_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    def test_command_failure_keeps_the_exit_status(self):
        with patch.object(check_public, 'deadline', time.monotonic() + 10), \
                self.assertRaises(subprocess.CalledProcessError) as error:
            check_public.run([sys.executable, '-c', 'raise SystemExit(7)'])
        self.assertEqual(error.exception.returncode, 7)

    def test_interrupted_command_is_stopped_before_propagating(self):
        with patch.object(check_public, 'deadline', time.monotonic() + 60), \
                patch.object(check_public.subprocess, 'Popen') as start, \
                patch.object(check_public.os, 'killpg') as stop:
            child = start.return_value.__enter__.return_value
            child.wait.side_effect = [KeyboardInterrupt(), -9]
            with self.assertRaises(KeyboardInterrupt):
                check_public.run(['owned-command'])
        stop.assert_called_once_with(child.pid, signal.SIGKILL)
        child.wait.assert_any_call()

    def test_test_imports_come_from_screened_build(self):
        command = [sys.executable, str(ROOT / 'tools/check_proof_security.py'), '--prepare-test-imports']
        environment = {k: v for k, v in os.environ.items() if k != 'PROOF_BUILD_THREADS'}
        with patch.dict(os.environ, environment, clear=True), patch.object(check_public, 'run') as run:
            check_public.build_lean()
        run.assert_called_once_with(command)
        with patch.dict(os.environ, {'PROOF_BUILD_THREADS': '4', 'LEAN_NUM_THREADS': '1'}), \
                patch.object(check_public, 'run') as run:
            check_public.build_lean()
        self.assertEqual(run.call_args.args, (command,))
        self.assertEqual(run.call_args.kwargs['env']['LEAN_NUM_THREADS'], '4')
        for value in ('0', 'four', ''):
            with self.subTest(value=value), patch.dict(os.environ, {'PROOF_BUILD_THREADS': value}), \
                    patch.object(check_public, 'run') as run, self.assertRaisesRegex(RuntimeError, 'positive'):
                check_public.build_lean()
            run.assert_not_called()

    def test_full_gate_builds_imports_before_tests_and_audits_afterwards(self):
        events = []

        def imported_check(*args):
            self.assertEqual(events, ['build'])
            events.append('imported-test')

        with ExitStack() as stack:
            for name in ['disable_network', 'lower_priority', 'check_local_results_untracked', 'check_compiler']:
                stack.enter_context(patch.object(check_public, name))
            stack.enter_context(patch.object(sys, 'argv', ['check_public.py']))
            stack.enter_context(patch.object(check_public, 'registry', return_value={}))
            stack.enter_context(patch.object(check_public, 'cpp_tasks', return_value=[]))
            stack.enter_context(patch.object(check_public, 'bridge_tasks', return_value=[]))
            stack.enter_context(patch.object(check_public, 'support_registry',
                                            return_value={'checks': ['tests/test_public_support.py']}))
            stack.enter_context(patch.object(check_public, 'run_traced', side_effect=imported_check))
            stack.enter_context(patch.object(check_public, 'build_lean', side_effect=lambda: events.append('build')))
            stack.enter_context(patch.object(check_public, 'check_lean', side_effect=lambda: events.append('audit')))
            check_public.main()
        self.assertEqual(events, ['build', 'imported-test', 'audit'])

    def test_failed_proof_build_stops_before_tests_and_audit(self):
        with ExitStack() as stack:
            for name in ['disable_network', 'lower_priority', 'check_local_results_untracked', 'check_compiler']:
                stack.enter_context(patch.object(check_public, name))
            stack.enter_context(patch.object(sys, 'argv', ['check_public.py']))
            stack.enter_context(patch.object(check_public, 'registry', return_value={}))
            stack.enter_context(patch.object(check_public, 'cpp_tasks', return_value=[]))
            stack.enter_context(patch.object(check_public, 'bridge_tasks', return_value=[]))
            stack.enter_context(patch.object(check_public, 'support_registry', return_value={'checks': []}))
            stack.enter_context(patch.object(check_public, 'build_lean', side_effect=RuntimeError('build failed')))
            tasks = stack.enter_context(patch.object(check_public, 'run_tasks'))
            audit = stack.enter_context(patch.object(check_public, 'check_lean'))
            with self.assertRaisesRegex(RuntimeError, 'build failed'):
                check_public.main()
            tasks.assert_not_called()
            audit.assert_not_called()

    def gate_events(self, argv, labels):
        """Run check_public.main with stubbed checks; return the order of build, checks and audit."""
        events = []
        tasks = [(label, lambda label=label: events.append(label)) for label in labels]
        with ExitStack() as stack:
            for name in ['disable_network', 'lower_priority', 'check_local_results_untracked', 'check_compiler']:
                stack.enter_context(patch.object(check_public, name))
            stack.enter_context(patch.object(sys, 'argv', ['check_public.py', *argv]))
            stack.enter_context(patch.object(check_public, 'registry', return_value={}))
            stack.enter_context(patch.object(check_public, 'all_tasks', return_value=tasks))
            stack.enter_context(patch.object(check_public, 'build_lean', side_effect=lambda: events.append('build')))
            stack.enter_context(patch.object(check_public, 'check_lean', side_effect=lambda: events.append('audit')))
            with redirect_stdout(io.StringIO()):
                check_public.main()
        return events

    def test_ci_shards_and_audit_together_run_the_full_gate_once(self):
        labels = [f'check:tests/t{i}.py' for i in range(23)] + ['cpp:a', 'bridge:a', 'cpp-common [x]']
        count = 5
        runs = [self.gate_events(['--mode', 'tests', '--shard', f'{index}/{count}'], labels)
                for index in range(count)]
        for events in runs:
            self.assertEqual(events[0], 'build')
            self.assertNotIn('audit', events)
        checks = [label for events in runs for label in events if label != 'build']
        self.assertEqual(sorted(checks), sorted(labels))
        self.assertEqual(self.gate_events(['--mode', 'audit'], labels), ['build', 'audit'])
        self.assertEqual(self.gate_events([], labels), ['build', *labels, 'audit'])
        self.assertEqual(self.gate_events(['--mode', 'cpp'], labels), labels)

    def test_shard_arguments_are_validated(self):
        for argv in (['--shard', '0/2'], ['--mode', 'audit', '--shard', '0/2']):
            with self.subTest(argv=argv), self.assertRaisesRegex(RuntimeError, '--shard needs --mode tests'):
                self.gate_events(argv, [])
        for text in ('2/2', '1', 'a/b', '-1/2'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                ci_shards.parse_shard(text)

    def test_shard_plan_is_deterministic_balanced_and_complete(self):
        weights = {'default_seconds': {'': 10, 'cpp': 1}, 'split_methods': [],
                   'seconds': {'check:big': 100, 'check:mid': 60, 'check:small': 40}}
        labels = ['check:small', 'cpp:x', 'check:big', 'check:unknown', 'check:mid', 'cpp:y']
        shards, loads = ci_shards.assign(labels, 2, weights)
        self.assertEqual(set(shards), set(labels))
        self.assertEqual(ci_shards.assign(list(reversed(labels)), 2, weights), (shards, loads))
        self.assertEqual(loads, [110, 102])
        self.assertEqual(shards['check:big'], 0)

    def test_split_methods_cover_every_unittest_method(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'test_split.py'
            source.write_text('import unittest\nclass A(unittest.TestCase):\n    def test_a(self): pass\n'
                              '    def helper(self): pass\nclass B(unittest.TestCase):\n    def test_b(self): pass\n'
                              'class Mixin:\n    pass\n')
            self.assertEqual(ci_shards.test_methods(source), ['A.test_a', 'B.test_b'])
            source.write_text('import unittest\nclass A(unittest.TestCase):\n    def test_a(self): pass\n'
                              'class C(A):\n    def test_c(self): pass\n')
            with self.assertRaisesRegex(ValueError, 'derive directly'):
                ci_shards.test_methods(source)
        weights = {'default_seconds': {'': 10}, 'split_methods': ['tests/test_template_class_layout.py'],
                   'seconds': {'check:tests/test_template_class_layout.py': 400}}
        tasks = ci_shards.check_tasks(['tests/test_public_support.py', 'tests/test_template_class_layout.py'], weights)
        methods = ci_shards.test_methods(ROOT / 'tests/test_template_class_layout.py')
        self.assertEqual(tasks[0], ('check:tests/test_public_support.py', []))
        self.assertEqual(tasks[1:], [(f'check:tests/test_template_class_layout.py::{m}', [m]) for m in methods])
        siblings = {'check:tests/test_template_class_layout.py': len(methods)}
        self.assertAlmostEqual(ci_shards.weight(tasks[1][0], weights, siblings), 400 / len(methods))
        with self.assertRaisesRegex(ValueError, 'unregistered'):
            ci_shards.check_split_registered(['tests/test_public_support.py'], weights)

    def test_registered_split_files_and_workflow_matrix_are_consistent(self):
        weights = ci_shards.load_weights()
        checks = public.support_registry()['checks']
        ci_shards.check_split_registered(checks, weights)
        self.assertGreater(ci_shards.workflow_shards((ROOT / '.github/workflows/ci.yml').read_text()), 1)
        with self.assertRaisesRegex(ValueError, 'does not list'):
            ci_shards.workflow_shards("        shard: [0, 2]\n      SHARDS: '2'\n")

    def test_weight_update_keeps_real_measurements_only(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'weights.json'
            path.write_text(json.dumps({'default_seconds': {'': 10}, 'split_methods': [],
                                        'seconds': {'check:a': 50, 'check:b': 70}}))
            log = Path(directory) / 'job.log'
            log.write_text('2026Z check passed after 0.012s: check:a\n2026Z check passed after 81.25s: check:b\n'
                           '2026Z check passed after 3.0s: check:tests/t.py::A.test_a\n')
            with patch.object(ci_shards, 'ROOT', Path(directory)), redirect_stdout(io.StringIO()):
                ci_shards.update([log], path)
            self.assertEqual(json.loads(path.read_text())['seconds'],
                             {'check:a': 50, 'check:b': 81.2, 'check:tests/t.py::A.test_a': 3.0})

    def fixture(self, root):
        def write(path, text=""):
            destination = root / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(text)
        write("verifier/support.toml", 'lean_modules = ["Proofs/Core.lean"]\n'
              'python_modules = ["verifier/core.py"]\nchecks = ["tests/core.py"]\n'
              'documents = ["docs/core.md"]\n')
        for path in ["Proofs/Core.lean", "verifier/core.py", "tests/core.py", "docs/core.md",
                     "verifier/nested_bridge.py", "docs/spec.md"]:
            write(path)
        for name in ["a", "b"]:
            write(f"library/{name}.hpp")
            write(f"Proofs/{name}.lean")
            write(f"Proofs/Generated/{name}.lean")
            write(f"tests/{name}.cpp")
            write(f"benchmarks/{name}.cpp")
            write(f"library/{name}.toml", f'''name = "{name}"
source = "{name}.hpp"
standard = "c++17"
translation = "nested_ir"
lean_namespace = "Proofs.Instance{name}"
spec = "docs/spec.md"
source_sha256 = "{'1' * 64}"
public_declarations = ["FunctionDecl:f"]
dependencies = []
proof = "Proofs/{name}.lean"
model = "Proofs/Generated/{name}.lean"
bridge = "verifier/nested_bridge.py"
benchmark = "benchmarks/{name}.cpp"
tests = ["tests/{name}.cpp"]
''')
        write("Proofs.lean", "import Proofs.a\nimport Proofs.b\nimport Proofs.Core\n")

    def test_nested_components_keep_unique_names_and_ordered_includes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            for name,category in [('a','array'),('b','graph')]:
                target=root/'library'/category;target.mkdir()
                (root/'library'/f'{name}.hpp').rename(target/f'{name}.hpp')
                old=root/'library'/f'{name}.toml'
                text=old.read_text().replace(f'source = "{name}.hpp"',f'source = "{category}/{name}.hpp"')
                if name=='b':text=text.replace('dependencies = []','dependencies = ["a"]')
                old.rename(target/f'{name}.toml');(target/f'{name}.toml').write_text(text)
            with patch.object(public,'ROOT',root),patch.object(public,'PUBLIC',root/'library'):
                entries=public.registry()
                self.assertEqual(public.component('b')['source'],'graph/b.hpp')
                self.assertEqual(public.dependency_order('b',entries),['a','b'])
                with patch.object(public,'TEMPLATE','library/array/a.hpp'):
                    includes=public.include_check(['b'],entries)
                    self.assertEqual(includes.count('library/array/a.hpp'),1)
                    self.assertLess(includes.index('array/a.hpp'),includes.index('graph/b.hpp'))
                duplicate=root/'library/graph/a.toml'
                duplicate.write_text((root/'library/array/a.toml').read_text().replace('array/a.hpp','graph/a.hpp'))
                (root/'library/graph/a.hpp').write_text('')
                with self.assertRaisesRegex(ValueError,'invalid component name'):public.registry()
                with self.assertRaisesRegex(ValueError,'expected one metadata'):public.component('a')

    def test_shared_bridge_and_support_are_allowed_but_unregistered_proofs_are_not(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            with patch.object(public, "ROOT", root), patch.object(public, "PUBLIC", root / "library"):
                self.assertEqual(set(public.registry()), {"a", "b"})
                (root / "Proofs/Hidden").mkdir()
                (root / "Proofs/Hidden/Unexpected.lean").write_text("")
                with self.assertRaisesRegex(ValueError, "proof/model files"):
                    public.registry()

    def test_support_import_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            (root / "Proofs.lean").write_text("import Proofs.a\nimport Proofs.b\n")
            with patch.object(public, "ROOT", root), patch.object(public, "PUBLIC", root / "library"):
                with self.assertRaisesRegex(ValueError, "imports"):
                    public.registry()

    def test_shared_generated_models_require_registration_and_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            model = root / "Proofs/Generated/Experiment.lean"
            model.write_text("")
            with patch.object(public, "ROOT", root), patch.object(public, "PUBLIC", root / "library"):
                with self.assertRaisesRegex(ValueError, "proof/model files"):
                    public.registry()
                manifest = root / "verifier/support.toml"
                manifest.write_text(manifest.read_text().replace('"Proofs/Core.lean"]',
                    '"Proofs/Core.lean", "Proofs/Generated/Experiment.lean"]'))
                with self.assertRaisesRegex(ValueError, "imports"):
                    public.registry()
                imports = root / "Proofs.lean"
                imports.write_text(imports.read_text() + "import Proofs.Generated.Experiment\n")
                self.assertEqual(set(public.registry()), {"a", "b"})

    def test_missing_support_checks_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            (root / "tests/core.py").unlink()
            with patch.object(public, "ROOT", root), patch.object(public, "PUBLIC", root / "library"):
                with self.assertRaisesRegex(ValueError, "missing or invalid"):
                    public.registry()

    def test_common_component_configuration_requires_spec_and_rejects_fingerprint_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            (root / "verifier/nested_bridge.py").rename(root / "verifier/state_bridge.py")
            (root / "docs/spec.md").write_text("input conditions and contract")
            for name in ["a", "b"]:
                metadata = root / f"library/{name}.toml"
                text = metadata.read_text().replace('verifier/nested_bridge.py', 'verifier/state_bridge.py')
                metadata.write_text(text.replace('translation = "nested_ir"', 'translation = "state_ir"'))
            with patch.object(public, "ROOT", root), patch.object(public, "PUBLIC", root / "library"):
                self.assertEqual(set(public.registry()), {"a", "b"})
                metadata = root / "library/a.toml"
                original = metadata.read_text()
                for policy in ['checked', 'gcc13.3-lp64-twos-complement']:
                    metadata.write_text(original + f'\nsigned_conversion = "{policy}"\n')
                    self.assertEqual(set(public.registry()), {'a', 'b'})
                metadata.write_text(original + '\nsigned_conversion = "unknown-target"\n')
                with self.assertRaisesRegex(ValueError, 'signed conversion contract'):
                    public.registry()
                metadata.write_text(original + f'\nreviewed_ast_sha256 = "{"0" * 64}"\n')
                with self.assertRaisesRegex(ValueError, "fingerprint"):
                    public.registry()
                metadata.write_text(original.replace('spec = "docs/spec.md"', 'spec = "docs/missing.md"'))
                with self.assertRaisesRegex(ValueError, "missing or invalid"):
                    public.registry()

    def test_context_class_registration_requires_one_matching_class_and_common_bridge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            metadata = root / 'library/a.toml'
            text = metadata.read_text().replace('translation = "nested_ir"',
                'translation = "context_class_ir"').replace('FunctionDecl:f', 'CXXRecordDecl:C')
            valid = text + '\nqualified_class = "cp::C"\n'
            with patch.object(public, 'ROOT', root), patch.object(public, 'PUBLIC', root / 'library'):
                metadata.write_text(valid)
                self.assertEqual(set(public.registry()), {'a', 'b'})
                for broken in [text, valid.replace('cp::C', 'other::C'),
                        valid.replace('cp::C', 'cp::D'), valid.replace('cp::C', 'cp::outer::C'),
                        valid.replace('["CXXRecordDecl:C"]', '["CXXRecordDecl:C", "FunctionDecl:f"]'),
                        valid.replace('verifier/nested_bridge.py', 'verifier/core.py')]:
                    with self.subTest(metadata=broken):
                        metadata.write_text(broken)
                        with self.assertRaises(ValueError):
                            public.registry()
                metadata.write_text(valid.replace('translation = "context_class_ir"',
                    'translation = "nested_ir"'))
                with self.assertRaisesRegex(ValueError, 'qualified_class'):
                    public.registry()


if __name__ == "__main__":
    disable_network()
    unittest.main()
