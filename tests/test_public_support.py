"""Registration checks for shared verification infrastructure."""

from pathlib import Path
from contextlib import ExitStack
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import public
import check_public
from offline import disable_network


class SupportTests(unittest.TestCase):
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
