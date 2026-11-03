"""Compiler-resolved include profiles retain origin checks and pristine comparison."""
from pathlib import Path
import subprocess
import json
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT/'verifier'))
sys.path.insert(0, str(ROOT/'tools'))
from vector_stl import standard_include_profile, pinned_includes, translation_unit, audit_vector_operations, audit_vector_nodes
from class_copy import emit_class_copy
from test_scalar_ir import lean_environment
from offline import disable_network

class StandardIncludeProfileTests(unittest.TestCase):
    def test_ordered_report_and_pinned_replay_validation(self):
        vector, algorithm = pinned_includes(('vector', 'algorithm'))
        with tempfile.TemporaryDirectory(prefix='include-report-') as directory:
            unit = Path(directory)/'main.cpp'; unit.write_text('')
            wrapper = Path(directory)/'wrapper.hpp'; wrapper.write_text('')
            report = json.dumps(dict(source=str(unit), includes=[vector, algorithm]))
            self.assertEqual(standard_include_profile(report, unit), (vector, algorithm))
            with self.assertRaisesRegex(ValueError, 'report'):
                standard_include_profile(report, wrapper)
            with self.assertRaisesRegex(ValueError, 'report'):
                standard_include_profile(json.dumps(dict(source=str(unit), includes=vector)), unit)
            with self.assertRaisesRegex(ValueError, 'pinned system'):
                pinned_includes((str(wrapper),))
            with self.assertRaisesRegex(ValueError, 'invalid'):
                pinned_includes(('vector>\n#define injected',))

    def test_active_macro_includes_and_search_path_shadowing(self):
        with tempfile.TemporaryDirectory(prefix='include-active-') as directory:
            directory = Path(directory)
            (directory/'wrapper.hpp').write_text('#include <algorithm>\n')
            # This user header is an intermediate wrapper, not a pristine replay input.
            (directory/'vector').write_text('#include_next <vector>\n')
            source = directory/'main.cpp'
            source.write_text('#define SELECTED "wrapper.hpp"\n#include SELECTED\n'
                              '#if 0\n#include <map>\n#endif\n#include <vector>\n'
                              'int f(){std::vector<int> v(3,2); return v[0];}\n')
            functions, roots = translation_unit(source, [directory])
            expected = pinned_includes(('algorithm', 'vector'))
            self.assertTrue(functions)
            self.assertTrue(roots)
            self.assertTrue(all(r['_standard_include_profile'] == expected for r in roots))
            audit_vector_operations(source, [directory])

    def test_macro_modified_standard_primary_remains_rejected(self):
        with tempfile.TemporaryDirectory(prefix='include-macro-') as directory:
            source = Path(directory)/'main.cpp'
            source.write_text('#define _GLIBCXX_ASSERTIONS 1\n#include <vector>\n'
                              'int f(){std::vector<int> v(3,2); return v[0];}\n')
            functions, roots = translation_unit(source)
            with self.assertRaisesRegex(ValueError, 'primary differs'):
                audit_vector_nodes(source, functions, roots)
            for root in roots:
                root.pop('_standard_include_profile')
            with self.assertRaisesRegex(ValueError, 'missing or inconsistent'):
                audit_vector_nodes(source, functions, roots)
            for root in roots:
                root['_standard_include_profile'] = (str(source),)
            with self.assertRaisesRegex(ValueError, 'pinned system'):
                audit_vector_nodes(source, functions, roots)
            for root in roots:
                root['_standard_include_profile'] = pinned_includes(('vector',))
            roots[0]['_standard_include_profile'] = pinned_includes(('algorithm',))
            with self.assertRaisesRegex(ValueError, 'missing or inconsistent'):
                audit_vector_nodes(source, functions, roots)


    def test_legacy_header_generates_the_same_copy_model(self):
        source = ROOT/'experiments/library/cpp/union_find/union_find.hpp'
        before = source.read_bytes()
        emitted = emit_class_copy(source, 'UnionFind', 'LegacyCopy', [ROOT/'experiments/library/cpp'])
        self.assertEqual(source.read_bytes(), before)
        proof = ('import Proofs.UfClassCopyBridge\n' + emitted.replace('import Proofs.CppClassCopy\n', '') + r'''
example : LegacyCopy.profile = Proofs.UfClassCopyBridge.profile := rfl
example : LegacyCopy.fieldNames = ["_ps","_num_groups","_n"] := rfl
example (s : Proofs.CppNestedProgram.NState) (layout : Proofs.UfReceiverState.Layout) :
  LegacyCopy.copy s ⟨layout.vectorSlot,[layout.countSlot,layout.nSlot]⟩ =
    (Proofs.UfCopyFields.copyReceiver s layout).map (fun r =>
      (r.1,Proofs.CppConstructorFinish.reference s 2)) :=
  Proofs.UfClassCopyBridge.copy_equiv s layout
''')
        with tempfile.TemporaryDirectory(prefix='legacy-copy-lean-') as directory:
            path = Path(directory)/'checks.lean'; path.write_text(proof)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
