"""Actual constructor export retains caller writes and the new field layout."""
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests'), str(ROOT / 'verifier')]
import test_class_call_ir as helpers
from class_copy_layout import emit_class_layout
from offline import disable_network
from test_scalar_ir import lean_environment

SOURCE = '''#include <vector>
struct Counter {
 std::vector<int> data; int count;
 Counter(int &outside):data(1,0),count(outside){outside=9;}
};
'''

CHECKS = r'''
namespace ConstructorWriteLayoutExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.CppConstructorLayout
abbrev i32 : Ty := ⟨32,true,false⟩
def caller : NState := ⟨⟨[⟨i32,7⟩],[⟨0,true⟩],0,0,0⟩,
  ⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[.scalar 0],0,0⟩
def make := Constructors.Counter_construct0_exportFuel 32 caller [.scalarReference 0]
def produced : NState := match make with | .finished (out,_) => out | _ => caller
example : produced.scalars.memory.map (·.value) = [9,7] := by decide +kernel
example : produced.slots = [.scalar 0,.vector 0,.scalar 1] := by decide +kernel
example : produced.scalars.bindings = [⟨0,true⟩,⟨1,true⟩] := by decide +kernel
example : Layout caller produced (reference caller 1) := by
  have actual : make = .finished (produced,reference caller 1) := by decide +kernel
  exact construct_layout Constructors.Counter_construct0 32 caller produced [.scalarReference 0]
    Constructors.Counter_construct0_vectorSlot (.integer i32) Constructors.Counter_construct0_scalarFields
    (reference caller 1) rfl actual
end ConstructorWriteLayoutExamples
'''

class CppConstructorLayoutTests(unittest.TestCase):
    def test_reference_write_is_kept_while_field_captures_original_value(self):
        with tempfile.TemporaryDirectory(prefix='constructor-write-layout-') as directory:
            source = Path(directory) / 'source.hpp'
            source.write_text(SOURCE)
            generated = emit_class_layout(source, 'Counter', 'Constructors')
            content = 'import Proofs.CppConstructorLayout\n' + generated + CHECKS
            imports = [line for line in content.splitlines() if line.startswith('import ')]
            body = [line for line in content.splitlines() if not line.startswith('import ')]
            proof = Path(directory) / 'checks.lean'
            proof.write_text('\n'.join(imports + body) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)
            self.assertEqual(helpers.ClassCallerTests.native(self, source,
                'int outside=7;Counter p(outside);std::cout<<outside<<" "<<p.count;', directory), '9 7')

if __name__ == '__main__':
    disable_network()
    unittest.main()
