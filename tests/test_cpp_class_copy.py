"""Generic member copy permissions, shape failures, and the UF whole-state bridge."""
from pathlib import Path
import subprocess
import tempfile
import unittest
import sys
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE
from test_union_find_constructed_receiver import CHECKS as RECEIVER
from test_union_find_receiver_trace import CHECKS as TRACE
from test_union_find_rank_doubling import CHECKS as RANK
from test_union_find_copy_receiver import CHECKS as COPY
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
from class_copy import emit_class_copy
CHECKS = r'''
namespace ClassCopyChecks
open Proofs.CppConstructorFinish
abbrev C := Proofs.CppClassCopy.Profile
 def sourceRef : ObjectRef :=
   ⟨(layoutOf populated).vectorSlot,[(layoutOf populated).countSlot,(layoutOf populated).nSlot]⟩
 example (s : NState) (layout : Layout) := Proofs.UfClassCopyBridge.copy_equiv s layout
 example : Proofs.CppClassCopy.copyClass built sourceRef Proofs.UfClassCopyBridge.profile =
     some (duplicate,reference built 2) := by
   rw [show sourceRef = ⟨(layoutOf populated).vectorSlot,[(layoutOf populated).countSlot,(layoutOf populated).nSlot]⟩ from rfl,
     Proofs.UfClassCopyBridge.copy_equiv,copyActual]
   rfl
 example : Proofs.CppClassCopy.copyClass readonly sourceRef Proofs.UfClassCopyBridge.profile =
     (copyReceiver readonly (layoutOf populated)).map (fun r => (r.1,reference readonly 2)) :=
   Proofs.UfClassCopyBridge.copy_equiv readonly (layoutOf populated)
 def zeroProfile : C := ⟨i32,false,[]⟩
 def zero := Proofs.CppClassCopy.copyClass readonly ⟨sourceRef.vectorSlot,[]⟩ zeroProfile
 #guard zero.isSome
 #guard zero.map (fun r => r.1.scalars.memory) == some readonly.scalars.memory
 #guard zero.map (fun r => r.2.scalarSlots) == some []
 #guard zero.map (fun r => r.1.work) == some (readonly.work+6)
 #guard zero.map (fun r => (r.1.frame.resolve readonly.frame.bindings.length (.integer i32)).map
   (fun p => p.1.writable)) == some (some false)
 def mixedProfile : C := ⟨i32,true,[(i32,false),(i32,true),(i32,false)]⟩
 def three := Proofs.CppClassCopy.copyClass readonly
   ⟨sourceRef.vectorSlot,[sourceRef.scalarSlots[0]!,sourceRef.scalarSlots[1]!,sourceRef.scalarSlots[0]!]⟩ mixedProfile
 #guard three.isSome
 #guard three.map (fun r => r.2.scalarSlots.length) == some 3
 #guard three.map (fun r => r.1.work) == some (readonly.work+9)
 #guard three.map (fun r => r.1.scalars.bindings.drop readonly.scalars.bindings.length |>.map
   (fun b => b.writable)) == some [false,true,false]
 #guard three.map (fun r => r.1.scalars.memory.take readonly.scalars.memory.length) == some readonly.scalars.memory
 #guard (Proofs.CppClassCopy.copyClass built sourceRef zeroProfile).isNone
 #guard (Proofs.CppClassCopy.copyClass built ⟨999,[]⟩ zeroProfile).isNone
 #guard (Proofs.CppClassCopy.copyClass built ⟨sourceRef.vectorSlot,[999]⟩ ⟨i32,true,[(i32,true)]⟩).isNone
 #guard (Proofs.CppClassCopy.copyClass built ⟨sourceRef.vectorSlot,[sourceRef.scalarSlots[0]!]⟩
   ⟨i32,true,[(⟨64,false,false⟩,true)]⟩).isNone
 -- Copy representation states even when scalar n/count do not match vector length.
 -- This does not assert a UF method invariant for such a state.
 def mismatch : NState := {built with scalars := {built.scalars with
   memory := built.scalars.memory.map (fun c => if c.type == i32 then {c with value := 77} else c)}}
 def mismatchCopy := Proofs.CppClassCopy.copyClass mismatch sourceRef Proofs.UfClassCopyBridge.profile
 #guard mismatchCopy.isSome
 #guard mismatchCopy.map (fun r => (r.1.scalarCell r.2.scalarSlots[1]! i32).map
   (fun p => p.2.value)) == some (some 77)
 #guard mismatchCopy.map (fun r => r.1.work) == some (mismatch.work+8)
 example : mismatchCopy = (copyReceiver mismatch (layoutOf populated)).map
     (fun r => (r.1,reference mismatch 2)) := Proofs.UfClassCopyBridge.copy_equiv mismatch (layoutOf populated)
end ClassCopyChecks
'''

class ClassCopyTests(unittest.TestCase):
    def test_generic_permissions_failures_and_all_state_equivalence(self):
        source = ('import Proofs.UfClassCopyBridge\nimport Proofs.UfCopyReceiver\n' +
                  HEADER + CALLER_HEADER + STAGE + RECEIVER + TRACE + RANK + COPY + CHECKS)
        with tempfile.TemporaryDirectory(prefix='cpp-class-copy-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_audited_source_generation_and_declaration_order(self):
        candidate = ROOT / 'experiments/verification/data_structure/union_find.hpp'
        uf = emit_class_copy(candidate, 'cp::UnionFind', 'GeneratedUF')
        # Non-UF names, type aliases, const/mutable members and three scalars.
        with tempfile.TemporaryDirectory(prefix='class-copy-generation-') as directory:
            header = Path(directory) / 'packet.hpp'
            header.write_text('#include <vector>\nnamespace other { using Wide = long long; '
                              'struct Packet { const std::vector<Wide> data; unsigned length; '
                              'const long stamp; mutable bool ready; }; }\n')
            packet = emit_class_copy(header, 'other::Packet', 'GeneratedPacket')
            self.assertEqual(packet, emit_class_copy(header, 'other::Packet', 'GeneratedPacket'))
            with self.assertRaisesRegex(ValueError, 'namespace'):
                emit_class_copy(header, 'other::Packet', 'Bad\nend Bad')
            checks = r'''
example : GeneratedUF.profile = Proofs.UfClassCopyBridge.profile := rfl
example : GeneratedUF.fieldNames = ["_ps","_num_groups","_n"] := rfl
example (s : Proofs.CppNestedProgram.NState) (layout : Proofs.UfReceiverState.Layout) :
  GeneratedUF.copy s ⟨layout.vectorSlot,[layout.countSlot,layout.nSlot]⟩ =
    (Proofs.UfCopyFields.copyReceiver s layout).map (fun r =>
      (r.1,Proofs.CppConstructorFinish.reference s 2)) :=
  Proofs.UfClassCopyBridge.copy_equiv s layout
example : GeneratedPacket.profile =
  ⟨⟨64,true,false⟩,false,[(⟨32,false,false⟩,true),(⟨64,true,false⟩,false),(⟨1,false,true⟩,true)]⟩ := rfl
example : GeneratedPacket.fieldNames = ["data","length","stamp","ready"] := rfl
example : GeneratedPacket.qualifiedClass = "other::Packet" := rfl
'''
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfClassCopyBridge\n' +
                             uf.replace('import Proofs.CppClassCopy\n', '') +
                             packet.replace('import Proofs.CppClassCopy\n', '') + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
