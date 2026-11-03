"""Normal receiver preparation, scalar addresses and compact callee shape."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from offline import disable_network

VALUE_CHECKS = r'''

namespace ValueArgumentExamples
open Proofs.CppMoveContext Proofs.CppMoveReceiverLayout
abbrev ty : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def initial : Context := ⟨⟨⟨[],[],[],0,0,0⟩,[]⟩,
  ⟨[⟨ty,7⟩,⟨ty,0⟩,⟨ty,0⟩],[⟨0,true⟩],0,2,0⟩,[.scalar 0],2,0⟩
example := bind_values initial ty [4,3,1] (by
  intro value member
  simp at member
  rcases member with rfl | rfl | rfl <;> decide +kernel)
#guard (bindSavedAll initial (valueArguments ty [4,3,1])).isSome
def out := (bindSavedAll initial (valueArguments ty [4,3,1])).getD initial
#guard out.scalars.memory.map (·.value) == [7,0,0,4,3,1]
#guard out.scalars.bindings == [⟨0,true⟩,⟨3,true⟩,⟨4,true⟩,⟨5,true⟩]
#guard out.slots == [.scalar 0,.scalar 1,.scalar 2,.scalar 3]
#guard out.scope == 2 && out.scalars.baseMemory == 2
#guard (bindSavedAll initial (valueArguments ty [2147483648])).isNone
end ValueArgumentExamples
'''

RECEIVER_CHECKS = r'''

namespace ReceiverLayoutExamples
open Proofs.CppMoveReceiverLayout Proofs.CppMoveContext Proofs.CppNestedCall
open Proofs.CppMoveCallBindings UfMoveCallExamples

-- Derive all five callee scalar layouts from actual argument resolution.

namespace root
def program := Proofs.UnionFindCandidateInstance.UnionFind_root
def arguments : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)]
def saved := receiverArguments ⟨1,true⟩ ty 2 true [4,3]
def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments = some (resolved.1,saved) := by
  have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := prepareArguments_receiver moved.1 resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
  [4,3] (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
  program.parameters arguments resolvedRun
end root

namespace same
def program := Proofs.UnionFindCandidateInstance.UnionFind_same
def arguments : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)]
def saved := receiverArguments ⟨1,true⟩ ty 2 true [4,3,1]
def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments = some (resolved.1,saved) := by
  have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := prepareArguments_receiver moved.1 resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
  [4,3,1] (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
  program.parameters arguments resolvedRun
end same

namespace size
def program := Proofs.UnionFindCandidateInstance.UnionFind_size
def arguments : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)]
def saved := receiverArguments ⟨1,true⟩ ty 2 true [4,3]
def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments = some (resolved.1,saved) := by
  have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := prepareArguments_receiver moved.1 resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
  [4,3] (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
  program.parameters arguments resolvedRun
end size

namespace unite
def program := Proofs.UnionFindCandidateInstance.UnionFind_unite
def arguments : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)]
def saved := receiverArguments ⟨1,true⟩ ty 2 true [4,3,1]
def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments = some (resolved.1,saved) := by
  have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := prepareArguments_receiver moved.1 resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
  [4,3,1] (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
  program.parameters arguments resolvedRun
end unite

namespace num_groups
def program := Proofs.UnionFindCandidateInstance.UnionFind_num_groups
def arguments : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)]
def saved := receiverArguments ⟨1,true⟩ ty 2 true [4]
def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments = some (resolved.1,saved) := by
  have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
  have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
example := prepareArguments_receiver moved.1 resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
  [4] (by intro value member; simp at member; subst value; decide +kernel)
  program.parameters arguments resolvedRun
end num_groups

-- Actually construct compact success and QS from the generated receiver shape.
example : ∃ prepared initial,
    prepareArguments moved.1 ty root.program.parameters root.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    Proofs.QuotientFrame.QS initial [] prepared.scalars.baseMemory prepared.scope
      prepared.scalars.memory prepared.scalars.bindings
      [.vector 0,.scalar 0,.scalar 1,.scalar 2] := by
  obtain ⟨prepared,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepareArguments_receiver moved.1 root.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) ty 2 true 1 (by decide +kernel) (by decide +kernel)
      [4,3] (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
      root.program.parameters root.arguments root.resolvedRun
  have view : prepared.objects.views[moved.1.objects.views.length]? = some ⟨1,true⟩ := by simp [objects]
  obtain ⟨initial,compacted,qs,frame,oneBinding⟩ := compact_receiver prepared ty _ 2 ⟨1,true⟩ view slots
  exact ⟨prepared,initial,run,compacted,qs⟩

-- Readonly vector/scalar permissions are kept; empty value suffix is legal.
example := prepare_receiver moved.1 ⟨1,false⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (by simp) ty 2 false 1 (by decide +kernel) (by decide +kernel)
  [] (by simp)
def prepared := (prepareSaved moved.1 (receiverArguments ⟨1,false⟩ ty 2 false [])).getD moved.1
#guard prepared.scalars.memory.length == 11
#guard prepared.scalars.bindings == [⟨2,false⟩]
#guard prepared.slots == [.vector 2,.scalar 0]
#guard (project prepared ty).frame.bindings[4]?.map (·.writable) == some false
#guard prepared.scope == moved.1.scope+1
#guard prepared.scalars.baseMemory == moved.1.scalars.baseMemory

-- Repeated argument values use distinct cells, preserving the reference prefix.
def aliasedValues := (prepareSaved moved.1 (receiverArguments ⟨1,true⟩ ty 2 true [1,1])).getD moved.1
#guard aliasedValues.scalars.memory.map (·.value) == [1,4,1,4,0,0,0,0,0,0,0,1,1]
#guard aliasedValues.scalars.bindings == [⟨2,true⟩,⟨11,true⟩,⟨12,true⟩]
#guard aliasedValues.slots == [.vector 2,.scalar 0,.scalar 1,.scalar 2]
#guard (prepareSaved moved.1 (receiverArguments ⟨1,true⟩ ty 999 true [4])).isNone
#guard (prepareSaved moved.1 (receiverArguments ⟨999,true⟩ ty 2 true [4])).isNone
#guard (prepareSaved moved.1 (receiverArguments ⟨1,true⟩ ty 2 true [2147483648])).isNone
#guard (prepareSaved moved.1 (receiverArguments ⟨1,true⟩ ⟨64,true,false⟩ 2 true [4])).isNone

def readonlyHeader : Context := {moved.1 with objects := {moved.1.objects with
  heap := {moved.1.objects.heap with headers := [some ⟨none,0,true,limit⟩,some ⟨some 0,0,false,limit⟩]}}}
#guard (prepareSaved readonlyHeader (receiverArguments ⟨1,true⟩ ty 2 true [4])).isNone
#guard (prepareSaved readonlyHeader (receiverArguments ⟨1,false⟩ ty 2 false [4])).isSome

-- The source object's empty vector after move retains its scalar fields.
example := prepare_receiver moved.1 ⟨0,true⟩ ⟨none,0,true,limit⟩
  (by decide +kernel) (fun h => h) ty 0 true 1 (by decide +kernel) (by decide +kernel)
  [4] (by intro value member; simp at member; subst value; decide +kernel)
end ReceiverLayoutExamples
'''


class MoveReceiverLayoutTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='move-receiver-layout-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveReceiverLayout\n'
                'import Proofs.UfClassCopyBridge\n'
                'import Proofs.UfFieldsSame\nimport Proofs.UfFieldsSize\n'
                'import Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n' + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_values_distinguish_memory_addresses_from_binding_slots(self):
        self.check_lean(VALUE_CHECKS)

    def test_original_methods_prepare_and_compact_from_receiver_fields(self):
        self.check_lean(UF_CHECKS + RECEIVER_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
