"""Audited implicit class move assignment generation and its Context evaluator."""
from pathlib import Path
import hashlib
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
from class_move import audit_class_move, emit_class_move_assignment
from test_scalar_ir import lean_environment
from check_public import check_compiler
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from offline import disable_network
SOURCE=ROOT/'experiments/verification/data_structure/union_find.hpp'
MIXED_SOURCE = """#include <vector>
namespace renamed {struct Packet {std::vector<long long> data;unsigned int count;long stamp;bool marked;};}
"""

CHECKS = r'''

namespace ClassMoveExamples
open Proofs.CppMoveClass Proofs.CppMoveContext Proofs.CppMoveHeaders
open Proofs.CppScalar Proofs.CppConstructorFinish

def ty : Ty := ⟨64,true,false⟩
def scalarContext : Context := ⟨⟨⟨[],[],[],0,0,0⟩,[]⟩,
  ⟨[⟨ty,3⟩,⟨ty,8⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,[.scalar 0,.scalar 1],0,0⟩
def fields : List (Ty × Bool) := [(ty,true),(ty,true)]
def sequenced := (scalarFields scalarContext ty [0,1] [1,0] fields).getD scalarContext
#guard (scalarFields scalarContext ty [0,1] [1,0] fields).isSome
#guard sequenced.scalars.memory.map (·.value) == [8,8]
#guard work sequenced == work scalarContext+4
#guard (scalarFields scalarContext ty [0] [] fields).isNone
#guard (scalarFields scalarContext ty [0] [1] [(ty,false)]).isNone
example := scalarFields_correspondence scalarContext ty [0,1] [1,0] fields
theorem sequenceRun : scalarFields scalarContext ty [0,1] [1,0] fields = some sequenced := by
  have live : (scalarFields scalarContext ty [0,1] [1,0] fields).isSome = true := by decide +kernel
  have nonempty : scalarFields scalarContext ty [0,1] [1,0] fields ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty scalarContext).symm
example := scalarFields_effects scalarContext sequenced ty [0,1] [1,0] fields sequenceRun
example := scalarFields_peak scalarContext sequenced ty [0,1] [1,0] fields sequenceRun
#guard sequenced.peak == 5
example := scalarFields_ready scalarContext ty [0,1] [1,0] fields
  ⟨rfl,⟨⟨0,true⟩,⟨ty,3⟩,rfl,rfl⟩,⟨⟨1,true⟩,⟨ty,8⟩,rfl⟩,
    rfl,⟨⟨1,true⟩,⟨ty,8⟩,rfl,rfl⟩,⟨⟨0,true⟩,⟨ty,3⟩,rfl⟩,True.intro⟩

def objectContext : Context := ⟨⟨HeaderMoveExamples.second.1,[⟨0,true⟩,⟨1,true⟩]⟩,
  ⟨[⟨ty,7⟩,⟨ty,8⟩,⟨ty,99⟩,⟨ty,100⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.vector 1,.scalar 2,.scalar 3],0,0⟩
def source : ObjectRef := ⟨0,[1,2]⟩
def target : ObjectRef := ⟨3,[4,5]⟩
def profile : Proofs.CppClassCopy.Profile := ⟨ty,true,fields⟩
def assigned := (assignClass objectContext target source profile).getD (objectContext,target)
#guard (assignClass objectContext target source profile).isSome
#guard assigned.2 == target
#guard assigned.1.objects.heap.header 0 == some ⟨none,1,true,8⟩
#guard assigned.1.objects.heap.header 1 == some ⟨some 0,0,true,8⟩
#guard assigned.1.scalars.memory.map (·.value) == [7,8,7,8]
#guard Proofs.CppMoveHeaders.read assigned.1.objects.heap ty.valid 0 == some 11
#guard work assigned.1 == work objectContext+7
#guard assigned.1.peak == 17

def selfAssigned := (assignClass assigned.1 target target profile).getD (assigned.1,target)
#guard (assignClass assigned.1 target target profile).isSome
#guard selfAssigned.1.scalars.memory == assigned.1.scalars.memory
#guard selfAssigned.1.objects.heap.header 1 == some ⟨none,0,true,8⟩
#guard (Proofs.CppMoveHeaders.read selfAssigned.1.objects.heap ty.valid 0).isNone
#guard work selfAssigned.1 == work assigned.1+8

theorem assignedRun : assignClass objectContext target source profile = some assigned := by
  have live : (assignClass objectContext target source profile).isSome = true := by decide +kernel
  have nonempty : assignClass objectContext target source profile ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (objectContext,target)).symm
example := assignClass_ready objectContext target source profile 1 0
  ⟨1,true⟩ ⟨0,true⟩ ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩
  rfl rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) rfl HeaderMoveExamples.secondUnique
  ⟨rfl,⟨⟨2,true⟩,⟨ty,99⟩,rfl,rfl⟩,⟨⟨0,true⟩,⟨ty,7⟩,rfl⟩,
    rfl,⟨⟨3,true⟩,⟨ty,100⟩,rfl,rfl⟩,⟨⟨1,true⟩,⟨ty,8⟩,rfl⟩,True.intro⟩
example := assignClass_heap objectContext assigned.1 target source assigned.2 profile assignedRun
example := assignClass_no_resurrection objectContext assigned.1 target source assigned.2 profile 999 assignedRun rfl
example := assignClass_invariants objectContext assigned.1 target source assigned.2 profile assignedRun
  HeaderMoveExamples.secondUnique HeaderMoveExamples.secondCovered FrameExamples.initialAllocValid
  WriteExamples.initialGrantBounds SpaceExamples.initialHeadersLive
example := assignClass_metadata objectContext assigned.1 target source assigned.2 profile assignedRun
example := assignClass_resources objectContext assigned.1 target source assigned.2 profile assignedRun
example := assignClass_peak objectContext assigned.1 target source assigned.2 profile assignedRun
end ClassMoveExamples
'''

class ClassMoveIRTests(unittest.TestCase):
    def check_lean(self,text):
        with tempfile.TemporaryDirectory(prefix='class-move-ir-') as directory:
            proof=Path(directory)/'check.lean';proof.write_text(text)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_model_correspondence_success_invariants_and_resources(self):
        self.check_lean('import Proofs.CppMoveClass\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CHECKS)

    def test_original_generated_profile_and_call(self):
        original=SOURCE.read_bytes()
        generated=emit_class_move_assignment(SOURCE,'cp::UnionFind','DraftMoveUF')
        self.assertIn(hashlib.sha256(original).hexdigest(),generated)
        proof=r"""
open Proofs.CppMoveContext Proofs.CppConstructorFinish
example : DraftMoveUF.profile = Proofs.UfClassCopyBridge.profile := rfl
example (s : Context) (target source : ObjectRef) :
  DraftMoveUF.assign s target source = Proofs.CppMoveClass.assignClass s target source Proofs.UfClassCopyBridge.profile := rfl
#guard DraftMoveUF.fieldNames == ["_ps","_num_groups","_n"]
namespace GeneratedMoveExamples
open ClassMoveExamples
def ty32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def before : Context := {objectContext with scalars := {objectContext.scalars with memory := objectContext.scalars.memory.map (fun cell => {cell with type := ty32})}}
def after := (DraftMoveUF.assign before target source).getD (before,target)
#guard (DraftMoveUF.assign before target source).isSome
#guard after.1.scalars.memory.map (·.value) == [7,8,7,8]
#guard work after.1 == work before+7
example (out : Context) (result : ObjectRef) (run : DraftMoveUF.assign before target source = some (out,result)) :
  result = target := DraftMoveUF.result_target before out target source result run
end GeneratedMoveExamples
"""
        self.check_lean('import Proofs.UfClassCopyBridge\n'+generated+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CHECKS+proof)
        self.assertEqual(SOURCE.read_bytes(),original)

    def test_mixed_scalar_types_and_boundary_values(self):
        with tempfile.TemporaryDirectory(prefix='move-mixed-ir-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(MIXED_SOURCE)
            generated=emit_class_move_assignment(source,'renamed::Packet','DraftMixedMove')
            proof=r"""
open Proofs.CppMoveContext Proofs.CppConstructorFinish
namespace MixedMoveExamples
def unsignedTy : Proofs.CppScalar.Ty := ⟨32,false,false⟩
def signedTy : Proofs.CppScalar.Ty := ⟨64,true,false⟩
def boolTy : Proofs.CppScalar.Ty := ⟨1,false,true⟩
def before : Context := ⟨⟨⟨[some ⟨none,0,true,8⟩,some ⟨none,0,true,8⟩],[],[],0,0,0⟩,[⟨0,true⟩,⟨1,true⟩]⟩,
  ⟨[⟨unsignedTy,2^32-1⟩,⟨signedTy,-(2^63)⟩,⟨boolTy,1⟩,⟨unsignedTy,0⟩,⟨signedTy,0⟩,⟨boolTy,0⟩],
    [⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩,⟨4,true⟩,⟨5,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.scalar 2,.vector 1,.scalar 3,.scalar 4,.scalar 5],0,0⟩
def source : ObjectRef := ⟨0,[1,2,3]⟩
def target : ObjectRef := ⟨4,[5,6,7]⟩
def after := (DraftMixedMove.assign before target source).getD (before,target)
#guard DraftMixedMove.profile.scalarFields.map (fun f => f.1.width) == [32,64,1]
#guard DraftMixedMove.fieldNames == ["data","count","stamp","marked"]
#guard (DraftMixedMove.assign before target source).isSome
#guard after.1.scalars.memory.map (·.value) == [2^32-1,-(2^63),1,2^32-1,-(2^63),1]
#guard work after.1 == 8
#guard after.1.peak == 16
end MixedMoveExamples
"""
            self.check_lean(generated+proof)

    def test_namespace_fingerprint_and_unsupported_assignment_rejected(self):
        with self.assertRaisesRegex(ValueError,'namespace'):
            emit_class_move_assignment(SOURCE,'cp::UnionFind','Bad;namespace')
        with tempfile.TemporaryDirectory(prefix='move-generation-reject-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(MIXED_SOURCE)
            def change(*args,**kwargs):
                plan=audit_class_move(*args,**kwargs)
                source.write_text(source.read_text()+'\n// changed after audit\n')
                return plan
            with patch('class_move.audit_class_move',side_effect=change):
                with self.assertRaisesRegex(ValueError,'source changed'):
                    emit_class_move_assignment(source,'renamed::Packet')
            source.write_text('#include <vector>\nstruct Packet {std::vector<int> data;const int count=7;};\n')
            with self.assertRaises(ValueError):emit_class_move_assignment(source,'Packet')

    def test_native_mixed_member_move_and_self_move(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='class-move-ir-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(MIXED_SOURCE+r"""
#include <cassert>
#include <limits>
#include <utility>
int main(){
  renamed::Packet source{{1,2},std::numeric_limits<unsigned int>::max(),std::numeric_limits<long>::min(),true};
  renamed::Packet target{{9},0,0,false};
  auto* reference=&source.data[1];
  target=std::move(source);
  assert(target.data[1]==2 && &target.data[1]==reference && *reference==2);
  assert(target.count==source.count && target.stamp==source.stamp && target.marked==source.marked);
  assert(target.count==std::numeric_limits<unsigned int>::max() && target.stamp==std::numeric_limits<long>::min());
  *reference=42;assert(target.data[1]==42);
  target=std::move(target);
  assert(target.data.empty() && target.data.capacity()==0);
  assert(target.count==std::numeric_limits<unsigned int>::max() && target.stamp==std::numeric_limits<long>::min() && target.marked);
}
""")
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
