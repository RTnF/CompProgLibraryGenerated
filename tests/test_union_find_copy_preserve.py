"""Copy-target histories preserve the original receiver and all pre-copy aliases."""
from pathlib import Path
import subprocess
import tempfile
import unittest
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

CHECKS = r'''
open Proofs.UfCopyPreserve Proofs.UfScalarTrace
 example := copy_calls_both mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
 example := copy_calls_both [] built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong (by simp)
 example := copy_calls_both mixed duplicate duplicateLayout (List.replicate 4 (-1)) 4 (fun _ => 0) duplicateStrong mixedAllowed
 def afterCalls : NState := match copiedRun with | .finished (out,_) => out | _ => empty
 def sourceRef := (built.frame.elementRef (layoutOf populated).vectorBinding i32 3).getD ⟨0,i32,false,⟨0,0,0⟩⟩
 #guard built.frame.read sourceRef == some (-1)
 #guard afterCalls.frame.read sourceRef == some (-1)
 #guard afterCalls.scalarCell (layoutOf populated).countSlot i32 == built.scalarCell (layoutOf populated).countSlot i32
 #guard (afterCalls.scalarCell duplicateLayout.countSlot i32).map (fun pair => pair.2.value) == some 1
 theorem originalAfterStrong : Strong afterCalls (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) := by
   obtain ⟨initial,fuels,out,vec,nextCount,nextRank,answers,copied,ran,old,new,len,fl,al,work,cells,reads⟩ :=
     copy_calls_both mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
   have initEq : initial = duplicate := congrArg Prod.fst (Option.some.inj (copied.symm.trans copyActual))
   subst initial
   rw [←both.1] at ran
   have fixed : runCalls (List.replicate mixed.length 128) mixed duplicate duplicateLayout =
       .finished (afterCalls,[4,0,2,0,2,0,0,1,4,1,0,1]) := by decide +kernel
   have same := Proofs.UfUniformScalarPeak.run_calls_unique mixed fuels (List.replicate mixed.length 128)
     duplicate duplicateLayout (out,answers) (afterCalls,[4,0,2,0,2,0,0,1,4,1,0,1]) ran fixed
   have finalEq : out = afterCalls := congrArg Prod.fst same
   rwa [finalEq] at old
 example := Proofs.UfTraceWork.calls_work mixed afterCalls (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) originalAfterStrong mixedAllowed
 #guard (match runCalls (List.replicate mixed.length 128) mixed afterCalls (layoutOf populated) with
   | .finished (_,answers) => answers == [4,0,2,0,2,0,0,1,4,1,0,1]
   | _ => false)
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   copy_calls_both ops s layout ps count rank strong allowed
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (cb : Proofs.CppState.Binding) (strong : Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length)
   (counter : s.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩)) :=
   calls_work_other ops s layout ps count rank cb strong allowed counter
 example (s out : NState) (slot : Nat) (ty otherTy : Ty) (b next : Proofs.CppState.Binding)
   (c other : Proofs.CppState.Cell) (effects : Proofs.CppCallFrame.CallEffects s out)
   (before : s.scalarCell slot ty = some (b,c)) (after : out.scalarCell slot otherTy = some (next,other)) :=
   binding_same s out slot ty otherTy b next c other effects before after
'''

class CopyPreserveTests(unittest.TestCase):
    def test_original_receiver_and_arbitrary_aliases_after_copy_history(self):
        source='import Proofs.UfCopyPreserve\nimport Proofs.UfUniformScalarPeak\n'+HEADER+CALLER_HEADER+STAGE+RECEIVER+TRACE+RANK+COPY+CHECKS
        with tempfile.TemporaryDirectory(prefix='uf-copy-preserve-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text(source)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
