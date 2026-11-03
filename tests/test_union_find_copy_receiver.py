"""UF copies own fresh fields, preserve both receivers, and run generated methods."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE
from test_union_find_constructed_receiver import CHECKS as RECEIVER
from test_union_find_receiver_trace import CHECKS as TRACE, OPS, EXPECTED
from test_union_find_rank_doubling import CHECKS as RANK
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent

CHECKS = r'''
open Proofs.UfCopyFields Proofs.UfCopyReceiver Proofs.UfBalancedReceiver
 def copied := (copyReceiver built (layoutOf populated)).getD (empty,layoutOf empty)
 def duplicate := copied.1
 def duplicateLayout := copied.2
 #guard copied.2 == layoutOf built
 theorem copyActual : copyReceiver built (layoutOf populated) = some (duplicate,duplicateLayout) := by decide +kernel
 def both := actual_copy_strong built duplicate (layoutOf populated) duplicateLayout
   (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong copyActual
 theorem duplicateStrong : Strong duplicate duplicateLayout (List.replicate 4 (-1)) 4 (fun _ => 0) := both.2.2
 #guard duplicateLayout.owner != (layoutOf populated).owner
 #guard duplicateLayout.vectorBinding != (layoutOf populated).vectorBinding
 #guard duplicate.scalarCell duplicateLayout.countSlot i32 == some (⟨built.scalars.memory.length,true⟩,⟨i32,4⟩)
 #guard duplicate.scalarCell duplicateLayout.nSlot i32 == some (⟨built.scalars.memory.length+1,true⟩,⟨i32,4⟩)
 #guard duplicate.scalars.memory.take built.scalars.memory.length == built.scalars.memory
 #guard duplicate.scalars.bindings.take built.scalars.bindings.length == built.scalars.bindings
 #guard duplicate.frame.state.storage.lookup (layoutOf populated).owner == built.frame.state.storage.lookup (layoutOf populated).owner
 #guard duplicate.work == built.work+8
 #guard duplicate.frame.state.liveSpace == built.frame.state.liveSpace+5
 #guard duplicate.scalars.memory.length == built.scalars.memory.length+2
 #guard duplicate.scalars.bindings.length == built.scalars.bindings.length+2
 def copiedRun := runCalls (List.replicate mixed.length 128) mixed duplicate duplicateLayout
 #guard (match copiedRun with
   | .finished (out,answers) => answers == [4,0,2,0,2,0,0,1,4,1,0,1] &&
     out.frame.state.storage.lookup (layoutOf populated).owner == built.frame.state.storage.lookup (layoutOf populated).owner &&
     out.scalarCell (layoutOf populated).countSlot i32 == built.scalarCell (layoutOf populated).countSlot i32 &&
     out.scalarCell (layoutOf populated).nSlot i32 == built.scalarCell (layoutOf populated).nSlot i32 &&
     out.work ≤ built.work+8+mixed.length*Proofs.UfTraceWork.budget 4
   | _ => false)
 example := copy_calls mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
 example := Proofs.UfTraceWork.calls_work mixed duplicate duplicateLayout (List.replicate 4 (-1)) 4
   (fun _ => 0) duplicateStrong mixedAllowed
 example := copy_calls mixed duplicate duplicateLayout (List.replicate 4 (-1)) 4 (fun _ => 0) duplicateStrong mixedAllowed
 example := copy_strong duplicate duplicateLayout (List.replicate 4 (-1)) 4 (fun _ => 0) duplicateStrong
 #guard (copyReceiver built {layoutOf populated with countSlot := 999}).isNone
 #guard (copyReceiver built {layoutOf populated with nSlot := 999}).isNone
 #guard (copyReceiver built {layoutOf populated with vectorSlot := 999}).isNone
 def readonly : NState := {built with
   scalars := {built.scalars with bindings := built.scalars.bindings.map (fun binding => {binding with writable := false})}
   frame := {built.frame with bindings := built.frame.bindings.map (fun binding => {binding with writable := false})}}
 def constCopy := (copyReceiver readonly (layoutOf populated)).getD (empty,layoutOf empty)
 #guard (copyReceiver readonly (layoutOf populated)).isSome
 #guard (constCopy.1.scalarCell constCopy.2.countSlot i32).map (fun pair => (pair.1.writable,pair.2.value)) == some (true,4)
 #guard (constCopy.1.scalarCell constCopy.2.nSlot i32).map (fun pair => (pair.1.writable,pair.2.value)) == some (true,4)
 #guard (constCopy.1.frame.resolve constCopy.2.vectorBinding (.integer i32)).map (fun pair => pair.1.writable) == some true
 #guard (constCopy.1.frame.resolve (layoutOf populated).vectorBinding (.integer i32)).map (fun pair => pair.1.writable) == some false
 example (s : NState) (f : Frame) (count n : Int) (slot : Nat) (ty : Ty)
   (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
   (found : s.scalarCell slot ty = some (binding,cell)) := fields_old_scalar s f count n slot ty binding cell found
 example (s : NState) (f : Frame) (count n : Int) (slot index : Nat)
   (found : s.vectorSlot slot = some index) := fields_old_vector s f count n slot index found
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Strong s layout ps count rank) := copy_strong s layout ps count rank strong
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int)
   (rank : Nat → Nat) (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   copy_calls ops s layout ps count rank strong allowed
 example : ∃ defaultState, ∃ out, copyReceiver defaultState (layoutOf populated) = some (out,layoutOf defaultState) ∧
   Strong out (layoutOf defaultState) [] 0 (fun _ => 0) := by
   obtain ⟨defaultState,_,strong⟩ := Proofs.UfBalancedReceiver.construct_default populated noHeap
     (by decide +kernel) (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   obtain ⟨out,ran,_,post⟩ := copy_strong defaultState (layoutOf populated) [] 0 (fun _ => 0) strong
   exact ⟨defaultState,out,ran,post⟩
'''

class UnionFindCopyTests(unittest.TestCase):
    def test_fields_invariants_and_generated_calls(self):
        source='import Proofs.UfCopyReceiver\n'+HEADER+CALLER_HEADER+STAGE+RECEIVER+TRACE+RANK+CHECKS
        with tempfile.TemporaryDirectory(prefix='uf-copy-receiver-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text(source)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_original_candidate_const_source_and_copy_operations(self):
        check_compiler()
        native=['#include "experiments/library/cpp/template/small_template.hpp"',
            'namespace legacy {', '#include "experiments/library/cpp/union_find/union_find.hpp"', '}',
            '#include "experiments/verification/data_structure/union_find.hpp"',
            'template<class U> void exercise(){U source(4);const U& input=source;U copied(input);']
        for (method,args),expected in zip(OPS,EXPECTED):
            arguments=','.join(map(str,args))
            native.append(f'assert(copied.{method}({arguments})=={expected});')
        native+=['assert(source._ps==std::vector<int>(4,-1));assert(source._num_groups==4 && source._n==4);',
            'assert((copied._ps==std::vector<int>{-4,0,0,0}));assert(copied._num_groups==1 && copied._n==4);',
            'U empty; const U& emptyInput=empty; U emptyCopy(emptyInput);assert(emptyCopy.num_groups()==0);}',
            'int main(){exercise<legacy::UnionFind>();exercise<cp::UnionFind>();}']
        with tempfile.TemporaryDirectory(prefix='uf-copy-native-') as directory:
            path=Path(directory)/'checks.cpp';path.write_text('\n'.join(native))
            executable=Path(directory)/'checks'
            result=subprocess.run(['g++',*FLAGS,'-I',str(ROOT),'-I',str(ROOT/'experiments/library/cpp'),'-fno-access-control',
                '-fsanitize=undefined','-fno-sanitize-recover=all',str(path),'-o',str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            result=subprocess.run([str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
