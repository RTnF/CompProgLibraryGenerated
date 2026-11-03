"""Constructor-to-arbitrary-call invariant and mixed generated/native call traces."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER, SOURCE
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
OPS = [('num_groups',()),('unite',(0,1)),('size',(1,)),('same',(0,2)),('unite',(2,3)),
       ('unite',(1,3)),('root',(3,)),('num_groups',()),('size',(2,)),('same',(0,3)),
       ('unite',(0,3)),('num_groups',())]
EXPECTED = [4,0,2,0,2,0,0,1,4,1,0,1]
CHECKS = '''
open Proofs.UfReceiverState Proofs.UfReceiverTrace
 def mixed : List Operation := [.numGroups,.unite 0 1,.size 1,.same 0 2,.unite 2 3,.unite 1 3,
   .root 3,.numGroups,.size 2,.same 0 3,.unite 0 3,.numGroups]
 theorem mixedAllowed : ∀ op ∈ mixed, op.allowed 4 := by
   intro op member
   simp only [mixed,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operation.allowed]
 example := constructed_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide) rfl rfl rfl mixed mixedAllowed
 def built : NState := match UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 4)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (s,_) => s
   | _ => empty
 theorem builtRep : Represents built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) := by
   obtain ⟨s,ran,rep⟩ := construct_sized populated noHeap (by decide +kernel) (noModels populated)
     (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide) rfl rfl rfl
   have eq : built = s := by
     unfold built
     have execution : UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 4)]
       (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
         .finished (s,Proofs.CppConstructorFinish.reference populated 2) := ran
     rw [execution]
   rwa [eq]
 example := calls_preserve mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0)
   builtRep (by simpa using mixedAllowed)
 def executed := runCalls (List.replicate mixed.length 128) mixed built (layoutOf populated)
 #guard (match executed with
   | .finished (s,answers) => answers == [4,0,2,0,2,0,0,1,4,1,0,1] &&
       s.scalars.memory == [⟨i32,2⟩,⟨i32,9876⟩,⟨i32,1⟩,⟨i32,4⟩] &&
       (s.frame.state.storage.lookup 1).map (·.items) == some ([-4,0,0,0].map Value.integer) &&
       s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
       saved.bind s.frame.read == some (-1)
   | _ => false)
 def defaults : List Operation := [.numGroups,.numGroups,.numGroups]
 theorem defaultsAllowed : ∀ op ∈ defaults, op.allowed 0 := by
   intro op member
   simp [defaults] at member
   subst op
   trivial
 example := default_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 #guard (match UnionFind_construct0.constructFuel 8 populated [] (Proofs.UfConstructionExport.vectorField false)
     (.integer i32) (Proofs.UfConstructionExport.fields false) with
   | .finished (s,_) => match runCalls [32,32,32] defaults s (layoutOf populated) with
     | .finished (_,answers) => answers == [0,0,0]
     | _ => false
   | _ => false)
 #guard runCalls [] mixed built (layoutOf populated) == .fault
 #guard runCalls [0] [.numGroups] built (layoutOf populated) == .exhausted
 #guard runCalls [128] [.root 4] built (layoutOf populated) == .fault
 example : ¬ (Operation.root 4).allowed 4 := by change ¬ (4 < 4); decide
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Represents s layout ps count rank) (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   calls_preserve ops s layout ps count rank rep allowed
 example (c : NState) (h : Proofs.CppRootModel.Heap) (valid : c.frame.state.wellFormed = true)
   (models : Proofs.CppRootModel.HeapModels c.frame.state h)
   (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) (e : NExpr) (n : Nat)
   (endpoint : n = 2147483647) (scalar : e.scalarOnly = true) (ty : e.resultType = i32)
   (value : e.denote (Proofs.CppNestedEval.envOf c) = some (n : Int))
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :=
   constructed_calls c h valid models lengths strict base e n (by omega) scalar ty value ops allowed
'''
class UnionFindReceiverTraceTests(unittest.TestCase):
    def test_class_invariant_and_arbitrary_finite_calls(self):
        with tempfile.TemporaryDirectory(prefix='uf-receiver-trace-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfReceiverTrace\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            calls=''.join(f'std::cout << u.{name}({",".join(map(str,args))}) << " ";' for name,args in OPS)
            native.write_text(f'#include "{SOURCE}"\n#include <iostream>\nint main(){{ cp::UnionFind u(4);'
                +calls+'std::cout << "\\n"; cp::UnionFind d; for(int i=0;i<3;i++) std::cout << d.num_groups() << " "; std::cout << "\\n";}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(native),'-o',str(binary)],check=True)
            native_result=subprocess.run([str(binary)],check=True,capture_output=True,text=True)
            self.assertEqual(native_result.stdout.splitlines(),[' '.join(map(str,EXPECTED))+' ','0 0 0 '])
if __name__ == '__main__':
    disable_network()
    unittest.main()
