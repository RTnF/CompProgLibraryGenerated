"""Total forest potential on generated methods and a depth-three compression trace."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
DEEP_OPS = [('unite',(0,1)),('unite',(2,3)),('unite',(0,2)),('unite',(4,5)),
            ('unite',(6,7)),('unite',(4,6)),('unite',(0,4)),('root',(7,)),
            ('size',(7,)),('num_groups',()),('same',(0,7))]
EXPECTED = [0,2,0,4,6,4,0,0,8,1,1]
LEAN_OPS = ','.join('.'+('numGroups' if name=='num_groups' else name)+
                    (' '+' '.join(map(str,args)) if args else '') for name,args in DEEP_OPS)
CHECKS = '''
open Proofs.UfPotential Proofs.UfForestPotential Proofs.UfHistoricalRank
 def deepOps : List Operation := [DEEP_OPS]
 theorem deepAllowed : ∀ op ∈ deepOps, op.allowed 8 := by
   intro op member
   simp only [deepOps,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operation.allowed]
 example := constructed_potential_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 8) 8 (by decide)
   rfl rfl rfl deepOps deepAllowed
 example := default_potential_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : History ps rho)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   potential_calls ops s layout ps count rank rho rep hist allowed
 example (n : Nat) : potentialAllowances n deepOps = 7*alpha n := by rw [allowance_count]; rfl
 def mergedRank (i : Nat) : Nat := if i=0 then 1 else 0
 theorem alphaTwo : alpha 2 = 1 := by
   have upper : alpha 2 ≤ 1 := alpha_le (by simp)
   have cutoff := alpha_spec 2
   by_contra different
   have zero : alpha 2 = 0 := by omega
   rw [zero] at cutoff
   simp at cutoff
 theorem mergedPotential : forestPotential [-2,0] mergedRank = 1 := by
   simp [forestPotential,vertexPotential,mergedRank,alphaTwo,nodePotential_zero,List.range_succ]
 example : ¬ forestPotential [-2,0] mergedRank ≤ forestPotential (Proofs.UfClassInvariant.initial 2) (fun _ => 0) := by
   rw [mergedPotential,forest_zero]
   omega
 def built8 : NState := match UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 8)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) with
   | .finished (s,_) => s
   | _ => empty
 #guard (match runCalls (List.replicate deepOps.length 128) deepOps built8 (layoutOf populated) with
   | .finished (s,answers) => answers == [EXPECTED] &&
       s.scalars.memory == [⟨i32,2⟩,⟨i32,9876⟩,⟨i32,1⟩,⟨i32,8⟩] &&
       (s.frame.state.storage.lookup 1).map (·.items) == some ([-8,0,0,2,0,4,0,0].map Value.integer) &&
       s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
       saved.bind s.frame.read == some (-1)
   | _ => false)
'''.replace('DEEP_OPS',LEAN_OPS).replace('EXPECTED',','.join(map(str,EXPECTED)))

class UnionFindForestPotentialTests(unittest.TestCase):
    def test_total_potential_and_deep_generated_native_trace(self):
        with tempfile.TemporaryDirectory(prefix='uf-forest-potential-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfForestPotential\n'+trace.HEADER+trace.CALLER_HEADER+
                trace.STAGE_CHECKS+trace.RECEIVER_CHECKS+trace.CHECKS+CHECKS)
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native = Path(directory)/'native.cpp'
            binary = Path(directory)/'native'
            calls = ''.join(f'std::cout << u.{name}({",".join(map(str,args))}) << " ";' for name,args in DEEP_OPS)
            native.write_text(f'#include "{trace.SOURCE}"\n#include <iostream>\nint main(){{cp::UnionFind u(8);'+
                calls+'std::cout << "\\n";cp::UnionFind d;for(int i=0;i<3;i++) std::cout << d.num_groups() << " ";std::cout << "\\n";}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(native),'-o',str(binary)],check=True)
            output = subprocess.run([str(binary)],check=True,capture_output=True,text=True).stdout
            self.assertEqual(output.splitlines(),[' '.join(map(str,EXPECTED))+' ','0 0 0 '])

if __name__ == '__main__':
    disable_network()
    unittest.main()
