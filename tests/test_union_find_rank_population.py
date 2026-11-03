"""Component rank populations on generated UF methods and arbitrary finite calls."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfHistoricalRank Proofs.UfRankPopulation Proofs.UfPopulationTrace
 example := constructed_population_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide)
   rfl rfl rfl mixed mixedAllowed
 example := population_calls mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) (fun _ => 0) builtRep (initial_population_history 4) (by simpa using mixedAllowed)
 example := default_population_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : HistoryWithPopulation ps rho)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   population_calls ops s layout ps count rank rho rep hist allowed

 def badParents : List Int := [-4,0,0,0]
 def badRank (i : Nat) : Nat := if i=0 then 2 else 1
 theorem pointwiseHistory : History badParents badRank := by
   constructor
   · intro i p found
     by_cases inside : i < 4
     · rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl
       · simp [badParents] at found
       all_goals
         simp [badParents] at found
         have zero : p=0 := by omega
         subst p
         decide
     · have absent : badParents[i]? = none := List.getElem?_eq_none_iff.mpr (by change 4 ≤ i; omega)
       rw [absent] at found
       contradiction
   · intro i w found negative
     by_cases inside : i < 4
     · rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl
       · simp [badParents] at found
         have eq : w = -4 := by omega
         subst w
         rfl
       all_goals simp [badParents] at found; omega
     · have absent : badParents[i]? = none := List.getElem?_eq_none_iff.mpr (by change 4 ≤ i; omega)
       rw [absent] at found
       contradiction
 theorem pointwiseDoesNotGivePopulation : ¬ Population badParents badRank := by
   classical
   intro population
   have mems : Proofs.UfClassInvariant.members badParents 0 = [0,1,2,3] := by
     unfold Proofs.UfClassInvariant.members
     change (List.range 4).filter (fun i => decide (Proofs.UfRootCall.Reach badParents i 0)) = List.range 4
     apply List.filter_eq_self.mpr
     intro i member
     simp only [decide_eq_true_eq]
     have inside := List.mem_range.mp member
     rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl
     · exact Proofs.UfRootCall.Reach.refl _
     all_goals exact Proofs.UfRootCall.Reach.step _ 0 0 (by rfl) (.refl 0)
   have bound := population 0 (-4) (by decide +kernel) (by decide) 1
   simp only [highCount,count,mems] at bound
   have budget : Budget 4 4 2 := by simpa [badRank] using bound
   have impossible := budget.2 (by decide)
   omega
'''

class UnionFindRankPopulationTests(unittest.TestCase):
    def test_population_and_generated_native_trace(self):
        with tempfile.TemporaryDirectory(prefix='uf-rank-population-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfPopulationTrace\n'+trace.HEADER+trace.CALLER_HEADER+
                trace.STAGE_CHECKS+trace.RECEIVER_CHECKS+trace.CHECKS+CHECKS)
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native = Path(directory)/'native.cpp'
            binary = Path(directory)/'native'
            calls = ''.join(f'std::cout << u.{name}({",".join(map(str,args))}) << " ";' for name,args in trace.OPS)
            native.write_text(f'#include "{trace.SOURCE}"\n#include <iostream>\nint main(){{cp::UnionFind u(4);'+
                calls+'std::cout << "\\n";cp::UnionFind d;for(int i=0;i<3;i++) std::cout << d.num_groups() << " ";std::cout << "\\n";}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(native),'-o',str(binary)],check=True)
            output = subprocess.run([str(binary)],check=True,capture_output=True,text=True).stdout
            self.assertEqual(output.splitlines(),[' '.join(map(str,trace.EXPECTED))+' ','0 0 0 '])

if __name__ == '__main__':
    disable_network()
    unittest.main()
