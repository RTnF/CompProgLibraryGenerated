"""Global rank populations on generated UF methods and arbitrary finite calls."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfHistoricalRank Proofs.UfRankPopulation Proofs.UfGlobalPopulation
 example := constructed_global_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide)
   rfl rfl rfl mixed mixedAllowed
 example := global_calls mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) (fun _ => 0) builtRep (initial_population_history 4) (by simpa using mixedAllowed)
 example := default_global_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : HistoryWithPopulation ps rho)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   global_calls ops s layout ps count rank rho rep hist allowed
 example : ∃ (fuels : List Nat) (out : NState) (vec : List Int) (rho : Nat → Nat) (answers : List Int),
     runCalls fuels mixed built (layoutOf populated) = .finished (out,answers) ∧
     ∀ k, globalCount vec rho k * 2^k ≤ 8 := by
   obtain ⟨fuels,out,vec,count,rank,rho,answers,ran,rep,hist,glob,length,fl,al⟩ :=
     global_calls mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
       (fun _ => 0) (fun _ => 0) builtRep (initial_population_history 4) (by simpa using mixedAllowed)
   refine ⟨fuels,out,vec,rho,answers,ran,?_⟩
   intro k
   have bound := glob k
   rw [length] at bound
   exact bound
 def badGlobalParents : List Int := [-8,0,0,0,0,0,0,0]
 def badGlobalRank (i : Nat) : Nat := if i=0 then 3 else 2
 theorem globalPointwiseHistory : History badGlobalParents badGlobalRank := by
   constructor
   · intro i p found
     by_cases inside : i < 8
     · rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
       · simp [badGlobalParents] at found
       all_goals
         simp [badGlobalParents] at found
         have zero : p=0 := by omega
         subst p
         decide
     · have absent : badGlobalParents[i]? = none := List.getElem?_eq_none_iff.mpr (by change 8 ≤ i; omega)
       rw [absent] at found
       contradiction
   · intro i w found negative
     by_cases inside : i < 8
     · rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
       · simp [badGlobalParents] at found
         have eq : w = -8 := by omega
         subst w
         rfl
       all_goals simp [badGlobalParents] at found; omega
     · have absent : badGlobalParents[i]? = none := List.getElem?_eq_none_iff.mpr (by change 8 ≤ i; omega)
       rw [absent] at found
       contradiction
 theorem pointwiseDoesNotGiveGlobal : ¬ GlobalPopulation badGlobalParents badGlobalRank := by
   intro population
   have bound := population 2
   change (32 : Nat) ≤ 16 at bound
   omega
'''

class UnionFindGlobalPopulationTests(unittest.TestCase):
    def test_global_population_and_generated_native_trace(self):
        with tempfile.TemporaryDirectory(prefix='uf-global-population-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfGlobalPopulation\n'+trace.HEADER+trace.CALLER_HEADER+
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
