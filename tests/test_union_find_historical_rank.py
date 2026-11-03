"""Historical ranks on generated UF methods, arbitrary finite calls and constructors."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfHistoricalRank Proofs.UfHistoricalTrace
 example := constructed_historical_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide)
   rfl rfl rfl mixed mixedAllowed
 example := historical_calls mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) (fun _ => 0) builtRep (initial_history 4) (by simpa using mixedAllowed)
 example := default_historical_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : History ps rho)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   historical_calls ops s layout ps count rank rho rep hist allowed
 example : ¬ History [-2,0] (fun _ => 0) := by
   intro hist
   have impossible := hist.1 1 0 (by decide +kernel)
   change (0 : Nat) < 0 at impossible
   omega
 example : ¬ RootRanks [-4] (fun _ => 0) := by
   intro roots
   have wrong := roots 0 (-4) (by decide +kernel) (by decide)
   change (0 : Nat) = 2 at wrong
   omega
 example (a b : Nat) (positive : 0 < b) (smaller : b ≤ a) := merge_levels a b positive smaller
 example (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (valid : Proofs.UfClassInvariant.Valid ps count rank) (hist : History ps rho)
   (i : Nat) (inside : i < ps.length) := historical_rank_bound valid hist i inside
'''

class UnionFindHistoricalRankTests(unittest.TestCase):
    def test_history_and_generated_native_trace(self):
        with tempfile.TemporaryDirectory(prefix='uf-historical-rank-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfHistoricalTrace\n'+trace.HEADER+trace.CALLER_HEADER+
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
