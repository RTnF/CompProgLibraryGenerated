"""Ackermann levels, node potentials and actual generated root compression."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfHistoricalRank Proofs.UfPotential
 example (n : Nat) : alpha n ≤ diagonalAlpha n+2 := alpha_diagonal_bound n
 example : ack 2 1 = 5 := by simp
 example : alpha 0 = 0 := by
   have upper : alpha 0 ≤ 0 := alpha_le (by simp)
   omega
 example : alpha 2 = 1 := by
   have upper : alpha 2 ≤ 1 := alpha_le (by simp)
   have cutoff := alpha_spec 2
   by_contra different
   have zero : alpha 2 = 0 := by omega
   rw [zero] at cutoff
   simp at cutoff
 example (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :=
   nodePotential_account n r p positive edge bound
 example (n r p q : Nat) (positive : 0 < r) (edge : r < p) (growth : p ≤ q) (bound : q ≤ n) :=
   nodePotential_parent_mono n r p q positive edge growth bound
 example (n p : Nat) : nodePotential n 0 p = 0 := nodePotential_zero n p
 example (a b : Nat) (positive : 0 < a) (smaller : b ≤ a) := merge_level_upper a b positive smaller
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : History ps rho) (a : Nat) (inside : a < ps.length) :=
   root_call_potential s layout ps count rank rho rep hist a inside
'''

class UnionFindPotentialTests(unittest.TestCase):
    def test_node_potential_and_generated_native_trace(self):
        with tempfile.TemporaryDirectory(prefix='uf-node-potential-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfPotential\n'+trace.HEADER+trace.CALLER_HEADER+
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
