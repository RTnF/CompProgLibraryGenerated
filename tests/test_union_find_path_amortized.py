"""Actual root-call work on exact paths, with forest amortized potential."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
import test_union_find_forest_potential as forest
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfPathAmortized Proofs.UfPotential Proofs.UfForestPotential Proofs.UfHistoricalRank
example : Trace [-8,0,0,2,0,4,4,6] 7 0 [7,6,4] :=
  .step 7 6 0 [6,4] (by decide) (.step 6 4 0 [4] (by decide)
    (.step 4 0 0 [] (by decide) (.done 0 (-8) (by decide) (by decide))))
example : Trace [-1] 0 0 [] := .done 0 (-1) (by decide) (by decide)
example (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (rep : Represents s layout ps count rank)
    (hist : History ps rho) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ root : Nat, ∃ vec,
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s (arguments layout ++ [.value (.literal i32 a)]) =
        .finished (out,.scalar (root : Int)) ∧
      Proofs.UfCompression.Compressed ps vec a root ∧ Represents out layout vec count rank ∧ History vec rho ∧
      out.work+91*forestPotential vec rho ≤ s.work+91*forestPotential ps rho+324*(alpha ps.length+1) :=
  root_amortized s layout ps count rank rho rep hist a inside
example (n : Nat) : alpha n+1 ≤ 3*(diagonalAlpha n+1) := alpha_positive_unit n
 def merged8 : NState := match runCalls (List.replicate 7 128) (deepOps.take 7) built8 (layoutOf populated) with
   | .finished (s,_) => s
   | _ => empty
 def root7 : NState := match Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 128 merged8
     (arguments (layoutOf populated) ++ [.value (.literal i32 7)]) with
   | .finished (s,_) => s
   | _ => empty
 #guard (merged8.frame.state.storage.lookup 1).map (·.items) ==
   some ([-8,0,0,2,0,4,4,6].map Value.integer)
 #guard (match Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 128 merged8
     (arguments (layoutOf populated) ++ [.value (.literal i32 7)]) with
   | .finished (s,.scalar root) => root == 0 && s.work ≤ merged8.work+91*3+142
   | _ => false)
 #guard (match Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 128 root7
     (arguments (layoutOf populated) ++ [.value (.literal i32 7)]) with
   | .finished (s,.scalar root) => root == 0 && s.work ≤ root7.work+91+142
   | _ => false)
 #guard (match Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 128 root7
     (arguments (layoutOf populated) ++ [.value (.literal i32 0)]) with
   | .finished (s,.scalar root) => root == 0 && s.work ≤ root7.work+142
   | _ => false)
'''

class UnionFindPathAmortizedTests(unittest.TestCase):
    def test_actual_work_deep_compressed_and_root_paths(self):
        with tempfile.TemporaryDirectory(prefix='uf-path-amortized-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfPathAmortized\n'+trace.HEADER+trace.CALLER_HEADER+
                trace.STAGE_CHECKS+trace.RECEIVER_CHECKS+trace.CHECKS+forest.CHECKS+CHECKS)
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native = Path(directory)/'native.cpp'
            binary = Path(directory)/'native'
            merges = ''.join(f'u.unite({a},{b});' for _,(a,b) in forest.DEEP_OPS[:7])
            native.write_text(f'#include "{trace.SOURCE}"\n#include <iostream>\nint main(){{cp::UnionFind u(8);'+
                merges+'std::cout << u.root(7) << " " << u.root(7) << " " << u.root(0) << "\\n";'+
                'cp::UnionFind v(1);std::cout << v.root(0) << " " << v.size(0) << "\\n";}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(native),'-o',str(binary)],check=True)
            output = subprocess.run([str(binary)],check=True,capture_output=True,text=True).stdout
            self.assertEqual(output.splitlines(),['0 0 0','0 1'])

if __name__ == '__main__':
    disable_network()
    unittest.main()
