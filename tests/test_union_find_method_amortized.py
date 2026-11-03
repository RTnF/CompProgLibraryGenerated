"""Generated all-method amortized work, including both distinct find paths."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
import test_union_find_receiver_trace as trace
import test_union_find_forest_potential as forest
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
OPS = forest.DEEP_OPS[:7]+[('same',(7,7)),('same',(7,3)),('size',(7,)),
                           ('num_groups',()),('unite',(7,7)),('root',(3,))]
EXPECTED = forest.EXPECTED[:7]+[1,1,8,1,0,0]
CHECKS = '''
open Proofs.UfMethodAmortized Proofs.UfPathAmortized Proofs.UfPotential
open Proofs.UfForestPotential Proofs.UfHistoricalRank
 def workOps : List Operation := [OPS]
 theorem workAllowed : ∀ op ∈ workOps, op.allowed 8 := by
   intro op member
   simp only [workOps,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
     simp [Operation.allowed]
 example := constructed_amortized_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 8) 8 (by decide)
   rfl rfl rfl workOps workAllowed
 example := default_amortized_calls populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank rho : Nat → Nat)
   (rep : Represents s layout ps count rank) (hist : History ps rho)
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
   ∃ fuels out vec nextCount nextRank nextRho answers,
     runCalls fuels ops s layout = .finished (out,answers) ∧
     Represents out layout vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
     out.work+91*forestPotential vec nextRho ≤
       s.work+91*forestPotential ps rho+769*ops.length*(alpha ps.length+1) ∧
     fuels.length = ops.length ∧ answers.length = ops.length :=
   amortized_calls ops s layout ps count rank rho rep hist allowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :=
   same_work_paths s layout ps count rank rep a b ha hb
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (rep : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :=
   unite_work_paths s layout ps count rank rep a b ha hb
 example (n m : Nat) : 769*m*(alpha n+1) ≤ 2307*m*(diagonalAlpha n+1) := diagonal_work_unit n m
 -- The first find has length 3. After its compression the second find of the same node has length 1.
 example : Trace [-8,0,0,2,0,4,4,6] 7 0 [7,6,4] :=
   .step 7 6 0 [6,4] (by decide) (.step 6 4 0 [4] (by decide)
     (.step 4 0 0 [] (by decide) (.done 0 (-8) (by decide) (by decide))))
 example : Trace [-8,0,0,2,0,4,0,0] 7 0 [7] :=
   .step 7 0 0 [] (by decide) (.done 0 (-8) (by decide) (by decide))
 def beforeSame : NState := match runCalls (List.replicate 7 128) (deepOps.take 7) built8 (layoutOf populated) with
   | .finished (s,_) => s
   | _ => empty
 #guard (match call 128 beforeSame (layoutOf populated) (.same 7 7) with
   | .finished (s,.scalar answer) => answer == 1 && s.work ≤ beforeSame.work+91*3+91+223 &&
       (s.frame.state.storage.lookup 1).map (·.items) == some ([-8,0,0,2,0,4,0,0].map Value.integer)
   | _ => false)
 #guard (match call 128 beforeSame (layoutOf populated) (.unite 7 7) with
   | .finished (s,.scalar answer) => answer == 0 && s.work ≤ beforeSame.work+91*3+91+405 &&
       (s.frame.state.storage.lookup 1).map (·.items) == some ([-8,0,0,2,0,4,0,0].map Value.integer)
   | _ => false)
 #guard (match call 128 beforeSame (layoutOf populated) (.size 7) with
   | .finished (s,.scalar answer) => answer == 8 && s.work ≤ beforeSame.work+91*3+162
   | _ => false)
 #guard (match call 128 beforeSame (layoutOf populated) .numGroups with
   | .finished (s,.scalar answer) => answer == 1 && s.work ≤ beforeSame.work+41
   | _ => false)
 #guard (match runCalls (List.replicate workOps.length 128) workOps built8 (layoutOf populated) with
   | .finished (s,answers) => answers == [EXPECTED] && s.work ≤ built8.work+769*workOps.length*4 &&
       s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
       saved.bind s.frame.read == some (-1)
   | _ => false)
'''.replace('OPS',','.join('.'+('numGroups' if name=='num_groups' else name)+
    (' '+' '.join(map(str,args)) if args else '') for name,args in OPS)).replace('EXPECTED',','.join(map(str,EXPECTED)))

class UnionFindMethodAmortizedTests(unittest.TestCase):
    def test_two_paths_all_methods_constructors_and_sequence_work(self):
        with tempfile.TemporaryDirectory(prefix='uf-method-amortized-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfMethodAmortized\n'+trace.HEADER+trace.CALLER_HEADER+
                trace.STAGE_CHECKS+trace.RECEIVER_CHECKS+trace.CHECKS+forest.CHECKS+CHECKS)
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native = Path(directory)/'native.cpp'
            binary = Path(directory)/'native'
            calls = ''.join(f'std::cout << u.{name}({",".join(map(str,args))}) << " ";' for name,args in OPS)
            native.write_text(f'#include "{trace.SOURCE}"\n#include <iostream>\nint main(){{cp::UnionFind u(8);'+
                calls+'std::cout << "\\n";cp::UnionFind v(3);v.unite(0,1);'+
                'std::cout << v.unite(2,0) << " " << v.same(2,1) << " " << v.size(2) << "\\n";'+
                'cp::UnionFind one(1);std::cout << one.same(0,0) << " " << one.unite(0,0) << " " << one.size(0) << "\\n";'+
                'cp::UnionFind empty;std::cout << empty.num_groups() << "\\n";}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(native),'-o',str(binary)],check=True)
            output = subprocess.run([str(binary)],check=True,capture_output=True,text=True).stdout
            self.assertEqual(output.splitlines(),[' '.join(map(str,EXPECTED))+' ','0 1 3','1 0 1','0'])

if __name__ == '__main__':
    disable_network()
    unittest.main()
