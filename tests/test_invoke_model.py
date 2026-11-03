"""Validate by-value invocation primitives and generated C++ calls."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
from state_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network


HELPERS = '''namespace cp {
long long bump(long long x) { x += 1ll; return x; }
long long copy(long long x, long long y) { x += 1ll; return y; }
long long constant() { return 8ll; }
long long down(long long n) { while (n > 0ll) { n -= 1ll; } return n; }
}'''

WRAPPERS = '''
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop
namespace InvokeTest
def i64 : Ty := ⟨64,true,false⟩
def bump : StateProgram := ⟨[⟨i64,true,true⟩],i64,
  .scope (.sequence (.invoke [(i64,true)] i64 [.variable i64 0] Helpers.bump.body)
                    (.ret (.variable i64 1)))⟩
def copy : StateProgram := ⟨[⟨i64,true,true⟩,⟨i64,true,true⟩],i64,
  .scope (.sequence (.invoke [(i64,true),(i64,true)] i64
                    [.variable i64 0,.variable i64 1] Helpers.copy.body)
                    (.ret (.variable i64 2)))⟩
def constant : StateProgram := ⟨[],i64,
  .scope (.sequence (.invoke [] i64 [] Helpers.constant.body) (.ret (.variable i64 0)))⟩
def down : LoopProgram := ⟨[⟨i64,true,true⟩],i64,
  .scope (.sequence (.invoke [(i64,true)] i64 [.variable i64 0] Helpers.down.body)
                    (.ret (.variable i64 1)))⟩
end InvokeTest

namespace PreparationTest
open Proofs.CppInvokePreparation
def caller : State := ⟨[⟨InvokeTest.i64,4⟩],[⟨0,true⟩],10,1,3⟩
def parameters : List (Ty × Bool) := Helpers.copy.parameters.map fun p => (p.type,p.writable)
def arguments : List Expr := [.variable InvokeTest.i64 0,.variable InvokeTest.i64 0]
def prepared : State :=
  ⟨[⟨InvokeTest.i64,4⟩,⟨⟨1,false,true⟩,0⟩,⟨InvokeTest.i64,4⟩,⟨InvokeTest.i64,4⟩],
    [⟨2,true⟩,⟨3,true⟩],15,1,5⟩
def completed : Step :=
  ⟨⟨[⟨InvokeTest.i64,4⟩,⟨⟨1,false,true⟩,0⟩,⟨InvokeTest.i64,5⟩,⟨InvokeTest.i64,4⟩],
    [⟨2,true⟩,⟨3,true⟩],21,1,8⟩,some 4,false⟩
example : ∃ result, prepareInvoke caller parameters arguments = some result := by
  exact prepare_of_evaluated caller parameters arguments [⟨4,1⟩,⟨4,1⟩] rfl rfl rfl
example : prepareInvoke caller parameters arguments = some prepared := by rfl
example : runFuel 101 (.invoke parameters InvokeTest.i64 arguments Helpers.copy.body) caller =
    .finished ⟨⟨[⟨InvokeTest.i64,4⟩,⟨InvokeTest.i64,4⟩],[⟨0,true⟩,⟨1,false⟩],22,1,8⟩,none,false⟩ := by
  exact invoke_composed 100 caller prepared parameters InvokeTest.i64 arguments Helpers.copy.body
    completed 4 6 rfl rfl rfl rfl (by decide) rfl
example (extra : Nat) :
    runFuel 101 (.invoke parameters InvokeTest.i64 arguments Helpers.copy.body)
      (Proofs.CppWorkFrame.addWork caller extra) =
    .finished ⟨⟨[⟨InvokeTest.i64,4⟩,⟨InvokeTest.i64,4⟩],[⟨0,true⟩,⟨1,false⟩],22+extra,1,8⟩,none,false⟩ := by
  rw [Proofs.CppWorkFrame.runFuel_addWork]
  rfl
example (extra : Nat) : runFuel 3 Helpers.down.body
    (Proofs.CppWorkFrame.addWork ⟨[⟨InvokeTest.i64,5⟩],[⟨0,true⟩],0,1,2⟩ extra) =
      .exhausted := by
  rw [Proofs.CppWorkFrame.runFuel_addWork]
  rfl
example (extra : Nat) : runFuel 101 Helpers.bump.body
    (Proofs.CppWorkFrame.addWork ⟨[⟨InvokeTest.i64,9223372036854775807⟩],[⟨0,true⟩],0,1,2⟩ extra) =
      .fault := by
  rw [Proofs.CppWorkFrame.runFuel_addWork]
  rfl
end PreparationTest
namespace StorageTest
open Proofs.CppStorageFrame
def before : State := ⟨[⟨InvokeTest.i64,5⟩],[⟨0,true⟩],17,1,1000⟩
def after : Step := ⟨⟨[⟨InvokeTest.i64,0⟩],[⟨0,true⟩],63,1,1000⟩,some 0,false⟩
example : StorageFrame before after.state := by
  exact runFuel_storage 100 Helpers.down.body before after rfl
example : after.state.baseMemory ≤ after.state.memory.length := by
  exact runFuel_base_bound 100 Helpers.down.body before after (by decide) rfl
example (temporaries : Nat) :
    (lowerBase after.state 1).observe temporaries = lowerBase (after.state.observe temporaries) 1 := by
  exact lowerBase_observe after.state 1 temporaries (by decide) (by decide)
def invalid : State := ⟨[⟨InvokeTest.i64,5⟩],[⟨0,true⟩],0,5,0⟩
#guard (lowerBase invalid 2).observe 0 != lowerBase (invalid.observe 0) 2
example : runFuel 100 Helpers.down.body (lowerBase before 1) =
    .finished (Proofs.CppBaseFrame.lowerStepBase after 1) := by
  rw [Proofs.CppBaseFrame.runFuel_lowerBase 100 Helpers.down.body before 1 (by decide) (by decide)]
  rfl
example : runFuel 101
    (.invoke PreparationTest.parameters InvokeTest.i64 PreparationTest.arguments Helpers.copy.body)
    (lowerBase PreparationTest.caller 1) =
    .finished ⟨⟨[⟨InvokeTest.i64,4⟩,⟨InvokeTest.i64,4⟩],[⟨0,true⟩,⟨1,false⟩],22,0,9⟩,none,false⟩ := by
  rw [Proofs.CppBaseFrame.runFuel_lowerBase 101 _ PreparationTest.caller 1 (by decide) (by decide)]
  rfl
example : runFuel 3 Helpers.down.body (lowerBase before 1) = .exhausted := by
  rw [Proofs.CppBaseFrame.runFuel_lowerBase 3 Helpers.down.body before 1 (by decide) (by decide)]
  rfl
example : runFuel 100 Helpers.bump.body
    (lowerBase ⟨[⟨InvokeTest.i64,9223372036854775807⟩],[⟨0,true⟩],0,1,0⟩ 1) = .fault := by
  rw [Proofs.CppBaseFrame.runFuel_lowerBase 100 _ _ 1 (by decide) (by decide)]
  rfl
end StorageTest
namespace UnsignedInvokeTest
open Proofs.FloorSumInvoke Proofs.FloorSumState Proofs.CppInvokePreparation Proofs.FloorSumArithmetic
def caller : State := ⟨[⟨unsigned64,5⟩,⟨unsigned64,7⟩],[⟨0,true⟩,⟨1,true⟩],19,0,10⟩
def arguments : List Expr := [.variable unsigned64 0,.variable unsigned64 1,
  .variable unsigned64 0,.variable unsigned64 1]
example : ∃ work peak : Nat,
    runFuel 837 (.invoke valueParameters unsigned64 arguments
      Proofs.FloorSumUnsignedInstance.floor_sum_unsigned.body) caller =
      .finished ⟨{caller with
        memory := caller.memory ++ [⟨unsigned64,10⟩],
        bindings := caller.bindings ++ [⟨caller.memory.length,false⟩],work := 29+work,peak := peak},none,false⟩ ∧
    work ≤ 4229 ∧ peak ≤ 29 ∧ work ≤ 401 := by
  have sumValue : directSum 7 5 7 5%wordLimit = 10 := by decide
  have logValue : Nat.log2 7 = 2 := by decide
  have result := invoke_correct caller arguments 5 7 5 7 1 1 1 1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [sumValue,logValue,caller,arguments,argumentPeak,callerPrefix,Expr.nodes,State.observe,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
end UnsignedInvokeTest
namespace SignedModInvokeTest
open Proofs.SafeModInvoke Proofs.SafeModFrame Proofs.SafeModProofs Proofs.CppInvokePreparation
def caller : State := ⟨[⟨signed64,-7⟩,⟨signed64,3⟩],[⟨0,true⟩,⟨1,true⟩],19,0,10⟩
def arguments : List Expr := [.variable signed64 0,.variable signed64 1]
example : ∃ peak : Nat,
    runFuel 10 (.invoke valueParameters signed64 arguments Proofs.SafeModInstance.safe_mod.body) caller =
      .finished ⟨{caller with
        memory := caller.memory ++ [⟨signed64,2⟩],
        bindings := caller.bindings ++ [⟨caller.memory.length,false⟩],work := 40,peak := peak},none,false⟩ ∧
    peak ≤ 12 := by
  have result := invoke_correct caller arguments (-7) 3 1 1 rfl
    (by decide) (by decide) (by decide) (by decide)
  simpa [caller,arguments,argumentPeak,callerPrefix,Expr.nodes,State.observe,bodyWork] using result
end SignedModInvokeTest
'''


class InvokeTests(unittest.TestCase):
    def test_native_helpers_caller_aliases_and_fuel(self):
        with tempfile.TemporaryDirectory(prefix='invoke-model-') as directory:
            scratch=Path(directory)
            source=scratch/'helpers.cpp'
            source.write_text(HELPERS)
            generated='import Proofs.FloorSumInvoke\nimport Proofs.CppBaseFrame\nimport Proofs.SafeModInvoke\n'+emit_lean(lower_source(source),'Helpers')
            checks='\n'
            for x in range(-20,21):
                checks+=f'#guard (InvokeTest.bump.call [⟨InvokeTest.i64,{x}⟩] [.reference 0]).map (fun r => (r.value,r.memory.map (·.value))) == some ({x+1},[{x}])\n'
                checks+=f'#guard (InvokeTest.copy.call [⟨InvokeTest.i64,{x}⟩] [.reference 0,.reference 0]).map (fun r => (r.value,r.memory.map (·.value))) == some ({x},[{x}])\n'
            checks+='''
#guard InvokeTest.bump.call [⟨InvokeTest.i64,9223372036854775807⟩] [.reference 0] == none
#guard InvokeTest.constant.call [⟨⟨64,false,false⟩,-1⟩] [] == some ⟨8,[⟨⟨64,false,false⟩,-1⟩],6,3⟩
#guard (match InvokeTest.down.callFuel 60 [⟨InvokeTest.i64,5⟩] [.reference 0] with
 | .finished r => r.value == 0 && r.memory.map (·.value) == [5]
 | _ => false)
#guard InvokeTest.down.callFuel 2 [⟨InvokeTest.i64,5⟩] [.reference 0] == .exhausted
#guard (Stmt.invoke [] InvokeTest.i64 [] .skip).run {memory := [],bindings := []} == none
#guard (Stmt.invoke [] InvokeTest.i64 [] .breakLoop).run {memory := [],bindings := []} == none
#guard runFuel 3 (.invoke [] InvokeTest.i64 [] .breakLoop) {memory := [],bindings := []} == .fault
#guard (Stmt.invoke [] ⟨32,true,false⟩ [] (.ret (.literal InvokeTest.i64 2147483648))).run {memory := [],bindings := []} == none
#guard (Stmt.invoke [(InvokeTest.i64,true)] InvokeTest.i64 [] Helpers.bump.body).run {memory := [],bindings := []} == none
#guard (Stmt.invoke [(InvokeTest.i64,false)] InvokeTest.i64 [.literal InvokeTest.i64 3] Helpers.bump.body).run {memory := [],bindings := []} == none
#guard (Stmt.invoke [] InvokeTest.i64 [.variable InvokeTest.i64 0] Helpers.constant.body).run {memory := [],bindings := []} == none
#guard (Stmt.invoke [(⟨32,true,false⟩,true)] InvokeTest.i64 [.literal InvokeTest.i64 2147483648] Helpers.bump.body).run {memory := [],bindings := []} == none
'''
            lake,env=lean_environment()
            proof=scratch/'test.lean'
            proof.write_text(generated+WRAPPERS+checks)
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            source.write_text(HELPERS.replace('x += 1ll','x += 2ll'))
            changed='import Proofs.FloorSumInvoke\nimport Proofs.CppBaseFrame\nimport Proofs.SafeModInvoke\n'+emit_lean(lower_source(source),'Helpers')
            proof.write_text(changed+WRAPPERS+'\n#guard (InvokeTest.bump.call [⟨InvokeTest.i64,0⟩] [.reference 0]).map (·.value) == some 1\n')
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)
            source.write_text('#include <cassert>\n#include \"number_theory/floor_sum.hpp\"\n'+HELPERS+'''
long long caller(long long &x) { return cp::bump(x); }
long long caller_copy(long long &x,long long &y) { return cp::copy(x,y); }
ll mod_alias(ll &x,ll &m){return safe_mod(x,m);}
ull floor_alias(ull &n,ull &m){return floor_sum_unsigned(n,m,n,m);}
int main(){ll xneg=-7,modulus=3;assert(mod_alias(xneg,modulus)==2);assert(xneg==-7&&modulus==3);ull n=5,m=7;assert(floor_alias(n,m)==10);assert(n==5&&m==7);for(long long x=-20;x<=20;++x) {long long a=x;assert(caller(a)==x+1);assert(a==x);
assert(caller_copy(a,a)==x);assert(a==x);} assert(cp::constant()==8);assert(cp::down(5)==0);}
''')
            binary=scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I'+str(ROOT/'experiments/library/cpp'),str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_cpp_direct_calls_are_generated(self):
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'source.cpp'
            source.write_text(HELPERS+'\nnamespace cp {long long caller(long long x){return bump(x);}}')
            ir=lower_source(source)
            self.assertIn('(.invoke',emit_lean(ir,'Calls'))
            lake,env=lean_environment()
            proof=Path(directory)/'test.lean'
            proof.write_text(emit_lean(ir,'Calls')+'\n#guard (Calls.caller.call [] [.value 3]).map (·.value) == some 4\n')
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.FloorSumInvoke','Proofs.CppBaseFrame','Proofs.SafeModInvoke'],cwd=ROOT,env=env,check=True)
    unittest.main()
