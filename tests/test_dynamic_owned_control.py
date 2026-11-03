"""Owned locals survive control composition and retire without reusing IDs."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_dynamic_expr import fixture_checks, HEADER
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {void owned(const std::vector<std::vector<int>>&g,int k,int j){
{std::vector<std::vector<int>>local((int)g.size()+g[k][j]);const std::vector<int>empty;const std::vector<int>v(g[k].size(),g[k][j]);}
if(g.size()){std::vector<int>q;}
while(g.size()){std::vector<int>tmp;break;}
}}
'''
CHECKS = '''
open Proofs.CppNestedCall
 def abi := OwnedControlSource.owned.parameters
 def args : List NArgument := [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]
 def rs : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 false,.scalar i32 true 1,.scalar i32 true 1]
 theorem pureArgs : Proofs.DynamicArguments.resolveAll params ⟨snapshot state,logical⟩ abi args = some rs := by decide +kernel
 def callee : NState := (prepare state abi args).getD state
 def calleeParams := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 rs
 theorem calleeReal : Proofs.DynamicRealizes.Realizes calleeParams (snapshot callee) logical callee := by
   obtain ⟨t,ran,real,_⟩ := Proofs.DynamicPrepareExists.prepare params ⟨snapshot state,logical⟩ state realizes abi args rs pureArgs
   have same : callee = t := by simp [callee,ran]
   simpa only [same,calleeParams] using real
 def owned0 : Proofs.DynamicOwnedState.State := ⟨⟨snapshot callee,logical⟩,calleeParams,7,1,3⟩
 theorem ownedReal : Proofs.DynamicOwnedState.Realizes owned0 callee := ⟨calleeReal,by decide +kernel,by decide +kernel,by decide +kernel⟩
 def body := OwnedControlSource.owned.body
 def final : Proofs.DynamicOwnedControl.Step := match Proofs.DynamicOwnedControl.runFuel 600 body owned0 with
   | .finished p => p
   | _ => ⟨owned0,none,false⟩
 theorem pureBody : Proofs.DynamicOwnedControl.runFuel 600 body owned0 = .finished final := by cbv
 def pipeline (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned0 s) := Proofs.DynamicOwnedControl.sound 600 body owned0 s real final pureBody
 def actual : NStep := match Proofs.CppNestedProgram.runFuel 600 body callee with
   | .finished a => a
   | _ => ⟨callee,none,false⟩
 theorem finalMatches : Proofs.DynamicOwnedControl.Matches final actual := by
   obtain ⟨a,ran,matched⟩ := pipeline callee ownedReal
   have same : actual = a := by simp [actual,ran]
   rw [same]; exact matched
 #guard final.state.nextOwner == 13 && final.state.nextBinding == 1 && final.state.scope == 3
 #guard final.state.params == calleeParams
 #guard final.returned.isNone && !final.breaking
 #guard final.state.core.contents 0 == logical 0 && final.state.core.contents 2 == logical 2
 #guard [7,8,9,10,11,12].all (fun n => (final.state.core.contents n).isNone)
 #guard actual.state.frame.state.storage.objects.length == 13
 #guard actual.state.frame.bindings == callee.frame.bindings
 #guard [7,8,9,10,11,12].all (fun n => (actual.state.frame.state.storage.lookup n).isNone)
 #guard actual.state.frame.state.wellFormed
 def nextStmt : NStmt := .declareVector i32 true
 def nextOwned := (Proofs.DynamicOwnedState.runConstruct nextStmt final.state).getD final.state
 example := Proofs.DynamicOwnedConstruct.sound final.state actual.state finalMatches.state nextStmt nextOwned (by cbv)
 #guard nextOwned.nextOwner == 14 && nextOwned.params.map (·.owner) == [0,13]
 def enteredOwned := Proofs.DynamicOwnedCleanup.enter owned0
 def tempOwned := (Proofs.DynamicOwnedState.runConstruct nextStmt enteredOwned).getD enteredOwned
 def restored := (Proofs.DynamicOwnedCleanup.leave owned0 tempOwned).getD owned0
 theorem pureCleanup : Proofs.DynamicOwnedCleanup.leave owned0 tempOwned = some restored := by cbv
 theorem cleanup (returned : Option Int) : ∃ t, callee.leave t (returned.map Ret.scalar) = some (Proofs.DynamicOwnedScope.left callee t) ∧ Proofs.DynamicOwnedState.Realizes restored (Proofs.DynamicOwnedScope.left callee t) ∧ (Proofs.DynamicOwnedScope.left callee t).work = t.work+t.frame.state.destroyWork 4+1 := by
   obtain ⟨t,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound enteredOwned {callee with scope := callee.scope+1} (Proofs.DynamicOwnedCleanup.enter_real owned0 callee ownedReal) nextStmt tempOwned (by cbv)
   exact ⟨t,Proofs.DynamicOwnedCleanup.sound owned0 tempOwned restored callee t ownedReal real returned pureCleanup⟩
 example := cleanup none
 example := cleanup (some 123)
 #guard restored.nextOwner == 8 && restored.nextBinding == 1 && restored.scope == 3
 #guard (restored.core.contents 7).isNone && restored.core.contents 0 == logical 0
 #guard (Proofs.DynamicOwnedCleanup.leave owned0 {tempOwned with nextBinding := 0}).isNone
 #guard (Proofs.DynamicOwnedCleanup.leave owned0 {tempOwned with params := []}).isNone
 #guard (Proofs.DynamicOwnedCleanup.leave owned0 {tempOwned with core.locals.memory := []}).isNone
 def unsupported : Command := .primitive (.write (.local 0) i32 (.literal i32 0) (.literal i32 1))
 #guard (match Proofs.DynamicOwnedControl.runFuel 10 unsupported owned0 with | .fault => true | _ => false)
 #guard (match Proofs.DynamicOwnedControl.runFuel 0 body owned0 with | .exhausted => true | _ => false)
 #guard (match Proofs.DynamicOwnedControl.runFuel 10 (.whileLoop (.literal i32 1) (.primitive .skip)) owned0 with | .exhausted => true | _ => false)
 def bypass : Command := .branch (.literal i32 0) unsupported (.primitive .skip)
 example := Proofs.DynamicOwnedControl.sound 2 bypass owned0 callee ownedReal ⟨owned0,none,false⟩ (by cbv)
 def call := OwnedControlSource.owned.callFuel 600 state args
 #guard (match call with | .finished (s,.unit) => s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,8,9,10,11,12].all (fun owner => (s.frame.state.storage.lookup owner).isNone) | _ => false)
'''

class DynamicOwnedControlTests(unittest.TestCase):
    def test_generated_owned_control_and_cleanup(self):
        checks = fixture_checks()
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-control-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'
            source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'OwnedControlSource')
            checks[0] = 'import Proofs.DynamicOwnedControl\nimport Proofs.DynamicPrepareExists\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            proof = scratch/'checks.lean'
            proof.write_text('\n'.join(checks)+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};cp::owned(g,1,1);std::cout<<g.size()<<" "<<g[1][1]<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy()
            env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['4 -3'])

if __name__ == '__main__':
    disable_network()
    unittest.main()
