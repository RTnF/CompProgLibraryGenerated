"""Scalar writes, loops and early returns compose with owned vector locals."""
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
#include <cassert>
namespace cp {int owned(const std::vector<std::vector<int>>&g,int k,int j){
int answer=0;
{std::vector<std::vector<int>>local((int)g.size()+g[k][j]);const std::vector<int>empty;
std::vector<int>v(g[k].size(),g[k][j]);
for(int i=0;i<(int)v.size();i++){answer+=v[i];}
assert(v.size());
if(g[k][j]<0)return answer;}
return answer+1;
}}
'''

class DynamicOwnedScalarTests(unittest.TestCase):
    def test_generated_scalar_writes_and_scope_returns(self):
        checks = fixture_checks()
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-scalar-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'
            source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'OwnedScalarSource')
            checks[0] = 'import Proofs.DynamicOwnedControl\nimport Proofs.DynamicPrepareExists\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['open Proofs.CppNestedCall', 'def abi := OwnedScalarSource.owned.parameters', 'def body := OwnedScalarSource.owned.body']
            for case, (k, j, want, cursor) in enumerate([(1, 1, -6, 11), (0, 1, 1, 14), (0, 0, 21, 24)]):
                checks += [f'def args{case} : List NArgument := [.vectorReference 1,.value (.literal i32 {k}),.value (.literal i32 {j})]',
                    f'def rs{case} : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 false,.scalar i32 true {k},.scalar i32 true {j}]',
                    f'theorem pureArgs{case} : Proofs.DynamicArguments.resolveAll params ⟨snapshot state,logical⟩ abi args{case} = some rs{case} := by decide +kernel',
                    f'def callee{case} : NState := (prepare state abi args{case}).getD state',
                    f'def calleeParams{case} := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 rs{case}',
                    f'theorem calleeReal{case} : Proofs.DynamicRealizes.Realizes calleeParams{case} (snapshot callee{case}) logical callee{case} := by',
                    f'  obtain ⟨t,ran,real,_⟩ := Proofs.DynamicPrepareExists.prepare params ⟨snapshot state,logical⟩ state realizes abi args{case} rs{case} pureArgs{case}',
                    f'  have same : callee{case} = t := by simp [callee{case},ran]',
                    f'  simpa only [same,calleeParams{case}] using real',
                    f'def owned{case} : Proofs.DynamicOwnedState.State := ⟨⟨snapshot callee{case},logical⟩,calleeParams{case},7,1,3⟩',
                    f'theorem ownedReal{case} : Proofs.DynamicOwnedState.Realizes owned{case} callee{case} := ⟨calleeReal{case},by decide +kernel,by decide +kernel,by decide +kernel⟩',
                    f'def final{case} : Proofs.DynamicOwnedControl.Step := match Proofs.DynamicOwnedControl.runFuel 600 body owned{case} with | .finished p => p | _ => ⟨owned{case},none,false⟩',
                    f'theorem pureBody{case} : Proofs.DynamicOwnedControl.runFuel 600 body owned{case} = .finished final{case} := by cbv',
                    f'def pipeline{case} (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned{case} s) := Proofs.DynamicOwnedControl.sound 600 body owned{case} s real final{case} pureBody{case}',
                    f'def actual{case} : NStep := match Proofs.CppNestedProgram.runFuel 600 body callee{case} with | .finished a => a | _ => ⟨callee{case},none,false⟩',
                    f'theorem finalMatches{case} : Proofs.DynamicOwnedControl.Matches final{case} actual{case} := by',
                    f'  obtain ⟨a,ran,matched⟩ := pipeline{case} callee{case} ownedReal{case}',
                    f'  have same : actual{case} = a := by simp [actual{case},ran]',
                    '  rw [same]; exact matched',
                    f'#guard final{case}.returned == some ({want}) && !final{case}.breaking',
                    f'#guard final{case}.state.nextOwner == {cursor} && final{case}.state.nextBinding == 1 && final{case}.state.scope == 3',
                    f'#guard final{case}.state.params == calleeParams{case}',
                    f'#guard final{case}.state.core.locals.slots.length == 4',
                    f'#guard final{case}.state.core.contents 0 == logical 0 && final{case}.state.core.contents 2 == logical 2',
                    f'#guard (List.range ({cursor}-7)).all (fun n => (final{case}.state.core.contents (7+n)).isNone)',
                    f'#guard actual{case}.state.frame.bindings == callee{case}.frame.bindings',
                    f'#guard actual{case}.state.frame.state.wellFormed',
                    f'def call{case} := OwnedScalarSource.owned.callFuel 600 state args{case}',
                    f'#guard (match call{case} with | .finished (s,.scalar x) => x == ({want}) && s.frame.bindings == state.frame.bindings && s.scalars.memory == state.scalars.memory && (List.range ({cursor}-7)).all (fun n => (s.frame.state.storage.lookup (7+n)).isNone) | _ => false)']
            checks += ['def readonly : NStmt := .declare i32 false (.read i32 (.row (.local 0) atom (.variable i32 1)) (.variable i32 2))',
                'def declaredOwned := (Proofs.DynamicOwnedControl.primitive readonly owned0).getD ⟨owned0,none,false⟩',
                'example := Proofs.DynamicOwnedScalar.sound owned0 callee0 ownedReal0 readonly (by trivial) ⟨declaredOwned.state.core,none⟩ (by cbv)',
                '#guard declaredOwned.state.nextOwner == 7 && declaredOwned.state.nextBinding == 1',
                '#guard (Proofs.DynamicOwnedControl.primitive (.assign 3 i32 (.literal i32 4)) declaredOwned.state).isNone',
                '#guard (Proofs.DynamicOwnedControl.primitive (.check (.literal i32 0)) owned0).isNone',
                '#guard (Proofs.DynamicOwnedControl.primitive (.declare i32 true (.literal ⟨64,false,false⟩ 2147483648)) owned0).isNone',
                'def stopBody : Command := .sequence (.primitive (.ret (.literal i32 123))) (.primitive (.check (.literal i32 0)))',
                'example := Proofs.DynamicOwnedControl.sound 2 stopBody owned0 callee0 ownedReal0 ⟨owned0,some 123,false⟩ (by cbv)',
                'def loopReturn : Command := .whileLoop (.literal i32 1) (.scope (.sequence (.primitive (.declareVector i32 true)) (.primitive (.ret (.literal i32 7)))))',
                'def returnResult : Proofs.DynamicOwnedControl.Step := match Proofs.DynamicOwnedControl.runFuel 5 loopReturn owned0 with | .finished p => p | _ => ⟨owned0,none,false⟩',
                'example := Proofs.DynamicOwnedControl.sound 5 loopReturn owned0 callee0 ownedReal0 returnResult (by cbv)',
                '#guard returnResult.returned == some 7 && returnResult.state.nextOwner == 8 && (returnResult.state.core.contents 7).isNone']
            proof = scratch/'checks.lean'
            proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::cout<<cp::owned(g,1,1)<<" "<<cp::owned(g,0,1)<<" "<<cp::owned(g,0,0)<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy()
            env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['-6 1 21'])

if __name__ == '__main__':
    disable_network()
    unittest.main()
