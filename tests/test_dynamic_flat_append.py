"""Flat root append preserves owned layout and carries amortised growth."""
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
namespace cp {int owned(const std::vector<std::vector<int>>&g,int k,int j){
std::vector<int>local;local.push_back(g[k][j]);local.push_back(local[0]);local.emplace_back((int)g.size()+g[k][j]);
return local[0]+local[1]+local[2];}}
'''
INITIAL = '''
 def outerOwned : Proofs.DynamicOwnedState.State := ⟨⟨snapshot state,logical⟩,params,7,3,2⟩
 theorem outerReal : Proofs.DynamicOwnedState.Realizes outerOwned state := ⟨realizes,by decide +kernel,by decide +kernel,rfl⟩
 def entered : NState := {state with scope := 3}
 def owned0 := Proofs.DynamicOwnedCleanup.enter outerOwned
 theorem real0 : Proofs.DynamicOwnedState.Realizes owned0 entered := Proofs.DynamicOwnedCleanup.enter_real outerOwned state outerReal
 def emptyStmt : NStmt := .declareVector i32 true
 def owned1 := (Proofs.DynamicOwnedState.runConstruct emptyStmt owned0).getD owned0
 def actual1 := ((emptyStmt.run entered).getD ⟨entered,none,false⟩).state
 theorem real1 : Proofs.DynamicOwnedState.Realizes owned1 actual1 := by
   obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned0 entered real0 emptyStmt owned1 (by cbv)
   have same : actual1 = out := by simp [actual1,ran]
   rw [same]; exact real
 def firstValue : NExpr := rowRead
 def selfValue : NExpr := .read i32 (.local 5) (.literal i32 0)
 def lastValue : NExpr := combined
'''

class DynamicFlatAppendTests(unittest.TestCase):
    def test_flat_growth_general_values_limits_and_cleanup(self):
        checks = fixture_checks()+[INITIAL]
        for step, value in enumerate(['firstValue', 'selfValue', 'lastValue']):
            before, after = step+1, step+2
            checks += [f'def stmt{after} : NStmt := .append (.local 5) i32 {value}',
                f'def owned{after} := (Proofs.DynamicOwnedAppend.run stmt{after} owned{before}).getD owned{before}',
                f'theorem pure{after} : Proofs.DynamicOwnedAppend.run stmt{after} owned{before} = some owned{after} := by cbv',
                f'theorem available{after} (s : NState) (room : Proofs.DynamicAppendAuto.RootRoom s 7) : Proofs.DynamicOwnedAppend.Available owned{before} s stmt{after} := by',
                '  intro p selected',
                f'  have chosen : Proofs.DynamicStmt.mutableRoot owned{before}.params owned{before}.core 5 atom = some (Proofs.DynamicOwnedState.newParameter owned0 atom true) := by decide +kernel',
                '  have same : p = Proofs.DynamicOwnedState.newParameter owned0 atom true := Option.some.inj (selected.symm.trans chosen)',
                '  subst p; exact room',
                f'theorem room{after} : Proofs.DynamicAppendAuto.RootRoom actual{before} 7 := ⟨(actual{before}.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                f'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned{before} s) (room : Proofs.DynamicAppendAuto.RootRoom s 7) := Proofs.DynamicOwnedRuns.Runs.append owned{before} s real stmt{after} owned{after} pure{after} (available{after} s room)',
                f'example := Proofs.DynamicFlatAppend.execute owned{before} actual{before} real{before} 5 i32 (Proofs.DynamicOwnedState.newParameter owned0 atom true) (by decide +kernel) 3 {"[]" if step == 0 else "[-3]" if step == 1 else "[-3,-3]"} (by decide +kernel) {value} {"(-3)" if step < 2 else "1"} (by decide +kernel) (by decide +kernel) (actual{before}.frame.state.storage.lookup 7 |>.getD ⟨0,[],0,64,0⟩) (by decide +kernel) (by decide +kernel)',
                f'def actual{after} := ((stmt{after}.run actual{before}).getD ⟨actual{before},none,false⟩).state',
                f'theorem real{after} : Proofs.DynamicOwnedState.Realizes owned{after} actual{after} := by',
                f'  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned{before} actual{before} real{before} stmt{after} owned{after} pure{after} (available{after} actual{before} room{after})',
                f'  have same : actual{after} = out := by simp [actual{after},ran]',
                '  rw [same]; exact real',
                f'#guard owned{after}.nextOwner == 8 && owned{after}.nextBinding == 4 && owned{after}.scope == 3',
                f'#guard actual{after}.frame.bindings == actual1.frame.bindings',
                f'#guard actual{after}.frame.state.storage.objects.length == 8',
                f'#guard (actual{after}.frame.state.storage.lookup 0) == (state.frame.state.storage.lookup 0) && (actual{after}.frame.state.storage.lookup 4) == (state.frame.state.storage.lookup 4) && (actual{after}.frame.state.storage.lookup 2) == (state.frame.state.storage.lookup 2)']
        checks += ['#guard owned4.core.contents 7 == some (.flat i32 3 [-3,-3,1])',
            '#guard [actual1,actual2,actual3,actual4].map (fun s => (s.frame.state.storage.lookup 7).map (·.capacity)) == [some 0,some 1,some 2,some 4]',
            'def restored := (Proofs.DynamicOwnedCleanup.leave outerOwned owned4).getD outerOwned',
            'theorem pureLeave : Proofs.DynamicOwnedCleanup.leave outerOwned owned4 = some restored := by cbv',
            'example := Proofs.DynamicOwnedCleanup.sound outerOwned owned4 restored state actual4 outerReal real4 none pureLeave',
            'def cleaned := Proofs.DynamicOwnedScope.left state actual4',
            'theorem cleanReal : Proofs.DynamicOwnedState.Realizes restored cleaned := (Proofs.DynamicOwnedCleanup.sound outerOwned owned4 restored state actual4 outerReal real4 none pureLeave).2.1',
            '#guard restored.nextOwner == 8 && restored.nextBinding == 3 && (cleaned.frame.state.storage.lookup 7).isNone',
            'def nextOwned := (Proofs.DynamicOwnedState.runConstruct emptyStmt restored).getD restored',
            'example := Proofs.DynamicOwnedConstruct.sound restored cleaned cleanReal emptyStmt nextOwned (by cbv)',
            '#guard nextOwned.nextOwner == 9 && nextOwned.params.map (·.owner) == [0,0,2,8]',
            'def readonlyOwned := (Proofs.DynamicOwnedState.runConstruct (.declareVector i32 false) owned0).getD owned0',
            '#guard (Proofs.DynamicOwnedAppend.run stmt2 readonlyOwned).isNone',
            '#guard (Proofs.DynamicOwnedAppend.run (.append (.local 0) i32 rowRead) owned1).isNone',
            '#guard (Proofs.DynamicOwnedAppend.run (.append (.local 5) i32 (.literal ⟨64,false,false⟩ 2147483648)) owned1).isNone',
            'def tightBuffer := {(actual1.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩ with limit := 0}',
            'def tight : NState := {actual1 with frame.state.storage.objects := actual1.frame.state.storage.objects.set 7 (some tightBuffer)}',
            '#guard tight.frame.state.wellFormed && (stmt2.run tight).isNone',
            'example : ¬ Proofs.DynamicAppendAuto.RootRoom tight 7 := by',
            '  intro ⟨old,found,room⟩',
            '  have lookup : tight.frame.state.storage.lookup 7 = some tightBuffer := by decide +kernel',
            '  have same : old = tightBuffer := Option.some.inj (found.symm.trans lookup)',
            '  subst old',
            '  have limit : tightBuffer.limit = 0 := rfl',
            '  omega']
        with tempfile.TemporaryDirectory(prefix='dynamic-flat-append-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'FlatAppendSource')
            checks[0] = 'import Proofs.DynamicOwnedRuns\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['def call := FlatAppendSource.owned.callFuel 600 state [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match call with | .finished (s,.scalar x) => x == -5 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && s.frame.state.storage.objects.length == 8 && (s.frame.state.storage.lookup 7).isNone | _ => false)']
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::cout<<cp::owned(g,1,1)<<" "<<g.size()<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['-5 4'])

if __name__ == '__main__':
    disable_network(); unittest.main()
