"""Owned append tracks fresh children, growth, cleanup and retained tombstones."""
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
namespace cp {int owned(std::vector<std::vector<int>>&g,int k,int j){
std::vector<std::vector<int>>local((int)g.size()+g[k][j]);local.emplace_back();
local[1].push_back(g[k][j]);local[1].push_back(g[k][j]);local[1].push_back(g[k][j]);
g.emplace_back();std::vector<int>later;return (int)local[1].size()+(int)g.size();}}
'''
CHECKS = '''
 def outerOwned : Proofs.DynamicOwnedState.State := ⟨⟨snapshot state,logical⟩,params,7,3,2⟩
 theorem outerReal : Proofs.DynamicOwnedState.Realizes outerOwned state := ⟨realizes,by decide +kernel,by decide +kernel,rfl⟩
 def entered : NState := {state with scope := 3}
 def owned0 := Proofs.DynamicOwnedCleanup.enter outerOwned
 theorem real0 : Proofs.DynamicOwnedState.Realizes owned0 entered := Proofs.DynamicOwnedCleanup.enter_real outerOwned state outerReal
 def rowsStmt : NStmt := .constructRows i32 true combined
 def owned1 := (Proofs.DynamicOwnedState.runConstruct rowsStmt owned0).getD owned0
 theorem construct : Proofs.DynamicOwnedState.runConstruct rowsStmt owned0 = some owned1 := by cbv
 def actual1 := ((rowsStmt.run entered).getD ⟨entered,none,false⟩).state
 theorem real1 : Proofs.DynamicOwnedState.Realizes owned1 actual1 := by
   obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned0 entered real0 rowsStmt owned1 construct
   have same : actual1 = out := by simp [actual1,ran]
   rw [same]; exact real
 def rootStmt : NStmt := .appendRow (.local 5) i32
 def owned2 := (Proofs.DynamicOwnedAppend.run rootStmt owned1).getD owned1
 theorem pureRoot : Proofs.DynamicOwnedAppend.run rootStmt owned1 = some owned2 := by cbv
 theorem rootAvail (s : NState) (room : Proofs.DynamicAppendAuto.RootRoom s 7) : Proofs.DynamicAppendAuto.Available owned1.params owned1.core s rootStmt := by
   intro p selected
   have chosen : Proofs.DynamicStmt.mutableRoot owned1.params owned1.core 5 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned0 (.vector atom) true) := by decide +kernel
   have same : p = Proofs.DynamicOwnedState.newParameter owned0 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)
   subst p; exact room
 theorem rootRoom : Proofs.DynamicAppendAuto.RootRoom actual1 7 := ⟨(actual1.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩
 example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned1 s) (room : Proofs.DynamicAppendAuto.RootRoom s 7) := Proofs.DynamicOwnedAppend.sound owned1 s real rootStmt owned2 pureRoot (rootAvail s room)
 example := Proofs.DynamicOwnedAppend.root_sound owned1 actual1 real1 5 i32 ⟨owned2.core,none⟩ (by cbv) (rootAvail actual1 rootRoom)
 def actual2 := ((rootStmt.run actual1).getD ⟨actual1,none,false⟩).state
 theorem real2 : Proofs.DynamicOwnedState.Realizes owned2 actual2 := by
   obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned1 actual1 real1 rootStmt owned2 pureRoot (rootAvail actual1 rootRoom)
   have same : actual2 = out := by simp [actual2,ran]
   rw [same]; exact real
 def idxNew : NExpr := .binary i32 .sub rowSize (.literal i32 1)
 def childStmt : NStmt := .append (.row (.local 5) atom idxNew) i32 rowRead
'''

def owned_checks():
    checks = fixture_checks()
    # Each availability proof identifies its pure target; only actual room
    # is supplied separately. The state simulation itself remains generic.
    common = CHECKS
    checks.append(common)
    for step in range(3):
        before, after = step+2, step+3
        checks += [f'def owned{after} := (Proofs.DynamicOwnedAppend.run childStmt owned{before}).getD owned{before}',
            f'theorem pure{after} : Proofs.DynamicOwnedAppend.run childStmt owned{before} = some owned{after} := by cbv',
            f'theorem available{after} (s : NState) (room : Proofs.DynamicAppendValue.RoomAt s 7 1) : Proofs.DynamicAppendAuto.Available owned{before}.params owned{before}.core s childStmt := by',
            '  intro p k selected index',
            f'  have chosen : Proofs.DynamicStmt.mutableRoot owned{before}.params owned{before}.core 5 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned0 (.vector atom) true) := by decide +kernel',
            '  have same : p = Proofs.DynamicOwnedState.newParameter owned0 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)',
            '  subst p',
            f'  have iv : Proofs.DynamicExpr.denote owned{before}.params owned{before}.core.locals owned{before}.core.contents idxNew = some (1 : Int) := by decide +kernel',
            '  have equal := Option.some.inj (index.symm.trans iv)',
            '  have pos : k = 1 := by omega',
            '  subst k; exact room',
            f'theorem room{after} : Proofs.DynamicAppendValue.RoomAt actual{before} 7 1 := ⟨(actual{before}.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,9,(actual{before}.frame.state.storage.lookup 9).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
            f'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned{before} s) (room : Proofs.DynamicAppendValue.RoomAt s 7 1) := Proofs.DynamicOwnedAppend.sound owned{before} s real childStmt owned{after} pure{after} (available{after} s room)',
            f'example := Proofs.DynamicOwnedAppend.child_sound owned{before} actual{before} real{before} 5 i32 i32 idxNew rowRead ⟨owned{after}.core,none⟩ (by cbv) (available{after} actual{before} room{after})',
            f'def actual{after} := ((childStmt.run actual{before}).getD ⟨actual{before},none,false⟩).state',
            f'theorem real{after} : Proofs.DynamicOwnedState.Realizes owned{after} actual{after} := by',
            f'  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned{before} actual{before} real{before} childStmt owned{after} pure{after} (available{after} actual{before} room{after})',
            f'  have same : actual{after} = out := by simp [actual{after},ran]',
            '  rw [same]; exact real',
            f'#guard owned{after}.nextOwner == 10 && owned{after}.nextBinding == 4 && owned{after}.scope == 3',
            f'#guard actual{after}.frame.bindings == actual1.frame.bindings']
    checks += ['#guard owned5.core.contents 7 == some (.rows i32 3 [[],[-3,-3,-3]])',
        '#guard (actual5.frame.state.storage.lookup 9).map (·.capacity) == some 4',
        '#guard (actual5.frame.state.storage.lookup 2) == (state.frame.state.storage.lookup 2)',
        'def restored := (Proofs.DynamicOwnedCleanup.leave outerOwned owned5).getD outerOwned',
        'theorem pureLeave : Proofs.DynamicOwnedCleanup.leave outerOwned owned5 = some restored := by cbv',
        'example := Proofs.DynamicOwnedCleanup.sound outerOwned owned5 restored state actual5 outerReal real5 none pureLeave',
        'def cleaned := Proofs.DynamicOwnedScope.left state actual5',
        'theorem cleanReal : Proofs.DynamicOwnedState.Realizes restored cleaned := (Proofs.DynamicOwnedCleanup.sound outerOwned owned5 restored state actual5 outerReal real5 none pureLeave).2.1',
        '#guard restored.nextOwner == 10 && restored.nextBinding == 3 && restored.scope == 2',
        '#guard [7,8,9].all (fun n => (restored.core.contents n).isNone && (cleaned.frame.state.storage.lookup n).isNone)',
        '#guard restored.core.contents 0 == logical 0 && restored.core.contents 2 == logical 2',
        'def nextOwned := (Proofs.DynamicOwnedState.runConstruct (.declareVector i32 true) restored).getD restored',
        'example := Proofs.DynamicOwnedConstruct.sound restored cleaned cleanReal (.declareVector i32 true) nextOwned (by cbv)',
        '#guard nextOwned.nextOwner == 11 && nextOwned.params.map (·.owner) == [0,0,2,10]',
        'def tightParent := {(actual1.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩ with limit := 1}',
        'def tight : NState := {actual1 with frame.state.storage.objects := actual1.frame.state.storage.objects.set 7 (some tightParent)}',
        '#guard tight.frame.state.wellFormed && (rootStmt.run tight).isNone',
        'def tightRow := {(actual2.frame.state.storage.lookup 9).getD ⟨0,[],0,64,0⟩ with limit := 0}',
        'def tightChild : NState := {actual2 with frame.state.storage.objects := actual2.frame.state.storage.objects.set 9 (some tightRow)}',
        '#guard tightChild.frame.state.wellFormed && (childStmt.run tightChild).isNone',
        'example : ¬ Proofs.DynamicAppendAuto.RootRoom tight 7 := by',
        '  intro ⟨old,found,room⟩',
        '  have lookup : tight.frame.state.storage.lookup 7 = some tightParent := by decide +kernel',
        '  have same : old = tightParent := Option.some.inj (found.symm.trans lookup)',
        '  subst old',
        '  have length : tightParent.items.length = 1 := by decide +kernel',
        '  have limit : tightParent.limit = 1 := rfl',
        '  omega',
        '#guard (Proofs.DynamicOwnedAppend.run (.appendRow (.local 1) i32) owned1).isNone',
        '#guard (Proofs.DynamicOwnedAppend.run (.append (.row (.local 5) atom (.literal i32 (-1))) i32 rowRead) owned2).isNone',
        '#guard (Proofs.DynamicOwnedAppend.run (.append (.local 5) i32 rowRead) owned2).isNone']
    return checks


class DynamicOwnedAppendTests(unittest.TestCase):
    def test_owned_append_pipeline_and_limits(self):
        checks = owned_checks()
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-append-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'OwnedAppendSource')
            checks[0] = 'import Proofs.DynamicOwnedAppend\nimport Proofs.DynamicOwnedCleanup\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['def call := OwnedAppendSource.owned.callFuel 600 state [.vectorReference 0,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match call with | .finished (s,.scalar x) => x == 8 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && s.frame.state.storage.objects.length == 12 && [7,8,9,11].all (fun n => (s.frame.state.storage.lookup n).isNone) && (s.frame.state.storage.lookup 10).isSome | _ => false)']
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
            self.assertEqual(result.stdout.splitlines(), ['8 5'])

if __name__ == '__main__':
    disable_network(); unittest.main()
