"""Vector return transfers flat/rows roots and retires their owned siblings."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_dynamic_expr import fixture_checks, HEADER
from test_dynamic_flat_append import INITIAL
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {
std::vector<std::vector<int>> rows(const std::vector<std::vector<int>>&g,int k,int j){
std::vector<int>flat;std::vector<std::vector<int>>local(2);std::vector<int>later;
local.emplace_back();local[2].push_back(g[k][j]);return local;}
std::vector<int> flat(const std::vector<std::vector<int>>&g,int k,int j){
std::vector<int>local;local.push_back(g[k][j]);std::vector<std::vector<int>>rows(2);std::vector<int>later;
rows.emplace_back();return local;}
}
'''

def vector_checks():
    checks = fixture_checks()+[INITIAL]
    for before, after, stmt in [(1, 2, '.constructRows i32 true (.literal i32 2)'), (2, 3, '.declareVector i32 true')]:
        checks += [f'def construct{after} : NStmt := {stmt}',
            f'def owned{after} := (Proofs.DynamicOwnedState.runConstruct construct{after} owned{before}).getD owned{before}',
            f'def actual{after} := ((construct{after}.run actual{before}).getD ⟨actual{before},none,false⟩).state',
            f'theorem real{after} : Proofs.DynamicOwnedState.Realizes owned{after} actual{after} := by',
            f'  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned{before} actual{before} real{before} construct{after} owned{after} (by cbv)',
            f'  have same : actual{after} = out := by simp [actual{after},ran]',
            '  rw [same]; exact real']
    checks += ['def rootStmt : NStmt := .appendRow (.local 6) i32',
        'def owned4 := (Proofs.DynamicOwnedAppend.run rootStmt owned3).getD owned3',
        'theorem rootRoom : Proofs.DynamicAppendAuto.RootRoom actual3 8 := ⟨(actual3.frame.state.storage.lookup 8).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
        'theorem rootAvail : Proofs.DynamicOwnedAppend.Available owned3 actual3 rootStmt := by',
        '  intro p selected',
        '  have chosen : Proofs.DynamicStmt.mutableRoot owned3.params owned3.core 6 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true) := by decide +kernel',
        '  have same : p = Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)',
        '  subst p; exact rootRoom',
        'def actual4 := ((rootStmt.run actual3).getD ⟨actual3,none,false⟩).state',
        'theorem real4 : Proofs.DynamicOwnedState.Realizes owned4 actual4 := by',
        '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned3 actual3 real3 rootStmt owned4 (by cbv) rootAvail',
        '  have same : actual4 = out := by simp [actual4,ran]',
        '  rw [same]; exact real',
        'def childStmt : NStmt := .append (.row (.local 6) atom (.literal i32 2)) i32 rowRead',
        'def owned5 := (Proofs.DynamicOwnedAppend.run childStmt owned4).getD owned4',
        'theorem childRoom : Proofs.DynamicAppendValue.RoomAt actual4 8 2 := ⟨(actual4.frame.state.storage.lookup 8).getD ⟨0,[],0,64,0⟩,12,(actual4.frame.state.storage.lookup 12).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
        'theorem childAvail : Proofs.DynamicOwnedAppend.Available owned4 actual4 childStmt := by',
        '  intro p k selected index',
        '  have chosen : Proofs.DynamicStmt.mutableRoot owned4.params owned4.core 6 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true) := by decide +kernel',
        '  have same : p = Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)',
        '  subst p',
        '  have equal : (2 : Int) = k := Option.some.inj index',
        '  have pos : k = 2 := by omega',
        '  subst k; exact childRoom',
        'def actual5 := ((childStmt.run actual4).getD ⟨actual4,none,false⟩).state',
        'theorem real5 : Proofs.DynamicOwnedState.Realizes owned5 actual5 := by',
        '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned4 actual4 real4 childStmt owned5 (by cbv) childAvail',
        '  have same : actual5 = out := by simp [actual5,ran]',
        '  rw [same]; exact real',
        '#guard owned5.nextOwner == 13 && owned5.nextBinding == 6',
        '#guard (actual5.frame.state.forest.lookup 8).map (·.children) == some [9,10,12]',
        'def flatFinal := (Proofs.DynamicVectorScope.leave outerOwned owned5 7 atom).getD outerOwned',
        'def rowsFinal := (Proofs.DynamicVectorScope.leave outerOwned owned5 8 (.vector atom)).getD outerOwned',
        'theorem pureFlat : Proofs.DynamicVectorScope.leave outerOwned owned5 7 atom = some flatFinal := by cbv',
        'theorem pureRows : Proofs.DynamicVectorScope.leave outerOwned owned5 8 (.vector atom) = some rowsFinal := by cbv',
        'example (s t : NState) (before : Proofs.DynamicOwnedState.Realizes outerOwned s) (after : Proofs.DynamicOwnedState.Realizes owned5 t) := Proofs.DynamicVectorScope.sound outerOwned owned5 rowsFinal s t before after 8 (.vector atom) pureRows',
        'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned5 s) := Proofs.DynamicVectorReturn.sound owned5 s real 6 (.vector 8 (.vector atom)) (by cbv)',
        'example := Proofs.DynamicVectorReturn.sound owned5 actual5 real5 5 (.vector 7 atom) (by cbv)',
        'example := Proofs.DynamicVectorScope.sound outerOwned owned5 rowsFinal state (actual5.charge 1 0) outerReal (Proofs.DynamicVectorReturn.sound owned5 actual5 real5 6 (.vector 8 (.vector atom)) (by cbv)).2.1 8 (.vector atom) pureRows',
        'def rowsOut := (state.leave actual5 (some (.vector 8 (.vector atom)))).getD state',
        'def flatOut := (state.leave actual5 (some (.vector 7 atom))).getD state',
        'theorem rowsReal : Proofs.DynamicOwnedState.Realizes rowsFinal rowsOut := by',
        '  obtain ⟨frame,out,moved,ran,real,_⟩ := Proofs.DynamicVectorScope.sound outerOwned owned5 rowsFinal state actual5 outerReal real5 8 (.vector atom) pureRows',
        '  have same : rowsOut = out := by simp [rowsOut,ran]',
        '  rw [same]; exact real',
        'theorem flatReal : Proofs.DynamicOwnedState.Realizes flatFinal flatOut := by',
        '  obtain ⟨frame,out,moved,ran,real,_⟩ := Proofs.DynamicVectorScope.sound outerOwned owned5 flatFinal state actual5 outerReal real5 7 atom pureFlat',
        '  have same : flatOut = out := by simp [flatOut,ran]',
        '  rw [same]; exact real',
        '#guard rowsFinal.core.contents 8 == some (.rows i32 2 [[],[],[-3]])',
        '#guard flatFinal.core.contents 7 == some (.flat i32 2 [])',
        '#guard rowsFinal.params == params && rowsFinal.nextOwner == 13 && rowsFinal.nextBinding == 3 && rowsFinal.scope == 2',
        '#guard [7,11].all (fun n => (rowsOut.frame.state.storage.lookup n).isNone)',
        '#guard [8,9,10,12].all (fun n => (rowsOut.frame.state.storage.lookup n).isSome && rowsOut.frame.state.forest.context n == some 2)',
        '#guard [8,9,10,11,12].all (fun n => (flatOut.frame.state.storage.lookup n).isNone)',
        '#guard rowsOut.frame.bindings == state.frame.bindings && flatOut.frame.bindings == state.frame.bindings',
        '#guard rowsOut.frame.state.wellFormed && flatOut.frame.state.wellFormed',
        '#guard rowsOut.work == actual5.work+3 && flatOut.work == actual5.work+9',
        '#guard rowsOut.frame.state.storage.objects.length == 13 && flatOut.frame.state.storage.objects.length == 13',
        '#guard rowsFinal.core.contents 0 == logical 0 && rowsFinal.core.contents 2 == logical 2',
        'def boundRows := ((rowsOut.frame.bindRoot 8 (.vector atom) 2 true).getD (rowsOut.frame,0)).1',
        '#guard (boundRows.child 3 atom 2).isSome',
        '#guard (Proofs.DynamicVectorReturn.run owned5 0).isNone',
        '#guard (Proofs.DynamicVectorReturn.run owned5 2).isNone',
        '#guard (Proofs.DynamicVectorScope.leave outerOwned owned5 0 (.vector atom)).isNone',
        '#guard (Proofs.DynamicVectorScope.leave outerOwned owned5 8 atom).isNone',
        '#guard (Proofs.DynamicVectorScope.leave outerOwned {owned5 with nextBinding := 0} 8 (.vector atom)).isNone',
        '#guard (Proofs.DynamicVectorScope.leave {outerOwned with params := owned5.params} owned5 8 (.vector atom)).isNone']
    return checks


class DynamicVectorScopeTests(unittest.TestCase):
    def test_vector_move_scope_cleanup_and_return_profile(self):
        checks = vector_checks()
        with tempfile.TemporaryDirectory(prefix='dynamic-vector-scope-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'VectorScopeSource')
            checks[0] = 'import Proofs.DynamicVectorReturn\nimport Proofs.DynamicOwnedAppend\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['def callRows := VectorScopeSource.rows.callFuel 600 state [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match callRows with | .finished (s,.vector root element) => root == 8 && element == .vector atom && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,11].all (fun n => (s.frame.state.storage.lookup n).isNone) && [8,9,10,12].all (fun n => s.frame.state.forest.context n == some 2) | _ => false)',
                'def callFlat := VectorScopeSource.flat.callFuel 600 state [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match callFlat with | .finished (s,.vector root element) => root == 7 && element == atom && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && (s.frame.state.storage.lookup root).map (·.items) == some [.integer (-3)] && [8,9,10,11,12].all (fun n => (s.frame.state.storage.lookup n).isNone) | _ => false)']
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};auto r=cp::rows(g,1,1);auto f=cp::flat(g,1,1);std::cout<<r.size()<<" "<<r[2][0]<<" "<<f[0]<<" "<<g.size()<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['3 -3 -3 4'])

if __name__ == '__main__':
    disable_network(); unittest.main()
