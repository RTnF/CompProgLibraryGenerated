"""Owned scalar/vector results compose through generated scopes and control."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_dynamic_vector_scope import vector_checks
from test_dynamic_expr import HEADER
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean, terminal_return_kinds
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {std::vector<std::vector<int>> rows(std::vector<std::vector<int>>&a,const std::vector<std::vector<int>>&g,const std::vector<int>&other,int k,int j){
{std::vector<int>flat;std::vector<std::vector<int>>local(2);std::vector<int>later;
local.emplace_back();local[2].push_back(g[k][j]);return local;}}}
'''

class DynamicResultRunsTests(unittest.TestCase):
    def test_generated_vector_body_and_nested_scope_return(self):
        checks = [s.replace('def idx : NExpr := .variable i32 3', 'def idx : NExpr := .cast ⟨64,false,false⟩ (.variable i32 3)')
                  .replace('def pos : NExpr := .variable i32 4', 'def pos : NExpr := .cast ⟨64,false,false⟩ (.variable i32 4)')
                  .replace('Ev state rowSize t 2 extra 4 5', 'Ev state rowSize t 2 extra 5 6')
                  .replace('Ev state rowRead t (-3) extra 5 6', 'Ev state rowRead t (-3) extra 7 8')
                  .replace('.constructRows i32 true (.literal i32 2)', '.constructRows i32 true (.cast ⟨64,false,false⟩ (.literal i32 2))')
                  .replace('.row (.local 6) atom (.literal i32 2)', '.row (.local 6) atom (.cast ⟨64,false,false⟩ (.literal i32 2))') for s in vector_checks()]
        checks += ['open Proofs.DynamicResultRuns',
            'def inside : Command := .sequence (.primitive emptyStmt) (.sequence (.primitive construct2) (.sequence (.primitive construct3) (.sequence (.primitive rootStmt) (.sequence (.primitive childStmt) (.sequence (.primitive (.retVector 6)) (.primitive .skip))))))',
            'theorem generatedBody : ResultRunsSource.rows.body = .sequence (.scope inside) (.primitive .skip) := rfl']
        for before, after, stmt, room in [(0, 1, 'emptyStmt', None), (1, 2, 'construct2', None), (2, 3, 'construct3', None), (3, 4, 'rootStmt', 'rootAvail'), (4, 5, 'childStmt', 'childAvail')]:
            initial = 'entered' if before == 0 else f'actual{before}'
            ctor = f'Runs.primitive owned{before} {initial} real{before} {stmt} ⟨owned{after},none,false⟩ (by cbv)' if room is None else f'Runs.append owned{before} {initial} real{before} {stmt} owned{after} (by cbv) {room}'
            checks += [f'theorem part{after} : Runs (.primitive {stmt}) owned{before} {initial} (fun p a => p = ⟨owned{after},none,false⟩ ∧ a.state = actual{after}) := by',
                f'  have run := ({ctor}).identify 1 ⟨actual{after},none,false⟩ (by cbv)',
                '  exact run.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)']
        checks += ['theorem insideRuns : Runs inside owned0 entered (fun p _ => p = ⟨owned5,some (.vector 8 (.vector atom)),false⟩) := by']
        for part in range(1, 6):
            checks += [f'  apply Runs.seq; apply part{part}.mono', '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]']
        checks += ['  apply Runs.sequence',
            '  apply (Runs.retVector owned5 actual5 real5 6 (.vector 8 (.vector atom)) (by cbv)).mono',
            '  rintro p a ⟨pe,work⟩; subst p; exact Or.inl ⟨Or.inl rfl,rfl⟩',
            'theorem scopedRuns : Runs (.scope inside) outerOwned state (fun p _ => p = ⟨rowsFinal,some (.vector 8 (.vector atom)),false⟩) := by',
            '  apply Runs.scope outerReal; apply insideRuns.mono',
            '  intro p a pe; subst p',
            '  exact ⟨rowsFinal,pureRows,fun _ _ => rfl⟩',
            'theorem sourceRuns : Runs ResultRunsSource.rows.body outerOwned state (fun p _ => p = ⟨rowsFinal,some (.vector 8 (.vector atom)),false⟩) := by',
            '  rw [generatedBody]',
            '  apply Runs.sequence; apply scopedRuns.mono',
            '  intro p a pe; subst p; exact Or.inl ⟨Or.inl rfl,rfl⟩',
            'def outer1 : Proofs.DynamicOwnedState.State := {outerOwned with scope := 1}',
            'def state1 : NState := {state with scope := 1}',
            'theorem realOuter1 : Proofs.DynamicOwnedState.Realizes outer1 state1 := ⟨⟨outerReal.data.locals,outerReal.data.heap⟩,outerReal.owner,outerReal.binding,rfl⟩',
            'def nestedFinal := (Proofs.DynamicResultScope.leave outer1 rowsFinal (some (.vector 8 (.vector atom)))).getD outer1',
            'theorem nestedRuns : Runs (.scope ResultRunsSource.rows.body) outer1 state1 (fun p _ => p = ⟨nestedFinal,some (.vector 8 (.vector atom)),false⟩) := by',
            '  apply Runs.scope realOuter1; apply sourceRuns.mono',
            '  intro p a pe; subst p',
            '  exact ⟨nestedFinal,by cbv,fun _ _ => rfl⟩',
            '#guard nestedFinal.core.contents 8 == some (.rows i32 1 [[],[],[-3]])',
            '#guard nestedFinal.nextOwner == 13 && nestedFinal.nextBinding == 3 && nestedFinal.scope == 1',
            'def nestedActual : NStep := match Proofs.CppNestedProgram.runFuel 100 (.scope ResultRunsSource.rows.body) state1 with | .finished a => a | _ => ⟨state1,none,false⟩',
            '#guard [8,9,10,12].all (fun n => nestedActual.state.frame.state.forest.context n == some 1)',
            'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned5 s) : Runs (.branch (.literal i32 1) (.primitive (.retVector 6)) (.primitive (.check (.literal i32 0)))) owned5 s (fun p _ => p.returned = some (.vector 8 (.vector atom))) := by',
            '  apply Runs.branch (v := 1) real (by decide +kernel)',
            '  intro next evaluated after',
            '  exact (Runs.retVector owned5 _ after 6 (.vector 8 (.vector atom)) (by cbv)).mono (fun p a ⟨pe,_⟩ => by subst p; rfl)',
            'def returnPost (p : Proofs.DynamicResultRuns.Step) (_ : NStep) : Prop := p.state = owned5 ∧ p.returned = some (.vector 8 (.vector atom)) ∧ p.breaking = false',
            'def returnInv (_ : Nat) (st : Proofs.DynamicOwnedState.State) (_ : NState) : Prop := st = owned5',
            'theorem returnStep (g : Nat) (st : Proofs.DynamicOwnedState.State) (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s) (inv : returnInv g st s) : ∃ v, Proofs.DynamicExpr.denote st.params st.core.locals st.core.contents (.literal i32 1) = some v ∧ ∀ next, (NExpr.literal i32 1).eval s = some (next,v) → Proofs.DynamicOwnedState.Realizes st ((next.release s).charge 1 0) → (v = 0 → returnPost ⟨st,none,false⟩ ⟨(next.release s).charge 1 0,none,false⟩) ∧ (v ≠ 0 → Runs (.primitive (.retVector 6)) st ((next.release s).charge 1 0) (fun p a => (p.returned.isSome = true ∧ returnPost p a) ∨ (p.returned = none ∧ ((p.breaking = true ∧ returnPost {p with breaking := false} {a with breaking := false}) ∨ (p.breaking = false ∧ ∃ g2, g2 < g ∧ returnInv g2 p.state a.state))))) := by',
            '  change st = owned5 at inv; subst st',
            '  refine ⟨1,by decide +kernel,?_⟩',
            '  intro next eval after; refine ⟨fun zero => by omega,?_⟩; intro nonzero',
            '  exact (Runs.retVector owned5 _ after 6 (.vector 8 (.vector atom)) (by cbv)).mono (fun p a ⟨pe,_⟩ => by subst p; exact Or.inl ⟨rfl,rfl,rfl,rfl⟩)',
            'example : Runs (.whileLoop (.literal i32 1) (.primitive (.retVector 6))) owned5 actual5 returnPost := Runs.whileGhostStop returnInv returnPost returnStep 0 owned5 actual5 real5 rfl',
            'def unitFinal := (Proofs.DynamicOwnedCleanup.leave outerOwned owned5).getD outerOwned',
            'example := Proofs.DynamicResultScope.sound outerOwned owned5 unitFinal state actual5 outerReal real5 (some .unit) (by cbv)']
        with tempfile.TemporaryDirectory(prefix='dynamic-result-runs-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'ResultRunsSource')
            checks[0] = 'import Proofs.DynamicResultRuns\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['def call := ResultRunsSource.rows.callFuel 600 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match call with | .finished (s,.vector root element) => root == 8 && element == .vector atom && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,11].all (fun n => (s.frame.state.storage.lookup n).isNone) && [8,9,10,12].all (fun n => s.frame.state.forest.context n == some 2) | _ => false)']
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::vector<int>other{77};auto r=cp::rows(g,g,other,1,1);std::cout<<r.size()<<" "<<r[2][0]<<" "<<g.size()<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['3 -3 4'])

    def test_terminal_return_paths_and_rejections(self):
        self.assertEqual(terminal_return_kinds([dict(kind='scope', body=[dict(kind='return_vector')])]), {'return_vector'})
        self.assertEqual(terminal_return_kinds([dict(kind='branch', yes=[dict(kind='return_vector')], no=[])]), set())
        cases = [('std::vector<int> f(int n){if(n){std::vector<int>a;return a;}else{std::vector<int>b;return b;}}', True),
                 ('int f(int n){{return n;}}', True),
                 ('std::vector<int> f(int n){if(n){std::vector<int>a;return a;}}', False),
                 ('std::vector<int> f(int n){while(n){std::vector<int>a;return a;}}', False)]
        with tempfile.TemporaryDirectory(prefix='nested-return-paths-') as directory:
            source = Path(directory)/'source.hpp'
            for body, accepted in cases:
                source.write_text('#include <vector>\nnamespace cp {'+body+'}')
                if accepted:
                    ir = lower_source(source)
                    self.assertTrue(ir['functions'])
                else:
                    with self.assertRaisesRegex(ValueError, 'final return on every supported path'):
                        lower_source(source)

if __name__ == '__main__':
    disable_network(); unittest.main()
