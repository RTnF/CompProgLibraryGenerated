"""Reached-state append room composes with owned scopes and control flow."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_dynamic_owned_append import owned_checks
from test_dynamic_expr import HEADER
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {void owned(std::vector<std::vector<int>>&a,const std::vector<std::vector<int>>&g,const std::vector<int>&other,int k,int j){
{std::vector<std::vector<int>>local((int)g.size()+g[k][j]);local.emplace_back();
local[1].push_back(g[k][j]);local[1].push_back(g[k][j]);local[1].push_back(g[k][j]);}}}
'''
CHECKS = '''
 open Proofs.DynamicOwnedRuns
 def inside : Command := .sequence (.primitive rowsStmt) (.sequence (.primitive rootStmt) (.sequence (.primitive childStmt) (.sequence (.primitive childStmt) (.sequence (.primitive childStmt) (.primitive .skip)))))
 theorem generatedBody : OwnedRunsSource.owned.body = .sequence (.scope inside) (.primitive .skip) := rfl
 theorem runRows : Runs (.primitive rowsStmt) owned0 entered (fun p a => p = ⟨owned1,none,false⟩ ∧ a.state = actual1) := by
   have run := (Runs.primitive owned0 entered real0 rowsStmt ⟨owned1,none,false⟩ (by cbv)).identify 1 ⟨actual1,none,false⟩ (by cbv)
   exact run.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)
 theorem runRoot : Runs (.primitive rootStmt) owned1 actual1 (fun p a => p = ⟨owned2,none,false⟩ ∧ a.state = actual2) := by
   have run := (Runs.append owned1 actual1 real1 rootStmt owned2 pureRoot (rootAvail actual1 rootRoom)).identify 1 ⟨actual2,none,false⟩ (by cbv)
   exact run.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)
'''

class DynamicOwnedRunsTests(unittest.TestCase):
    def test_generated_scope_sequence_branch_and_loop_break(self):
        checks = owned_checks()
        # Use precisely the casts emitted for the source's size_t arguments.
        checks = [s.replace('def idx : NExpr := .variable i32 3', 'def idx : NExpr := .cast ⟨64,false,false⟩ (.variable i32 3)')
                  .replace('def pos : NExpr := .variable i32 4', 'def pos : NExpr := .cast ⟨64,false,false⟩ (.variable i32 4)')
                  .replace('Ev state rowSize t 2 extra 4 5', 'Ev state rowSize t 2 extra 5 6')
                  .replace('Ev state rowRead t (-3) extra 5 6', 'Ev state rowRead t (-3) extra 7 8')
                  .replace('def rowsStmt : NStmt := .constructRows i32 true combined', 'def rowsStmt : NStmt := .constructRows i32 true (.cast ⟨64,false,false⟩ combined)')
                  .replace('def idxNew : NExpr := .binary i32 .sub rowSize (.literal i32 1)', 'def idxNew : NExpr := .cast ⟨64,false,false⟩ (.literal i32 1)') for s in checks]
        checks.append(CHECKS)
        for step in range(3):
            before, after = step+2, step+3
            checks += [f'theorem runChild{after} : Runs (.primitive childStmt) owned{before} actual{before} (fun p a => p = ⟨owned{after},none,false⟩ ∧ a.state = actual{after}) := by',
                f'  have run := (Runs.append owned{before} actual{before} real{before} childStmt owned{after} pure{after} (available{after} actual{before} room{after})).identify 1 ⟨actual{after},none,false⟩ (by cbv)',
                '  exact run.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)']
        checks += ['theorem insideRuns : Runs inside owned0 entered (fun p a => p = ⟨owned5,none,false⟩ ∧ a.state = actual5) := by',
            '  apply Runs.seq; apply runRows.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  apply Runs.seq; apply runRoot.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  apply Runs.seq; apply runChild3.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  apply Runs.seq; apply runChild4.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  apply Runs.seq; apply runChild5.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  have skip := (Runs.primitive owned5 actual5 real5 .skip ⟨owned5,none,false⟩ rfl).identify 1 ⟨actual5,none,false⟩ rfl',
            '  exact skip.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)',
            'theorem scopedRuns : Runs (.scope inside) outerOwned state (fun p a => p = ⟨restored,none,false⟩ ∧ a.state = cleaned) := by',
            '  apply Runs.scope outerReal',
            '  apply insideRuns.mono',
            '  rintro p a ⟨pe,ae⟩; subst p',
            '  exact ⟨restored,pureLeave,rfl,by rw [ae]; rfl⟩',
            'theorem sourceRuns : Runs OwnedRunsSource.owned.body outerOwned state (fun p a => p = ⟨restored,none,false⟩ ∧ a.state = cleaned) := by',
            '  rw [generatedBody]',
            '  apply Runs.seq; apply scopedRuns.mono',
            '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]',
            '  have skip := (Runs.primitive restored cleaned cleanReal .skip ⟨restored,none,false⟩ rfl).identify 1 ⟨cleaned,none,false⟩ rfl',
            '  exact skip.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)',
            'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned2 s) : Runs (.sequence (.primitive (.ret (.literal i32 7))) (.primitive (.check (.literal i32 0)))) owned2 s (fun p _ => p.returned = some 7) := by',
            '  apply Runs.sequence',
            '  apply (Runs.primitive owned2 s real (.ret (.literal i32 7)) ⟨owned2,some 7,false⟩ (by cbv)).mono',
            '  intro p a same; subst p; exact Or.inl ⟨Or.inl rfl,rfl⟩',
            'def loopBody : Command := .sequence (.primitive childStmt) .breakLoop',
            'def loopPost (p : Proofs.DynamicOwnedControl.Step) (_ : NStep) : Prop := p.state = owned3 ∧ p.returned = none ∧ p.breaking = false',
            'def loopInv (g : Nat) (st : Proofs.DynamicOwnedState.State) (s : NState) : Prop := g = 0 ∧ st = owned2 ∧ s.frame = actual2.frame',
            'theorem loopStep (g : Nat) (st : Proofs.DynamicOwnedState.State) (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s) (inv : loopInv g st s) : ∃ v, Proofs.DynamicExpr.denote st.params st.core.locals st.core.contents (.literal i32 1) = some v ∧ ∀ next, (NExpr.literal i32 1).eval s = some (next,v) → Proofs.DynamicOwnedState.Realizes st ((next.release s).charge 1 0) → (v = 0 → loopPost ⟨st,none,false⟩ ⟨(next.release s).charge 1 0,none,false⟩) ∧ (v ≠ 0 → Runs loopBody st ((next.release s).charge 1 0) (fun p a => (p.returned.isSome = true ∧ loopPost p a) ∨ (p.returned = none ∧ ((p.breaking = true ∧ loopPost {p with breaking := false} {a with breaking := false}) ∨ (p.breaking = false ∧ ∃ g2, g2 < g ∧ loopInv g2 p.state a.state))))) := by',
            '  obtain ⟨zero,pe,frame⟩ := inv; subst st',
            '  refine ⟨1,by decide +kernel,?_⟩',
            '  intro next eval after',
            '  refine ⟨fun zero => by omega,?_⟩',
            '  intro nonzero',
            '  have nextEq : next = s.charge 1 1 := (Prod.mk.inj (Option.some.inj eval)).1.symm',
            '  have room : Proofs.DynamicAppendValue.RoomAt ((next.release s).charge 1 0) 7 1 := by simpa only [Proofs.DynamicAppendValue.RoomAt,nextEq,NState.charge,NState.observe,NState.release,frame] using room3',
            '  apply Runs.seq',
            '  apply ((Runs.append owned2 ((next.release s).charge 1 0) after childStmt owned3 pure3 (available3 _ room)).inspect).mono',
            '  rintro p a ⟨matched,pe⟩; subst p; refine ⟨rfl,rfl,?_⟩',
            '  exact (Runs.breakLoop owned3 a.state matched.state).mono (fun p a pe => by subst p; exact Or.inr ⟨rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩)',
            'example : Runs (.whileLoop (.literal i32 1) loopBody) owned2 actual2 loopPost := Runs.whileGhostStop loopInv loopPost loopStep 0 owned2 actual2 real2 ⟨rfl,rfl,rfl⟩',
            'example (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned2 s) (room : Proofs.DynamicAppendValue.RoomAt ((s.charge 1 1).release s |>.charge 1 0) 7 1) : Runs (.branch (.literal i32 1) (.primitive childStmt) (.primitive (.check (.literal i32 0)))) owned2 s (fun p _ => p = ⟨owned3,none,false⟩) := by',
            '  apply Runs.branch (v := 1) real (by decide +kernel)',
            '  intro next evaluated after',
            '  have same : next = s.charge 1 1 := (Prod.mk.inj (Option.some.inj evaluated)).1.symm',
            '  subst next',
            '  exact Runs.append owned2 _ after childStmt owned3 pure3 (available3 _ room)']
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-runs-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'OwnedRunsSource')
            checks[0] = 'import Proofs.DynamicOwnedRuns\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            checks += ['def call := OwnedRunsSource.owned.callFuel 600 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                '#guard (match call with | .finished (s,.unit) => s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && s.frame.state.storage.objects.length == 10 && [7,8,9].all (fun n => (s.frame.state.storage.lookup n).isNone) | _ => false)']
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::vector<int>other{77};cp::owned(g,g,other,1,1);std::cout<<g.size()<<" "<<g[1][1]<<" "<<other[0]<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['4 -3 77'])

if __name__ == '__main__':
    disable_network(); unittest.main()
