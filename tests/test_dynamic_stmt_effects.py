"""Primitive effects and composed scalar scope with dynamic row appends."""
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
ROOT=Path(__file__).resolve().parent.parent
SOURCE='''#include <vector>
namespace cp {int push(std::vector<std::vector<int>>&g,int k,int j){int index=(int)g.size()+g[k][j];g[index].emplace_back(g[k][j]);return g[index].size();}
int scoped(const std::vector<std::vector<int>>&g,int&x){if(g.size()){int z=7;x=z;return z;}return 0;} int constant(){return 7;}}
'''

class DynamicStmtEffectsTests(unittest.TestCase):
    def test_effects_and_composition(self):
        checks=fixture_checks()
        checks += ['open Proofs.DynamicPhysicalEffects Proofs.DynamicForestEffects',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'example (ps : List Parameter) (st : Proofs.DynamicStmt.State) (s : NState) (real : Realizes ps st.locals st.contents s) (stmt : NStmt) (p : Proofs.DynamicStmt.Step) (pure : Proofs.DynamicStmt.run ps stmt st = some p) (a : NStep) (ran : stmt.run s = some a) : Change s a.state := Proofs.DynamicStmtEffects.effects ps st s real stmt p pure a ran',
          'def append : NStmt := .append (.row (.local 0) atom combined) i32 rowRead',
          'def appendPure : Proofs.DynamicStmt.Step := ⟨⟨snapshot state,putContents logical 0 (.rows i32 0 (values.set 1 [17,-3,-3]))⟩,none⟩',
          'theorem pureAppend : Proofs.DynamicStmt.run params append st0 = some appendPure := by cbv',
          'def appended : NStep := (append.run state).getD ⟨state,none,false⟩',
          'theorem actualAppend : append.run state = some appended := by decide +kernel',
          'theorem appendEffect : Change state appended.state := Proofs.DynamicStmtEffects.effects params st0 state realizes append appendPure pureAppend appended actualAppend',
          'example : NoScope appended.state.frame.state.forest 3 := appendEffect.1.absent _ (NoScope.of_tags _ _ (by decide +kernel))',
          'example : appended.state.frame.rootWritable[0]? = some true := appendEffect.1.flag 0 true (by decide +kernel)',
          '#guard appended.state.frame.state.forest == state.frame.state.forest',
          '#guard appended.state.frame.rootWritable == state.frame.rootWritable',
          '#guard (appended.state.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3)]',
          '#guard (appended.state.frame.state.storage.lookup 4).map (·.capacity) == some 4',
          'theorem available : Proofs.DynamicAppendAuto.Available params st0 state append := by',
          '  intro p k selected value',
          '  have chosen : Proofs.DynamicStmt.mutableRoot params st0 0 (.vector atom) = some p0 := by decide +kernel',
          '  have same : p = p0 := Option.some.inj (selected.symm.trans chosen)',
          '  subst p',
          '  have index : Proofs.DynamicExpr.denote params st0.locals st0.contents combined = some 1 := by decide +kernel',
          '  have natural : (k : Int) = 1 := Option.some.inj (value.symm.trans index)',
          '  have one : k = 1 := by omega',
          '  subst k',
          '  exact ⟨(state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,4,(state.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
          'example := Proofs.DynamicStmtEffects.sound params st0 state realizes append appendPure pureAppend available',
          'def decl : NStmt := .declare i32 true (.literal i32 7)',
          'def stA : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared st0.locals i32 true 7,logical⟩',
          'def assign : NStmt := .assign 3 i32 (.variable i32 5)',
          'def stB : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.assigned stA.locals ⟨0,true⟩ ⟨i32,1⟩ 7,logical⟩',
          'def ret : NStmt := .ret (.variable i32 5)',
          'def body : Command := .sequence (.primitive decl) (.sequence (.primitive assign) (.primitive ret))',
          'theorem bodyVerified (s : NState) (real : Realizes params st0.locals st0.contents s) : Proofs.DynamicEffectRuns.Runs params body st0 s (fun p _ => p = ⟨stB,some 7,false⟩) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.seq',
          '  have first := Proofs.DynamicEffectRuns.Runs.primitive params st0 s real decl (⟨stA,none⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro',
          '  apply first.inspect.mono',
          '  intro p a ⟨matched,same⟩; subst p',
          '  refine ⟨rfl,rfl,?_⟩',
          '  apply Proofs.DynamicEffectRuns.Runs.seq',
          '  have second := Proofs.DynamicEffectRuns.Runs.primitive params stA a.state matched.state assign (⟨stB,none⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro',
          '  apply second.inspect.mono',
          '  intro p a ⟨matched,same⟩; subst p',
          '  refine ⟨rfl,rfl,?_⟩',
          '  exact Proofs.DynamicEffectRuns.Runs.primitive params stB a.state matched.state ret (⟨stB,some 7⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro',
          'theorem branchVerified : Proofs.DynamicEffectRuns.Runs params (.branch rootSize body (.primitive .skip)) st0 state (fun p _ => p = ⟨stB,some 7,false⟩) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.branch realizes (v := 4) (by decide +kernel)',
          '  intro next evaluated real; exact bodyVerified _ real',
          'def final : Proofs.DynamicStmt.State := ⟨⟨[⟨i32,7⟩,⟨i32,1⟩],st0.locals.bindings,st0.locals.slots⟩,logical⟩',
          'theorem scopeVerified : Proofs.DynamicEffectRuns.Runs params (.scope body) st0 state (fun p a => p.state.locals.memory = [⟨i32,7⟩,⟨i32,1⟩] ∧ a.state.scope = state.scope ∧ p.returned = some 7) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.scope realizes (NoScope.of_tags _ _ (by decide +kernel))',
          '  apply (bodyVerified {state with scope := state.scope+1} (Proofs.DynamicScopeAuto.enter params st0 state realizes)).mono',
          '  intro p a same; subst p',
          '  intro restored left',
          '  have known : Proofs.DynamicControl.leave st0 stB = some final := rfl',
          '  have equal : restored = final := Option.some.inj (left.symm.trans known)',
          '  subst restored; exact ⟨rfl,rfl,rfl⟩',
          'example := Proofs.DynamicControlBridge.Runs.aligned scopeVerified',
          'example := Proofs.DynamicControlBridge.Runs.aligned branchVerified',
          'def check : NStmt := .check rootSize',
          'def checkOut : NStep := (check.run state).getD ⟨state,none,false⟩',
          'example : Change state checkOut.state := Proofs.DynamicStmtEffects.effects params st0 state realizes check ⟨st0,none⟩ (by rfl) checkOut (by decide +kernel)',
          '#guard (Proofs.DynamicStmt.run params (.check (.literal i32 0)) st0).isNone',
          '#guard (Proofs.DynamicStmt.run params (.assign 3 i32 (.binary i32 .add (.literal i32 2147483647) combined)) st0).isNone',
          '#guard (Proofs.DynamicStmt.run params (.append (.row (.local 1) atom combined) i32 rowRead) st0).isNone',
          '#guard (Proofs.DynamicStmt.run params (.append (.row (.local 0) atom (.literal i32 (-1))) i32 rowRead) st0).isNone']
        checks += ['def zeroState : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.assigned st0.locals ⟨0,true⟩ ⟨i32,1⟩ 0,logical⟩',
          'def zeroAssign : NStmt := .assign 3 i32 (.literal i32 0)',
          'def inv (g : Nat) (st : Proofs.DynamicStmt.State) (_ : NState) : Prop := (g = 1 ∧ st = st0) ∨ (g = 0 ∧ st = zeroState)',
          'theorem loopVerified : Proofs.DynamicEffectRuns.Runs params (.whileLoop (.variable i32 3) (.primitive zeroAssign)) st0 state (fun p _ => p.state = zeroState ∧ p.returned = none ∧ p.breaking = false) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.whileGhostStop inv _ ?_ 1 st0 state realizes (Or.inl ⟨rfl,rfl⟩)',
          '  intro g st s real invariant',
          '  rcases invariant with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩',
          '  · refine ⟨1,by decide +kernel,?_⟩',
          '    intro next evaluated after',
          '    refine ⟨fun zero => by contradiction,?_⟩',
          '    intro nonzero',
          '    apply (Proofs.DynamicEffectRuns.Runs.primitive params st0 _ after zeroAssign (⟨zeroState,none⟩ : Proofs.DynamicStmt.Step) (by cbv) True.intro).mono',
          '    intro p a same; subst p',
          '    exact Or.inr ⟨rfl,Or.inr ⟨rfl,0,by decide,Or.inr ⟨rfl,rfl⟩⟩⟩',
          '  · refine ⟨0,by decide +kernel,?_⟩',
          '    intro next evaluated after',
          '    exact ⟨fun _ => ⟨rfl,rfl,rfl⟩,fun nonzero => False.elim (nonzero rfl)⟩',
          'example := Proofs.DynamicControlBridge.Runs.aligned loopVerified',
          'theorem breakVerified : Proofs.DynamicEffectRuns.Runs params (.whileLoop rootSize .breakLoop) st0 state (fun p _ => p.state = st0 ∧ p.returned = none ∧ p.breaking = false) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.whileGhostStop (fun _ st _ => st = st0) _ ?_ 0 st0 state realizes rfl',
          '  intro g st s real same; subst st',
          '  refine ⟨4,by decide +kernel,?_⟩',
          '  intro next evaluated after',
          '  refine ⟨fun zero => by contradiction,?_⟩',
          '  intro nonzero',
          '  apply (Proofs.DynamicEffectRuns.Runs.breakLoop params st0 _ after).mono',
          '  intro p a same; subst p',
          '  exact Or.inr ⟨rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩',
          'example := Proofs.DynamicControlBridge.Runs.aligned breakVerified',
          'theorem returnVerified : Proofs.DynamicEffectRuns.Runs params (.whileLoop rootSize (.primitive (.ret (.literal i32 7)))) st0 state (fun p _ => p.returned = some 7) := by',
          '  apply Proofs.DynamicEffectRuns.Runs.whileGhostStop (fun _ st _ => st = st0) _ ?_ 0 st0 state realizes rfl',
          '  intro g st s real same; subst st',
          '  refine ⟨4,by decide +kernel,?_⟩',
          '  intro next evaluated after',
          '  refine ⟨fun zero => by contradiction,?_⟩',
          '  intro nonzero',
          '  apply (Proofs.DynamicEffectRuns.Runs.primitive params st0 _ after (.ret (.literal i32 7)) (⟨st0,some 7⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro).mono',
          '  intro p a same; subst p; exact Or.inl ⟨rfl,rfl⟩',
          'example := Proofs.DynamicControlBridge.Runs.aligned returnVerified']
        checks += ['def genericCall (s : NState) (real : Realizes params st0.locals st0.contents s) (absent : NoScope s.frame.state.forest (s.scope+1)) := Proofs.DynamicEffectRuns.call params st0 s real EffectsSource.constant [] [] rfl absent (by',
          '  intro initial prepared initialReal',
          '  change Proofs.DynamicEffectRuns.Runs [] (.sequence (.primitive (.ret (.literal i32 7))) (.primitive .skip)) ⟨snapshot initial,logical⟩ initial _',
          '  apply Proofs.DynamicEffectRuns.Runs.sequence',
          '  apply (Proofs.DynamicEffectRuns.Runs.primitive [] ⟨snapshot initial,logical⟩ initial initialReal (.ret (.literal i32 7)) (⟨⟨snapshot initial,logical⟩,some 7⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro).mono',
          '  intro p a same; subst p',
          '  exact Or.inl ⟨Or.inl rfl,rfl,.scalar 7,by rfl⟩)',
          'example := genericCall state realizes (NoScope.of_tags _ _ (by decide +kernel))']
        with tempfile.TemporaryDirectory(prefix='dynamic-stmt-effects-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'EffectsSource')
            checks[0]='import Proofs.DynamicEffectRuns\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['def pushCall := EffectsSource.push.callFuel 300 state [.vectorReference 0,.value (.literal i32 1),.value (.literal i32 1)]',
              '#guard (match pushCall with | .finished (s,.scalar x) => x == 3 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && s.frame.state.forest == state.frame.state.forest && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3)] | _ => false)',
              'def scopeCall := EffectsSource.scoped.callFuel 300 state [.vectorReference 1,.scalarReference 3]',
              '#guard (match scopeCall with | .finished (s,.scalar x) => x == 7 && s.scalars.memory == [⟨i32,7⟩,⟨i32,1⟩] && s.scope == state.scope && s.frame.bindings == state.frame.bindings | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};int r=cp::push(g,1,1);std::cout<<r<<" "<<g[1].back()<<" "<<g[1].capacity()<<std::endl;int x=1;std::cout<<cp::scoped(g,x)<<" "<<x<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['3 -3 4','7 7'])

if __name__=='__main__':
    disable_network();unittest.main()
