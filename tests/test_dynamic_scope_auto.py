"""Pure scope restoration preserves outer writes, heap changes and control."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_dynamic_expr import fixture_checks
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT=Path(__file__).resolve().parent.parent


class DynamicScopeAutoTests(unittest.TestCase):
    def test_scope_restoration_and_native_control(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicScopeAuto\n'+checks[0]
        checks += ['open Proofs.DynamicScopeAuto Proofs.DynamicControlBridge Proofs.CppNestedScope',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def entered : NState := {state with scope := state.scope+1}',
                   'theorem enteredReal : Realizes params st0.locals st0.contents entered := enter params st0 state realizes',
                   'def decl : NStmt := .declare i32 true (.literal i32 7)',
                   'def stA : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared st0.locals i32 true 7,logical⟩',
                   'def assign : NStmt := .assign 3 i32 (.variable i32 5)',
                   'def stB : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.assigned stA.locals ⟨0,true⟩ ⟨i32,1⟩ 7,logical⟩',
                   'def ret : NStmt := .ret (.variable i32 5)',
                   'def body : Command := .sequence (.primitive decl) (.sequence (.primitive assign) (.primitive ret))',
                   'theorem declPure : Proofs.DynamicStmt.run params decl st0 = some ⟨stA,none⟩ := by rfl',
                   'theorem assignPure : Proofs.DynamicStmt.run params assign stA = some ⟨stB,none⟩ := by rfl',
                   'theorem retPure : Proofs.DynamicStmt.run params ret stB = some ⟨stB,some 7⟩ := by rfl',
                   'theorem body_verified (s : NState) (real : Realizes params st0.locals st0.contents s) : Runs params body st0 {s with scope := s.scope+1} (fun p _ => p = ⟨stB,some 7,false⟩) := by',
                   '  apply Runs.seq',
                   '  have first := Proofs.DynamicAppendAuto.runs params st0 {s with scope := s.scope+1} (enter params st0 s real) decl _ declPure True.intro',
                   '  apply first.inspect.mono',
                   '  intro p a ⟨matched,same⟩; subst p; refine ⟨rfl,rfl,?_⟩',
                   '  apply Runs.seq',
                   '  have second := Proofs.DynamicAppendAuto.runs params stA a.state matched.state assign _ assignPure True.intro',
                   '  apply second.inspect.mono',
                   '  intro p b ⟨matched,same⟩; subst p; refine ⟨rfl,rfl,?_⟩',
                   '  exact Proofs.DynamicAppendAuto.runs params stB b.state matched.state ret _ retPure True.intro',
                   'def actualBody : NStep := match Proofs.CppNestedProgram.runFuel 20 body entered with | .finished r => r | _ => ⟨entered,none,false⟩',
                   'theorem actualRun : Proofs.CppNestedProgram.runFuel 20 body entered = .finished actualBody := by decide +kernel',
                   'theorem actualMatched : Matches params ⟨stB,some 7,false⟩ actualBody := by',
                   '  obtain ⟨p,a,_,⟨fuel,middle,ran,same⟩,matched,pEq⟩ := body_verified state realizes',
                   '  subst p; subst middle',
                   '  have equal := Proofs.CppNestedHoare.runFuel_success_unique fuel 20 body entered a actualBody ran actualRun',
                   '  subst a; exact matched',
                   'def restored : Proofs.DynamicStmt.State := ⟨⟨[⟨i32,7⟩,⟨i32,1⟩],st0.locals.bindings,st0.locals.slots⟩,logical⟩',
                   'theorem pureLeave : Proofs.DynamicControl.leave st0 stB = some restored := by rfl',
                   'theorem fresh : ∀ owner, actualBody.state.frame.state.forest.context owner ≠ some (state.scope+1) := fresh_of_tags _ _ (by decide +kernel)',
                   'example := leave_sound params st0 stB restored state actualBody.state realizes actualMatched.state (some 7) pureLeave fresh',
                   'theorem scopeVerified : Runs params (.scope body) st0 state (fun p a => p.state.locals.memory = [⟨i32,7⟩,⟨i32,1⟩] ∧ a.state.scalars.memory = p.state.locals.memory ∧ p.returned = some 7 ∧ a.returned = some (.scalar 7) ∧ a.state.scope = state.scope ∧ a.state.frame.bindings = base.bindings) := by',
                   '  apply Proofs.DynamicScopeAuto.scope params body st0 state realizes',
                   '  refine ⟨⟨stB,some 7,false⟩,actualBody,⟨20,_,by rfl,rfl⟩,⟨20,_,actualRun,rfl⟩,actualMatched,restored,pureLeave,fresh,?_⟩',
                   '  decide +kernel',
                   'example := scopeVerified.aligned',
                   'def root : NStmt := .appendRow (.local 0) i32',
                   'def stRoot : Proofs.DynamicStmt.State := ⟨snapshot state,putContents logical 0 (.rows i32 0 (values ++ [[]]))⟩',
                   'def grow : NState := ((root.run entered).getD ⟨entered,none,false⟩).state',
                   'theorem growReal : Realizes params stRoot.locals stRoot.contents grow := by',
                   '  have room : Proofs.DynamicAppendAuto.Available params st0 entered root := by',
                   '    intro p selected',
                   '    have chosen : Proofs.DynamicStmt.mutableRoot params st0 0 (.vector atom) = some p0 := by decide +kernel',
                   '    have same : p = p0 := Option.some.inj (selected.symm.trans chosen)',
                   '    subst p; exact ⟨(entered.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                   '  obtain ⟨out,run,matched⟩ := Proofs.DynamicAppendAuto.sound params st0 entered enteredReal root (⟨stRoot,none⟩ : Proofs.DynamicStmt.Step) (by rfl) room',
                   '  have same : grow = out.state := by simp [grow,run]',
                   '  rw [same]; exact matched.state',
                   'def stGrow : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared stRoot.locals i32 true 7,stRoot.contents⟩',
                   'def innerGrow : NState := ((decl.run grow).getD ⟨grow,none,false⟩).state',
                   'theorem innerGrowReal : Realizes params stGrow.locals stGrow.contents innerGrow := by',
                   '  obtain ⟨out,run,matched⟩ := Proofs.DynamicAppendAuto.sound params stRoot grow growReal decl (⟨stGrow,none⟩ : Proofs.DynamicStmt.Step) (by rfl) True.intro',
                   '  have same : innerGrow = out.state := by simp [innerGrow,run]',
                   '  rw [same]; exact matched.state',
                   'theorem growLeave : Proofs.DynamicControl.leave st0 stGrow = some stRoot := by rfl',
                   'theorem growFresh : ∀ owner, innerGrow.frame.state.forest.context owner ≠ some (state.scope+1) := fresh_of_tags _ _ (by decide +kernel)',
                   'example := leave_sound params st0 stGrow stRoot state innerGrow realizes innerGrowReal none growLeave growFresh',
                   '#guard (state.left innerGrow).scalars.memory.length == 2',
                   '#guard (state.left innerGrow).slots == state.slots',
                   '#guard (state.left innerGrow).frame.bindings == state.frame.bindings',
                   '#guard ((state.left innerGrow).frame.state.storage.lookup 0).map (fun b => b.items.length) == some 5',
                   '#guard (state.left innerGrow).frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2',
                   '#guard (state.left innerGrow).work == innerGrow.work+1',
                   'def wrongType : Proofs.DynamicStmt.State := ⟨{st0.locals with memory := [⟨⟨64,false,false⟩,1⟩,⟨i32,1⟩]},logical⟩',
                   'def shortMemory : Proofs.DynamicStmt.State := ⟨{st0.locals with memory := [⟨i32,1⟩]},logical⟩',
                   '#guard (Proofs.DynamicControl.leave st0 wrongType).isNone',
                   '#guard (Proofs.DynamicControl.leave st0 shortMemory).isNone',
                   'def owned : NState := (((NStmt.constructRows i32 true (.literal i32 0)).run entered).getD ⟨entered,none,false⟩).state',
                   '#guard owned.frame.state.forest.context state.frame.state.storage.objects.length == some (state.scope+1)',
                   'def ownedPure : Proofs.DynamicStmt.State := ⟨snapshot owned,logical⟩',
                   '#guard (Proofs.DynamicControl.leave st0 ownedPure).isSome',
                   'example : ¬ (∀ owner, owned.frame.state.forest.context owner ≠ some (state.scope+1)) := by',
                   '  intro fresh; exact fresh state.frame.state.storage.objects.length (by decide +kernel)',
                   '#guard (((state.leave owned none).getD state).frame.state.storage.lookup state.frame.state.storage.objects.length).isNone',
                   '#guard ((state.left owned).frame.state.storage.lookup state.frame.state.storage.objects.length).isSome']
        source_text='''#include <vector>
namespace cp {
int early(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& a,const std::vector<int>& other,int k,int j){{int x=a[k][j];k=7;return x+other[0];}return 0;}
int grow(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& a,const std::vector<int>& other,int k,int j){{int x=(int)a.size();g.emplace_back();k=x;}return k+(int)a.size()+other[0];}
int stopping(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& a,const std::vector<int>& other,int k,int j){while(k>0){{int x=a[k][j];if(x<0)break;k=k-1;}}return k+other[0];}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-scope-auto-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'ScopeAutoSource')
            checks[0]='import Proofs.DynamicScopeAuto\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicScopeAuto\n','').replace('import Proofs.DynamicReadSound\n','')
            for name,value,k,size in [('early',74,7,4),('grow',86,4,5),('stopping',78,1,4)]:
                checks += [f'def pure_{name} := Proofs.DynamicControl.runFuel params 150 ScopeAutoSource.{name}.body st0',
                           f'def actual_{name} := Proofs.CppNestedProgram.runFuel 150 ScopeAutoSource.{name}.body state',
                           f'#guard (match pure_{name},actual_{name} with | .finished p,.finished a => p.returned == some {value} && a.returned == some (.scalar {value}) && p.state.locals.memory == [⟨i32,{k}⟩,⟨i32,1⟩] && a.state.scalars.memory == p.state.locals.memory && a.state.slots == state.slots && a.state.frame.bindings == state.frame.bindings && a.state.scope == state.scope && !a.breaking && (a.state.frame.state.storage.lookup 0).map (fun b => b.items.length) == some {size} && a.state.frame.state.wellFormed | _,_ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<int> other{77};'+''.join(f'{{std::vector<std::vector<int>> g{{{{10,0}},{{17,-3}},{{}},{{}}}};std::cout<<cp::{name}(g,g,other,1,1)<<" "<<g.size()<<std::endl;}}' for name in ['early','grow','stopping'])+'}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['74 4','86 5','78 4'])


if __name__ == '__main__':
    disable_network(); unittest.main()
