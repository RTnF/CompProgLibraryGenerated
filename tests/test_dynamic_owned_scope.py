"""Destroy owned rows and flat roots while retaining outer writes and grants."""
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
namespace cp {int owned(std::vector<std::vector<int>>&g,const std::vector<int>&other,int&x){int out=0;{std::vector<std::vector<int>>local(2);const std::vector<int>empty;std::vector<int>v(3,5);local[0].emplace_back(42);local.emplace_back();local[2].emplace_back(99);v.emplace_back(9);g[1].emplace_back(-7);x=9;int z=123;out=z;}return out+g[1].size()+other[0];}}
'''

class DynamicOwnedScopeTests(unittest.TestCase):
    def test_owned_cleanup_and_native_source(self):
        checks=fixture_checks()
        begin=next(i for i,s in enumerate(checks) if s.startswith('theorem model :'))
        end=next(i for i,s in enumerate(checks) if s.startswith('theorem family :'))
        outer_model='\n'.join(checks[begin:end]).replace('theorem model :','theorem outerModel :').replace('state.frame.state','inner.frame.state').replace('base.state.storage','inner.frame.state.storage').replace('0 view','0 outerView')
        checks += ['open Proofs.DynamicRetire',
          'def entered : NState := {state with scope := state.scope+1}']
        steps=[('.constructRows i32 true (.literal i32 2)'),('.declareVector i32 false'),('.fillVector i32 true (.literal i32 3) (.literal i32 5)'),('.append (.row (.local 5) atom (.literal i32 0)) i32 (.literal i32 42)'),('.appendRow (.local 5) i32'),('.append (.row (.local 5) atom (.literal i32 2)) i32 (.literal i32 99)'),('.append (.local 7) i32 (.literal i32 9)'),('.append (.row (.local 0) atom (.literal i32 1)) i32 (.literal i32 (-7))'),('.assign 3 i32 (.literal i32 9)'),('.declare i32 true (.literal i32 123)')]
        for i,stmt in enumerate(steps):
            previous='entered' if i==0 else f'step{i-1}'
            checks += [f'def step{i} : NState := (({stmt} : NStmt).run {previous}).getD ⟨{previous},none,false⟩ |>.state',
              f'#guard (({stmt} : NStmt).run {previous}).isSome']
        checks += ['def inner : NState := step9',
          'def outerView : View := .rows i32 0 [1,4,5,6] 2 [[10,0],[17,-3,-7],[],[]]',
          'def localView : View := .rows i32 3 [8,9,12] 1 [[42],[],[99]]',
          'def emptyView : View := .flat i32 3 []',
          'def filledView : View := .flat i32 3 [5,5,5,9]',
          'def allHeap : Heap := fun owner => if owner = 0 then some outerView else if owner = 2 then some (.flat i32 1 [77]) else if owner = 7 then some localView else if owner = 10 then some emptyView else if owner = 11 then some filledView else none',
          'def p3 : Parameter := ⟨3,7,row,3,true,true⟩',
          'def p4 : Parameter := ⟨4,10,atom,3,false,false⟩',
          'def p5 : Parameter := ⟨5,11,atom,3,true,true⟩',
          'def allParams := params ++ [p3,p4,p5]',outer_model,
          'theorem localModel : Models inner.frame.state 7 localView := by',
          '  refine ⟨⟨by decide +kernel,by decide +kernel,(inner.frame.state.storage.lookup 7).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩,rfl,?_⟩',
          '  intro k owner lookup',
          '  refine ⟨(inner.frame.state.storage.lookup owner).getD ⟨0,[],0,64,0⟩,?_,?_⟩',
          '  all_goals have bound : k < 3 := (List.getElem?_eq_some_iff.mp lookup).1',
          '  all_goals have positions : k = 0 ∨ k = 1 ∨ k = 2 := by omega',
          '  all_goals rcases positions with h|h|h <;> subst k <;> simp at lookup <;> subst owner',
          '  all_goals decide +kernel',
          'theorem allFamily : Family allParams allHeap inner.frame (resources inner.frame) := by',
          '  refine ⟨by decide +kernel,?_,by decide +kernel,?_,?_,?_,?_,measured_resources _⟩',
          '  · intro owner v found',
          '    by_cases zero : owner = 0',
          '    · subst owner; simp [allHeap] at found; subst v; exact outerModel',
          '    by_cases two : owner = 2',
          '    · subst owner; simp [allHeap] at found; subst v; exact ⟨by decide +kernel,by decide +kernel,(inner.frame.state.storage.lookup 2).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
          '    by_cases seven : owner = 7',
          '    · subst owner; simp [allHeap] at found; subst v; exact localModel',
          '    by_cases ten : owner = 10',
          '    · subst owner; simp [allHeap] at found; subst v; exact ⟨by decide +kernel,by decide +kernel,(inner.frame.state.storage.lookup 10).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
          '    by_cases eleven : owner = 11',
          '    · subst owner; simp [allHeap] at found; subst v; exact ⟨by decide +kernel,by decide +kernel,(inner.frame.state.storage.lookup 11).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
          '    simp [allHeap,zero,two,seven,ten,eleven] at found',
          '  · intro p member; simp [allParams,params] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
          '  · intro p member; simp [allParams,params] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
          '  · intro p member; simp [allParams,params] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel',
          '  · intro p member; simp [allParams,params] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl',
          '    all_goals first | exact ⟨outerView,by decide +kernel,rfl,rfl⟩ | exact ⟨.flat i32 1 [77],by decide +kernel,rfl,rfl⟩ | exact ⟨localView,by decide +kernel,rfl,rfl⟩ | exact ⟨emptyView,by decide +kernel,rfl,rfl⟩ | exact ⟨filledView,by decide +kernel,rfl,rfl⟩',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'def stInner : Proofs.DynamicStmt.State := ⟨snapshot inner,eraseHeap allHeap⟩',
          'theorem innerReal : Realizes allParams stInner.locals stInner.contents inner := of_family allParams allHeap (resources inner.frame) inner allFamily',
          'theorem subset : ∀ p ∈ params, p ∈ allParams := by intro p member; exact List.mem_append_left _ member',
          'theorem kept : ∀ p ∈ params, p.scope ≠ state.scope+1 := by',
          '  intro p member; simp [params] at member; rcases member with rfl|rfl|rfl <;> decide +kernel',
          'example := Family.retired allFamily (state.scope+1) subset kept',
          'example := frame_runs inner.frame 3 allFamily.valid',
          'def final : Proofs.DynamicStmt.State := ⟨⟨[⟨i32,9⟩,⟨i32,1⟩],st0.locals.bindings,st0.locals.slots⟩,retireContents stInner.contents 3⟩',
          'theorem pureLeave : Proofs.DynamicOwnedScope.leave st0 stInner 3 = some final := by cbv',
          'theorem finalReal : Realizes params final.locals final.contents (Proofs.DynamicOwnedScope.left state inner) := (Proofs.DynamicOwnedScope.sound params allParams st0 stInner final state inner realizes innerReal subset kept (some 123) pureLeave).2.1',
          'example := Proofs.DynamicOwnedScope.sound params allParams st0 stInner final state inner realizes innerReal subset kept none pureLeave',
          'example := Proofs.DynamicOwnedScope.left_peak state inner (by decide +kernel)',
          'def restored := Proofs.DynamicOwnedScope.left state inner',
          '#guard state.leave inner (some (.scalar 123)) == some restored',
          '#guard restored.scalars.memory == [⟨i32,9⟩,⟨i32,1⟩]',
          '#guard restored.slots == state.slots',
          '#guard restored.frame.bindings == state.frame.bindings',
          '#guard restored.scope == state.scope',
          '#guard restored.frame.state.wellFormed',
          '#guard restored.frame.state.storage.objects.length == inner.frame.state.storage.objects.length',
          '#guard inner.frame.state.destroyWork 3 == 9',
          '#guard restored.work == inner.work+10',
          '#guard final.contents 0 == some (.rows i32 0 [[10,0],[17,-3,-7],[],[]])',
          '#guard final.contents 2 == logical 2',
          '#guard [7,8,9,10,11,12].all (fun owner => (restored.frame.state.storage.lookup owner).isNone && (restored.frame.state.forest.lookup owner).isNone)',
          '#guard [7,10,11].all (fun owner => (final.contents owner).isNone)',
          '#guard (restored.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-7)]',
          'example : ¬ Proofs.DynamicForestEffects.NoScope inner.frame.state.forest 3 := by intro absent; exact absent 8 (by decide +kernel)',
          'example : ¬ (p3.scope ≠ state.scope+1) := by decide +kernel',
          'def wrong : Proofs.DynamicStmt.State := ⟨{stInner.locals with memory := [⟨⟨64,false,false⟩,9⟩,⟨i32,1⟩]},stInner.contents⟩',
          '#guard (Proofs.DynamicOwnedScope.leave st0 wrong 3).isNone',
          'def next := ((NStmt.declareVector i32 true).run restored).getD ⟨restored,none,false⟩ |>.state',
          '#guard next.frame.state.storage.objects.length == 14',
          '#guard next.frame.state.forest.context 13 == some 2',
          '#guard (next.frame.state.storage.lookup 7).isNone',
          '#guard final.contents 7 == none']
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-scope-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'OwnedSource')
            checks[0]='import Proofs.DynamicOwnedScope\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['def call := OwnedSource.owned.callFuel 600 state [.vectorReference 0,.vectorReference 2,.scalarReference 3]',
              '#guard (match call with | .finished (s,.scalar x) => x == 203 && s.scalars.memory == [⟨i32,9⟩,⟨i32,1⟩] && s.frame.bindings == state.frame.bindings && s.scope == state.scope && s.frame.state.wellFormed && [7,8,9,10,11,12].all (fun owner => (s.frame.state.storage.lookup owner).isNone) | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::vector<int> other{77};int x=1;int r=cp::owned(g,other,x);std::cout<<r<<" "<<x<<" "<<g[1].back()<<" "<<g[1].size()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['203 9 -7 3'])

if __name__=='__main__':
    disable_network();unittest.main()
