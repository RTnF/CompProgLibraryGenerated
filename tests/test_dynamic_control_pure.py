"""Pure control flow, coupled termination, and AST/native correspondence."""
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

ROOT = Path(__file__).resolve().parent.parent


class DynamicPureControlTests(unittest.TestCase):
    def test_control_and_coupled_rules(self):
        checks = fixture_checks()
        checks[0] = 'import Proofs.DynamicControlBridge\n'+checks[0]
        checks += ['open Proofs.DynamicControlBridge Proofs.DynamicExprDerive',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def one : NExpr := .literal i32 1',
                   'def stopLoop : Command := .whileLoop one .breakLoop',
                   'theorem stop_verified (st : Proofs.DynamicStmt.State) (s : NState) (real : Realizes params st.locals st.contents s) :',
                   '    Proofs.DynamicControlBridge.Runs params stopLoop st s (fun p a => p.returned = none ∧ p.breaking = false ∧ a.returned = none ∧ a.breaking = false) := by',
                   '  apply Proofs.DynamicControlBridge.Runs.whileGhostStop (fun _ _ _ => True) _ (step := ?_) 0 st s real True.intro',
                   '  intro g st s real inv',
                   '  refine ⟨1,by rfl,Ready.scalar _ rfl,?_⟩',
                   '  intro next evaluated preserved',
                   '  refine ⟨by intro impossible; omega,?_⟩',
                   '  intro nonzero',
                   '  apply Proofs.DynamicControlBridge.Runs.of_run (fuel := 1) (pure := ⟨st,none,true⟩) (actual := ⟨((next.release s).charge 1 0).charge 1 0,none,true⟩)',
                   '  · rfl',
                   '  · rfl',
                   '  · exact ⟨⟨preserved.locals,preserved.heap⟩,rfl,rfl⟩',
                   '  · exact Or.inr ⟨rfl,Or.inl ⟨rfl,rfl,rfl,rfl,rfl⟩⟩',
                   'example := (stop_verified st0 state realizes).aligned',
                   'def returnLoop : Command := .whileLoop one (.sequence (.primitive (.ret (.literal i32 77))) (.primitive (.check (.literal i32 0))))',
                   'theorem return_verified (st : Proofs.DynamicStmt.State) (s : NState) (real : Realizes params st.locals st.contents s) :',
                   '    Proofs.DynamicControlBridge.Runs params returnLoop st s (fun p a => p.returned = some 77 ∧ a.returned = some (.scalar 77)) := by',
                   '  apply Proofs.DynamicControlBridge.Runs.whileGhostStop (fun _ _ _ => True) _ (step := ?_) 0 st s real True.intro',
                   '  intro g st s real inv',
                   '  refine ⟨1,by rfl,Ready.scalar _ rfl,?_⟩',
                   '  intro next evaluated preserved',
                   '  refine ⟨by intro impossible; omega,?_⟩',
                   '  intro nonzero',
                   '  apply Proofs.DynamicControlBridge.Runs.sequence',
                   '  have r := Proofs.DynamicControlBridge.Runs.scalar (stmt := .ret (.literal i32 77)) preserved (Ready.scalar (.literal i32 77) rfl) (⟨st,some 77⟩ : Proofs.DynamicStmt.Step) (by rfl)',
                   '  apply r.inspect.mono',
                   '  intro p a post; obtain ⟨matched,rfl,_,_⟩ := post',
                   '  exact Or.inl ⟨Or.inl rfl,Or.inl ⟨rfl,rfl,matched.returned⟩⟩',
                   'example := (return_verified st0 state realizes).aligned',
                   'example : Proofs.DynamicControlBridge.Runs params (.branch one (.primitive .skip) (.primitive (.check (.literal i32 0)))) st0 state (fun _ _ => True) := by',
                   '  apply Proofs.DynamicControlBridge.Runs.branch realizes (Ready.scalar _ rfl) (by rfl)',
                   '  intro next evaluated preserved',
                   '  change Proofs.DynamicControlBridge.Runs params (.primitive .skip) st0 ((next.release state).charge 1 0) _',
                   '  exact (Proofs.DynamicControlBridge.Runs.scalar (stmt := .skip) preserved True.intro (⟨st0,none⟩ : Proofs.DynamicStmt.Step) rfl).mono (fun _ _ _ => True.intro)',
                   'def countE : NExpr := .variable i32 3',
                   'def decrement : Command := .primitive (.assign 3 i32 (.binary i32 .sub countE one))',
                   'def counter (n : Int) : Proofs.DynamicStmt.State := ⟨{st0.locals with memory := [⟨i32,n⟩,⟨i32,1⟩]},logical⟩',
                   'def CountInv (g : Nat) (st : Proofs.DynamicStmt.State) : Prop := (g=3 ∧ st=counter 3) ∨ (g=2 ∧ st=counter 2) ∨ (g=1 ∧ st=counter 1) ∨ (g=0 ∧ st=counter 0)',
                   'theorem count_terminates : Proofs.DynamicControlHoare.Runs params (.whileLoop countE decrement) (counter 3) (fun p => p.state.locals.memory = (counter 0).locals.memory ∧ p.returned = none ∧ p.breaking = false) := by',
                   '  apply Proofs.DynamicControlHoare.Runs.whileGhostStop CountInv _ (step := ?_) 3 (counter 3) (by simp [CountInv])',
                   '  intro g st inv',
                   '  rcases inv with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩']
        for n in (3,2,1,0):
            checks += [f'  · refine ⟨{n},by decide +kernel,?_,?_⟩']
            if n:
                checks += ['    · intro impossible; omega',
                           f'    · intro nz; refine ⟨1,⟨counter {n-1},none,false⟩,?_,Or.inr ⟨rfl,Or.inr ⟨rfl,{n-1},by omega,?_⟩⟩⟩',
                           '      · change Proofs.CppLoop.Outcome.finished _ = Proofs.CppLoop.Outcome.finished _',
                           '        congr 1', '      · simp [CountInv]']
            else:
                checks += ['    · intro zero; exact ⟨rfl,rfl,rfl⟩','    · intro impossible; omega']
        checks += ['theorem count_coupled (s : NState) (real : Realizes params (counter 3).locals (counter 3).contents s) : Proofs.DynamicControlBridge.Runs params (.whileLoop countE decrement) (counter 3) s (fun p _ => p.state.locals.memory = (counter 0).locals.memory ∧ p.returned = none ∧ p.breaking = false) := by',
                   '  apply Proofs.DynamicControlBridge.Runs.whileGhostStop (fun g st _ => CountInv g st) _ (step := ?_) 3 (counter 3) s real (by simp [CountInv])',
                   '  intro g st s real inv',
                   '  rcases inv with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩']
        for n in (3,2,1,0):
            checks += [f'  · refine ⟨{n},by decide +kernel,Ready.scalar _ rfl,?_⟩',
                       '    intro next evaluated preserved',
                       '    refine ⟨?_,?_⟩']
            if n:
                checks += ['    · intro impossible; omega',
                           '    · intro nz',
                           f'      have ran := Proofs.DynamicControlBridge.Runs.scalar (stmt := .assign 3 i32 (.binary i32 .sub countE one)) preserved (Ready.scalar _ rfl) (⟨counter {n-1},none⟩ : Proofs.DynamicStmt.Step) (by rfl)',
                           '      apply ran.mono',
                           '      intro p a post; obtain ⟨rfl,_,_⟩ := post',
                           f'      exact Or.inr ⟨rfl,Or.inr ⟨rfl,{n-1},by omega,by simp [CountInv,Proofs.DynamicControl.ofStmt]⟩⟩']
            else:
                checks += ['    · intro zero; exact ⟨rfl,rfl,rfl⟩','    · intro impossible; omega']
        checks += ['#guard (match Proofs.DynamicControl.runFuel params 0 stopLoop st0 with | .exhausted => true | _ => false)',
                   '#guard (match Proofs.DynamicControl.runFuel params 10 (.whileLoop one (.primitive .skip)) st0 with | .exhausted => true | _ => false)',
                   '#guard (match Proofs.DynamicControl.runFuel params 1 (.primitive (.check (.literal i32 0))) st0 with | .fault => true | _ => false)',
                   'def moreState : NState := {state with scalars := {state.scalars with memory := [⟨i32,3⟩,⟨i32,1⟩]}}',
                   'def morePure : Proofs.DynamicStmt.State := ⟨snapshot moreState,logical⟩',
                   'theorem moreReal : Realizes params morePure.locals morePure.contents moreState := ⟨rfl,realizes.heap⟩',
                   'example := (count_coupled moreState moreReal).aligned']
        source_text = '''#include <vector>
namespace cp {
int run(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,const std::vector<int>& other,int k,int j){while(k>0){{int local=k;if(local==2)g.emplace_back();g[1].emplace_back(alias[1][0]+local);}k=k-1;}return g[1].size()+other[0];}
int early(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,const std::vector<int>& other,int k,int j){while(k>0){if(k==2)break;g.emplace_back();k=k-1;}return g.size();}
int returning(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,const std::vector<int>& other,int k,int j){while(k>0){return alias[1][j]+other[0];}return 0;}
}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-control-pure-') as directory:
            scratch = Path(directory); source = scratch/'source.hpp'; source.write_text(source_text)
            generated = emit_lean(lower_source(source),'PureSource')
            checks[0] = 'import Proofs.DynamicControlBridge\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicControlBridge\n','').replace('import Proofs.DynamicReadSound\n','')
            for name, expected, rows, row_values in [('run',82,5,'[17,-3,20,19,18]'),('early',5,5,'[17,-3]'),('returning',74,4,'[17,-3]')]:
                checks += [f'def pure_{name} := Proofs.DynamicControl.runFuel params 200 PureSource.{name}.body morePure',
                           f'def actual_{name} := Proofs.CppNestedProgram.runFuel 200 PureSource.{name}.body moreState',
                           f'#guard (match pure_{name} with | .finished p => p.returned == some {expected} && !p.breaking && p.state.locals.memory.length == 2 && p.state.locals.slots.length == 5 && (p.state.contents 0).map (fun v => match v with | .rows _ _ xs => xs.length | _ => 0) == some {rows} && (p.state.contents 0).map (fun v => match v with | .rows _ _ xs => xs[1]?.getD [] | _ => []) == some {row_values} | _ => false)',
                           f'#guard (match pure_{name},actual_{name} with | .finished p,.finished a => p.state.locals.memory == a.state.scalars.memory && p.state.locals.slots == a.state.slots && p.returned.map Ret.scalar == a.returned && p.breaking == a.breaking && (a.state.frame.state.storage.lookup 4).map (fun b => b.items) == some (({row_values} : List Int).map Proofs.CppNestedVectorStore.Value.integer) && a.state.frame.state.wellFormed | _,_ => false)']
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); native = scratch/'native.cpp'; exe=scratch/'native'
            native.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<int> o{77};'+''.join(f'{{std::vector<std::vector<int>> g{{{{10,0}},{{17,-3}},{{}},{{}}}};std::cout<<cp::{name}(g,g,o,3,1)<<" "<<g.size()<<" "<<g[1].size()<<std::endl;}}' for name in ['run','early','returning'])+'}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(native),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['82 5 5','5 5 2','74 4 2'])


if __name__ == '__main__':
    disable_network(); unittest.main()
