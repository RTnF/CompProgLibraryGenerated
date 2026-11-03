"""Pure expression success constructs certificates without supplied lookups."""
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


class DynamicAutoTests(unittest.TestCase):
    def test_automatic_certificates_and_statements(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicStmtAuto\nimport Proofs.DynamicAppendIndex\n'+checks[0]
        checks += ['open Proofs.DynamicExprCertified',
                   'def nested : NExpr := .read i32 (.row (.local 1) atom combined) combined',
                   'def zeroIdx : NExpr := .binary i32 .add nested (.literal i32 3)',
                   'def flat : NExpr := .read i32 (.local 2) zeroIdx',
                   'def sized : NExpr := .size atom (.row (.local 1) atom combined)',
                   'def full : NExpr := .binary i32 .add (.binary i32 .add nested flat) (.cast i32 sized)',
                   'theorem automatic (e : NExpr) (v : Int) (success : Proofs.DynamicExpr.denote params (snapshot state) logical e = some v) : Atomic params (snapshot state) logical e v := Proofs.DynamicExprAuto.sound params _ _ e v success',
                   'theorem fullCert : Evaluation params (snapshot state) logical full 76 := Proofs.DynamicExprAuto.evaluation params _ _ full 76 (by decide +kernel)',
                   'example (s : NState) (r : Realizes params (snapshot state) logical s) := released fullCert s r',
                   'example (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) : Proofs.DynamicExprDerive.Ready params l h e := Proofs.DynamicExprAuto.ready params l h e']
        cases=[('rootSize',4),('rowSize',2),('rowRead',-3),('combined',1),('nested',-3),('flat',77),('sized',2),('full',76),
               ('.size atom (.local 2)',1),('.size atom (.row (.local 0) atom (.literal i32 2))',0),
               ('.targetCast ⟨8,false,false⟩ nested',253),('.unary i32 .neg nested',3),
               ('.divrem i32 false nested (.literal i32 2)',-1),('.divrem i32 true nested (.literal i32 2)',-1),
               ('.logical true (.literal i32 0) bad',0),('.logical false (.literal i32 1) bad',1),
               ('.logical true combined nested',1),('.logical false (.literal i32 0) nested',1)]
        for expr,value in cases:
            checks += [f'example : Atomic params (snapshot state) logical ({expr}) ({value}) := automatic _ _ (by decide +kernel)']
        checks += ['def failures : List NExpr := [bad,.read i32 (.row (.local 1) atom (.literal i32 2)) (.literal i32 0),.read i32 (.row (.row (.local 1) atom idx) atom idx) pos,.size atom (.row (.row (.local 1) atom idx) atom idx),.size atom (.local 1),.divrem i32 false full (.literal i32 0),.logical true (.literal i32 1) bad,.binary i32 .add (.literal i32 2147483647) combined]',
                   '#guard failures.all (fun e => (Proofs.DynamicExpr.denote params (snapshot state) logical e).isNone && (e.eval state).isNone)',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def decl : NStmt := .declare i32 true full',
                   'def st1 : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared st0.locals i32 true 76,logical⟩',
                   'theorem declPure : Proofs.DynamicStmt.run params decl st0 = some ⟨st1,none⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st0.locals st0.contents full = some 76 := by decide +kernel',
                   '  have convert : i32.convert 76 = some 76 := by decide +kernel',
                   '  simp only [decl,Proofs.DynamicStmt.run,value,Bind.bind,Option.bind,convert]; rfl',
                   'def actual1 := ((decl.run state).getD ⟨state,none,false⟩).state',
                   'theorem real1 : Realizes params st1.locals st1.contents actual1 := by',
                   '  obtain ⟨out,run,matched,_⟩ := Proofs.DynamicStmtAuto.scalar_sound params st0 state realizes decl True.intro _ declPure',
                   '  have same : actual1 = out.state := by simp [actual1,run]',
                   '  rw [same]; exact matched.state',
                   'def ret : NStmt := .ret (.binary i32 .add (.variable i32 5) flat)',
                   'theorem retPure : Proofs.DynamicStmt.run params ret st1 = some ⟨st1,some 153⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st1.locals st1.contents (.binary i32 .add (.variable i32 5) flat) = some 153 := by decide +kernel',
                   '  simp only [ret,Proofs.DynamicStmt.run,value,Bind.bind,Option.bind]',
                   'example := Proofs.DynamicStmtAuto.scalar_sound params st1 actual1 real1 ret True.intro _ retPure',
                   'example := Proofs.DynamicStmtAuto.scalar_runs params st0 state realizes decl True.intro _ declPure',
                   'example (s : NState) (r : Realizes params st0.locals st0.contents s) (room : Proofs.DynamicAppendValue.RoomAt s 0 1) :=',
                   '  Proofs.DynamicAppendIndex.appendChild params st0 s r 0 i32 p0 (by decide +kernel) 0 1 values [17,-3] (by decide +kernel) (by decide +kernel) combined nested (Proofs.DynamicExprAuto.ready _ _ _ _) (by decide +kernel) (-3) (Proofs.DynamicExprAuto.ready _ _ _ _) (by decide +kernel) (by decide +kernel) room',
                   'example : ¬ Proofs.DynamicStmtAuto.ScalarForm (.appendRow (.local 0) i32) := by intro bad; exact bad']
        source_text='''#include <vector>
namespace cp {
int inspect(const std::vector<std::vector<int>>& g,const std::vector<int>& other,int k,int j){return g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+other[g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+3]+(int)g[(int)g.size()+g[k][j]].size();}
int scalar(const std::vector<std::vector<int>>& g,const std::vector<int>& other,int k,int j){int x=g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+other[g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+3]+(int)g[(int)g.size()+g[k][j]].size();return x+other[g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+3];}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-auto-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'AutoSource')
            checks[0]='import Proofs.DynamicStmtAuto\nimport Proofs.DynamicAppendIndex\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicStmtAuto\n','').replace('import Proofs.DynamicAppendIndex\n','').replace('import Proofs.DynamicReadSound\n','')
            for name,value in [('inspect',76),('scalar',153)]:
                checks += [f'def call_{name} := AutoSource.{name}.callFuel 500 state [.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                           f'#guard (match call_{name} with | .finished (s,.scalar x) => x == {value} && s.frame.bindings == base.bindings && s.frame.state.wellFormed && s.scalars.memory == state.scalars.memory && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3)] | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};std::cout<<cp::inspect(g,other,1,1)<<std::endl;std::cout<<cp::scalar(g,other,1,1)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['76','153'])


if __name__ == '__main__':
    disable_network(); unittest.main()
