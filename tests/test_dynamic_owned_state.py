"""Pure owned constructors carry allocation and reference cursors exactly."""
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
namespace cp {int owned(const std::vector<std::vector<int>>&g,int k,int j){std::vector<std::vector<int>>local((int)g.size()+g[k][j]);const std::vector<int>empty;const std::vector<int>v(g[k].size(),g[k][j]);return (int)local.size()+(int)empty.size()+v[0];}}
'''

class DynamicOwnedStateTests(unittest.TestCase):
    def test_pure_owned_constructors_and_generic_pipeline(self):
        checks=fixture_checks()
        checks += ['def entered : NState := {state with scope := 3}',
          'def owned0 : Proofs.DynamicOwnedState.State := ⟨⟨snapshot entered,logical⟩,params,7,3,3⟩',
          'theorem initialReal : Proofs.DynamicOwnedState.Realizes owned0 entered := ⟨of_family params heap (resources state.frame) entered family,by decide +kernel,by decide +kernel,rfl⟩',
          'def rowsStmt : NStmt := .constructRows i32 true combined',
          'def emptyStmt : NStmt := .declareVector i32 false',
          'def fillStmt : NStmt := .fillVector i32 false rowSize rowRead',
          'def owned1 := (Proofs.DynamicOwnedState.runConstruct rowsStmt owned0).getD owned0',
          'def owned2 := (Proofs.DynamicOwnedState.runConstruct emptyStmt owned1).getD owned1',
          'def owned3 := (Proofs.DynamicOwnedState.runConstruct fillStmt owned2).getD owned2',
          'theorem pure1 : Proofs.DynamicOwnedState.runConstruct rowsStmt owned0 = some owned1 := by cbv',
          'theorem pure2 : Proofs.DynamicOwnedState.runConstruct emptyStmt owned1 = some owned2 := by cbv',
          'theorem pure3 : Proofs.DynamicOwnedState.runConstruct fillStmt owned2 = some owned3 := by cbv',
          'def actual1 := (rowsStmt.run entered).getD ⟨entered,none,false⟩ |>.state',
          'def actual2 := (emptyStmt.run actual1).getD ⟨actual1,none,false⟩ |>.state',
          'def actual3 := (fillStmt.run actual2).getD ⟨actual2,none,false⟩ |>.state',
          'theorem real1 : Proofs.DynamicOwnedState.Realizes owned1 actual1 := by',
          '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned0 entered initialReal rowsStmt owned1 pure1',
          '  have same : actual1 = out := by simp [actual1,ran]',
          '  rw [same]; exact real',
          'theorem real2 : Proofs.DynamicOwnedState.Realizes owned2 actual2 := by',
          '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned1 actual1 real1 emptyStmt owned2 pure2',
          '  have same : actual2 = out := by simp [actual2,ran]',
          '  rw [same]; exact real',
          'theorem real3 : Proofs.DynamicOwnedState.Realizes owned3 actual3 := by',
          '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned2 actual2 real2 fillStmt owned3 pure3',
          '  have same : actual3 = out := by simp [actual3,ran]',
          '  rw [same]; exact real',
          'def body : Command := .sequence (.primitive rowsStmt) (.sequence (.primitive emptyStmt) (.primitive fillStmt))',
          'theorem pipeline (s : NState) (real : Proofs.DynamicOwnedState.Realizes owned0 s) : ∃ out, Proofs.CppNestedProgram.runFuel 3 body s = .finished ⟨out,none,false⟩ ∧ Proofs.DynamicOwnedState.Realizes owned3 out := by',
          '  obtain ⟨a,first,ra⟩ := Proofs.DynamicOwnedConstruct.sound owned0 s real rowsStmt owned1 pure1',
          '  obtain ⟨b,second,rb⟩ := Proofs.DynamicOwnedConstruct.sound owned1 a ra emptyStmt owned2 pure2',
          '  obtain ⟨c,third,rc⟩ := Proofs.DynamicOwnedConstruct.sound owned2 b rb fillStmt owned3 pure3',
          '  refine ⟨c,?_,rc⟩',
          '  simp [Proofs.CppNestedProgram.runFuel,body,first,second,third,Proofs.CppLoop.liftChecked,bind,pure,Proofs.CppLoop.Outcome.bind]',
          'example := pipeline entered initialReal',
          '#guard owned0.nextOwner == 7',
          '#guard owned1.nextOwner == 9 && owned2.nextOwner == 10 && owned3.nextOwner == 11',
          '#guard owned1.nextBinding == 4 && owned2.nextBinding == 5 && owned3.nextBinding == 6',
          '#guard owned3.params.map (·.owner) == [0,0,2,7,9,10]',
          '#guard owned3.params.map (·.writable) == [true,false,false,true,false,false]',
          '#guard owned3.params.map (·.maximum) == [true,true,true,true,false,false]',
          '#guard owned3.core.contents 7 == some (.rows i32 3 [[]])',
          '#guard (owned3.core.contents 8).isNone',
          '#guard owned3.core.contents 9 == some (.flat i32 3 [])',
          '#guard owned3.core.contents 10 == some (.flat i32 3 [-3,-3])',
          '#guard owned3.core.contents 0 == logical 0 && owned3.core.contents 2 == logical 2',
          '#guard owned3.core.locals.memory == owned0.core.locals.memory',
          '#guard actual3.frame.bindings.length == owned3.nextBinding',
          '#guard actual3.frame.state.storage.objects.length == owned3.nextOwner',
          '#guard actual3.scope == owned3.scope',
          '#guard (actual3.frame.state.storage.lookup 3).isNone',
          '#guard ((NStmt.append (.local 7) i32 (.literal i32 1)).run actual3).isNone',
          'def readNew : NExpr := .read i32 (.local 7) (.literal i32 1)',
          'example := Proofs.DynamicExprCertified.sound (Proofs.DynamicExprDerive.derive (Proofs.DynamicExprAuto.ready owned3.params owned3.core.locals owned3.core.contents readNew) (-3) (by decide +kernel)) actual3 real3.data',
          'def badCursor : Proofs.DynamicOwnedState.State := {owned0 with nextOwner := 3}',
          'example : ¬ Proofs.DynamicOwnedState.Realizes badCursor entered := by',
          '  intro real; have bad := real.owner',
          '  have count : entered.frame.state.storage.objects.length = 7 := by decide +kernel',
          '  rw [count] at bad; contradiction',
          'def badBinding : Proofs.DynamicOwnedState.State := {owned0 with nextBinding := 4}',
          'example : ¬ Proofs.DynamicOwnedState.Realizes badBinding entered := by',
          '  intro real; have bad := real.binding',
          '  have count : entered.frame.bindings.length = 3 := by decide +kernel',
          '  rw [count] at bad; contradiction',
          'def badScope : Proofs.DynamicOwnedState.State := {owned0 with scope := 4}',
          'example : ¬ Proofs.DynamicOwnedState.Realizes badScope entered := by intro real; have bad := real.scopedState; contradiction',
          'def zero : NExpr := .binary i32 .sub rowRead rowRead',
          'def zeroRows := (Proofs.DynamicOwnedState.runConstruct (.constructRows i32 false zero) owned0).getD owned0',
          'example := Proofs.DynamicOwnedConstruct.sound owned0 entered initialReal (.constructRows i32 false zero) zeroRows (by cbv)',
          '#guard zeroRows.nextOwner == 8 && zeroRows.nextBinding == 4',
          'def zeroFill := (Proofs.DynamicOwnedState.runConstruct (.fillVector i32 true zero rowRead) owned0).getD owned0',
          'example := Proofs.DynamicOwnedConstruct.sound owned0 entered initialReal (.fillVector i32 true zero rowRead) zeroFill (by cbv)',
          '#guard zeroFill.core.contents 7 == some (.flat i32 3 [])',
          '#guard (Proofs.DynamicOwnedState.runConstruct (.constructRows i32 true rowRead) owned0).isNone',
          '#guard (Proofs.DynamicOwnedState.runConstruct (.fillVector i32 true (.literal i32 1) (.literal ⟨64,false,false⟩ 2147483648)) owned0).isNone',
          '#guard (Proofs.DynamicOwnedState.runConstruct (.declareVector ⟨16,true,false⟩ true) owned0).isNone',
          '#guard (Proofs.DynamicOwnedState.runConstruct (.declare i32 true (.literal i32 1)) owned0).isNone']
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-state-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'OwnedStateSource')
            checks[0]='import Proofs.DynamicOwnedConstruct\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['def call := OwnedStateSource.owned.callFuel 600 state [.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]',
              '#guard (match call with | .finished (s,.scalar x) => x == -2 && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && [7,8,9,10].all (fun owner => (s.frame.state.storage.lookup owner).isNone) | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::cout<<cp::owned(g,1,1)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['-2'])

if __name__=='__main__':
    disable_network();unittest.main()
