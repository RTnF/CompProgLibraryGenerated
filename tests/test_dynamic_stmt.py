"""Pure scalar statements and mixed vector-read append preserve Realizes."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_dynamic_expr import fixture_checks
from test_scalar_ir import lean_environment
from nested_ir import lower_source,emit_lean
from check_public import FLAGS,check_compiler
from offline import disable_network

ROOT=Path(__file__).resolve().parent.parent


class DynamicStmtTests(unittest.TestCase):
    def test_scalar_chain_and_reallocating_append_value(self):
        checks=fixture_checks();checks[0]='import Proofs.DynamicAppendValue\n'+checks[0]
        checks += ['open Proofs.DynamicExprCertified Proofs.DynamicExprDerive Proofs.DynamicScalarSound',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'theorem rootReady : Ready params st0.locals st0.contents rootSize := known (by decide +kernel) (Proofs.DynamicExprAtoms.root_size params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 values (by decide +kernel) (by decide +kernel))',
                   'theorem readReady : Ready params st0.locals st0.contents rowRead := known (by decide +kernel) (Proofs.DynamicExprAtoms.row_read params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] idx pos (-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'theorem combinedReady : Ready params st0.locals st0.contents combined := Ready.binary _ _ _ _ (Ready.cast _ _ rootReady) readReady',
                   'def decl : NStmt := .declare i32 true combined',
                   'def st1 : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared st0.locals i32 true 1,logical⟩',
                   'theorem declPure : Proofs.DynamicStmt.run params decl st0 = some ⟨st1,none⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st0.locals st0.contents combined = some 1 := by decide +kernel',
                   '  have converted : i32.convert 1 = some 1 := by decide +kernel',
                   '  simp only [decl,Proofs.DynamicStmt.run,value,Bind.bind,Option.bind,converted]; rfl',
                   'def actual1 := ((decl.run state).getD ⟨state,none,false⟩).state',
                   'theorem real1 : Realizes params st1.locals st1.contents actual1 := by',
                   '  obtain ⟨out,run,matched,_⟩ := Proofs.DynamicScalarSound.sound params st0 state realizes decl combinedReady _ declPure',
                   '  have same : actual1 = out.state := by simp [actual1,run]',
                   '  rw [same]; exact matched.state',
                   'theorem sizeReady1 : Ready params st1.locals st1.contents rowSize := known (by decide +kernel) (Proofs.DynamicExprAtoms.row_size params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 values [17,-3] idx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'def assignE : NExpr := .binary i32 .add (.variable i32 5) (.cast i32 rowSize)',
                   'theorem assignReady : Ready params st1.locals st1.contents assignE := Ready.binary _ _ _ _ (Ready.scalar _ (by decide +kernel)) (Ready.cast _ _ sizeReady1)',
                   'def assignStmt : NStmt := .assign 5 i32 assignE',
                   'def st2 : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.assigned st1.locals ⟨2,true⟩ ⟨i32,1⟩ 3,logical⟩',
                   'theorem assignPure : Proofs.DynamicStmt.run params assignStmt st1 = some ⟨st2,none⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st1.locals st1.contents assignE = some 3 := by decide +kernel',
                   '  have cell : Proofs.DynamicStmt.scalarCell st1.locals 5 i32 = some (⟨2,true⟩,⟨i32,1⟩) := by decide +kernel',
                   '  have converted : i32.convert 3 = some 3 := by decide +kernel',
                   '  simp only [assignStmt,Proofs.DynamicStmt.run,value,Bind.bind,Option.bind,cell,converted,ite_true]; rfl',
                   'def actual2 := ((assignStmt.run actual1).getD ⟨actual1,none,false⟩).state',
                   'theorem real2 : Realizes params st2.locals st2.contents actual2 := by',
                   '  obtain ⟨out,run,matched,_⟩ := Proofs.DynamicScalarSound.sound params st1 actual1 real1 assignStmt assignReady _ assignPure',
                   '  have same : actual2 = out.state := by simp [actual2,run]',
                   '  rw [same]; exact matched.state',
                   'def testE : NExpr := .binary ⟨1,false,true⟩ .eq (.variable i32 5) (.literal i32 3)',
                   'def checkStmt : NStmt := .check testE',
                   'theorem checkPure : Proofs.DynamicStmt.run params checkStmt st2 = some ⟨st2,none⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st2.locals st2.contents testE = some 1 := by decide +kernel',
                   '  simp [checkStmt,Proofs.DynamicStmt.run,value]',
                   'example : ∃ out, checkStmt.run actual2 = some out ∧ Matches params ⟨st2,none⟩ out ∧ out.state.work ≤ actual2.work+workBound checkStmt ∧ out.state.peak ≤ max actual2.peak (max actual2.scalars.peak (Proofs.CppNestedEval.liveS actual2+tempBound checkStmt)+actual2.frame.state.storage.peak) :=',
                   '  Proofs.DynamicScalarSound.sound params st2 actual2 real2 checkStmt (Ready.scalar _ (by decide +kernel)) _ checkPure',
                   'def flat : NExpr := .read i32 (.local 2) (.literal i32 0)',
                   'theorem flatReady2 : Ready params st2.locals st2.contents flat := known (by decide +kernel) (Proofs.DynamicExprAtoms.flat_read params _ _ 2 p2 (by decide +kernel) (by decide +kernel) i32 1 0 [77] (.literal i32 0) 77 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'def returnE : NExpr := .binary i32 .add (.variable i32 5) flat',
                   'theorem returnReady : Ready params st2.locals st2.contents returnE := Ready.binary _ _ _ _ (Ready.scalar _ (by decide +kernel)) flatReady2',
                   'def returnStmt : NStmt := .ret returnE',
                   'theorem returnPure : Proofs.DynamicStmt.run params returnStmt st2 = some ⟨st2,some 80⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote params st2.locals st2.contents returnE = some 80 := by decide +kernel',
                   '  simp [returnStmt,Proofs.DynamicStmt.run,value]',
                   'example : ∃ out, returnStmt.run actual2 = some out ∧ Matches params ⟨st2,some 80⟩ out ∧ out.state.work ≤ actual2.work+workBound returnStmt ∧ out.state.peak ≤ max actual2.peak (max actual2.scalars.peak (Proofs.CppNestedEval.liveS actual2+tempBound returnStmt)+actual2.frame.state.storage.peak) :=',
                   '  Proofs.DynamicScalarSound.sound params st2 actual2 real2 returnStmt returnReady _ returnPure',
                   '#guard (Proofs.DynamicStmt.run params (.check (.literal i32 0)) st2).isNone',
                   '#guard (Proofs.DynamicStmt.run params (.assign 5 ⟨64,false,false⟩ (.literal i32 1)) st2).isNone',
                   'def constState : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.declared st0.locals i32 false 1,logical⟩',
                   '#guard (Proofs.DynamicStmt.run params (.assign 5 i32 (.literal i32 1)) constState).isNone',
                   'def oldParent := (state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩',
                   'example := Proofs.DynamicAppendSound.appendRoot params st0 state realizes 0 i32 p0 (by decide +kernel) 0 values (by decide +kernel) oldParent (by decide +kernel) (by decide +kernel)',
                   'def appendValue : NExpr := .binary i32 .add (.targetCast i32 rootSize) rowRead',
                   'theorem valueReady : Ready params st0.locals st0.contents appendValue := Ready.binary _ _ _ _ (Ready.targetCast _ _ rootReady) readReady',
                   'theorem available : Proofs.DynamicAppendValue.RoomAt state 0 1 :=',
                   '  ⟨oldParent,4,(state.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
                   'example := Proofs.DynamicAppendValue.appendChild params st0 state realizes 0 i32 p0 (by decide +kernel) 0 1 values [17,-3] (by decide +kernel) (by decide +kernel) idx appendValue (by decide +kernel) (by decide +kernel) 1 valueReady (by decide +kernel) (by decide +kernel) available',
                   'def appendStmt : NStmt := .append (.row (.local 0) atom idx) i32 appendValue',
                   'def pureAppend := (Proofs.DynamicStmt.run params appendStmt st0).getD ⟨st0,none⟩',
                   '#guard pureAppend.state.contents 0 == some (.rows i32 0 [[10,0],[17,-3,1],[],[]])',
                   '#guard pureAppend.state.contents 2 == some (.flat i32 1 [77])',
                   'def actualAppend := ((appendStmt.run state).getD ⟨state,none,false⟩).state',
                   '#guard (actualAppend.frame.state.storage.lookup 4 |>.map (·.capacity)) == some 4',
                   '#guard (actualAppend.frame.state.storage.lookup 4 |>.map (·.items)) == some [.integer 17,.integer (-3),.integer 1]',
                   '#guard actualAppend.frame.bindings == base.bindings']
        source_text='''#include <vector>
#include <cassert>
namespace cp {
int scalar(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,const std::vector<int>& other,int k,int j){int x=(int)alias.size()+alias[k][j];x=x+(int)alias[k].size();assert(x==3);return x+other[0];}
int mutate(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& alias,const std::vector<int>& other,int k,int j){g[k].emplace_back((int)alias.size()+alias[k][j]);return g[k].size()+other[0];}
int add(std::vector<std::vector<int>>& g){g.emplace_back();return g.size();}}
'''
        native=['#include "experiments/library/cpp/template/small_template.hpp"','#include "source.hpp"','#include <iostream>','#include <cassert>',
                'int main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};',
                'std::cout<<cp::scalar(g,g,other,1,1)<<std::endl;',
                'std::cout<<cp::mutate(g,g,other,1,1)<<" "<<g[1].capacity()<<" "<<g[1].back()<<std::endl;',
                'assert(g[0][0]==10&&other[0]==77);',
                'std::cout<<cp::add(g)<<std::endl;}']
        with tempfile.TemporaryDirectory(prefix='dynamic-stmt-') as directory:
            scratch=Path(directory);fixture=scratch/'source.hpp';fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'StmtSource')
            checks[0]='import Proofs.DynamicAppendValue\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicAppendValue\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['def scalarCall := StmtSource.scalar.callFuel 300 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                       '#guard (match scalarCall with | .finished (s,.scalar x) => x == 80 && s.frame.state.wellFormed | _ => false)',
                       'def mutateCall := StmtSource.mutate.callFuel 300 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                       '#guard (match mutateCall with | .finished (s,.scalar x) => x == 80 && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer 1] && (s.frame.state.storage.lookup 4).map (·.capacity) == some 4 && s.frame.bindings == base.bindings && s.frame.state.wellFormed | _ => false)',
                       'def afterMutate := (match mutateCall with | .finished (s,_) => s | _ => state)',
                       'def addCall := StmtSource.add.callFuel 100 afterMutate [.vectorReference 0]',
                       '#guard (match addCall with | .finished (s,.scalar x) => x == 5 && s.frame.state.wellFormed && (s.frame.state.storage.lookup 2).map (·.items) == some [.integer 77] | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source,exe=scratch/'native.cpp',scratch/'native';source.write_text('\n'.join(native))
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0';result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['80','80 4 1','5'])


if __name__ == '__main__':
    disable_network()
    unittest.main()
