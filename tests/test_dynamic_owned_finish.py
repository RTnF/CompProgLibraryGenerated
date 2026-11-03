"""Call finish restores reordered caller bindings and retires owned locals."""
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
ROOT = Path(__file__).resolve().parent.parent
SOURCE = '''#include <vector>
namespace cp {std::vector<std::vector<int>> rows(const std::vector<int>&other,const std::vector<std::vector<int>>&g,int k,int j){
std::vector<int>flat;std::vector<std::vector<int>>local(2);std::vector<int>later;
local.emplace_back();local[2].push_back(g[k][j]);return local;}
void mutate(std::vector<std::vector<int>>&g){std::vector<int>local;g.emplace_back();}
}
'''
START = '''
 open Proofs.CppNestedCall
 def outerOwned : Proofs.DynamicOwnedState.State := ⟨⟨snapshot state,logical⟩,params,7,3,2⟩
 theorem outerReal : Proofs.DynamicOwnedState.Realizes outerOwned state := ⟨realizes,by decide +kernel,by decide +kernel,rfl⟩
 def abi := FinishCallSource.rows.parameters
 def args : List NArgument := [.vectorReference 2,.vectorReference 1,.value (.literal i32 1),.value (.literal i32 1)]
 def rs : List Proofs.CppNestedCall.Resolved := [.vector 2 1 i32 false,.nestedRoot 0 0 i32 false,.scalar i32 true 1,.scalar i32 true 1]
 theorem pureArgs : Proofs.DynamicArguments.resolveAll params ⟨snapshot state,logical⟩ abi args = some rs := by decide +kernel
 def callee : NState := (prepare state abi args).getD state
 theorem prepared : prepare state abi args = some callee := by decide +kernel
 theorem calleeReal : Proofs.DynamicRealizes.Realizes (Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 rs) (snapshot callee) logical callee := by
   obtain ⟨t,ran,real,_⟩ := Proofs.DynamicPrepareExists.prepare params ⟨snapshot state,logical⟩ state realizes abi args rs pureArgs
   have same : callee = t := by simp [callee,ran]
   simpa only [same] using real
 def owned0 := Proofs.DynamicResultCall.initialState outerOwned state callee rs
 theorem real0 : Proofs.DynamicOwnedState.Realizes owned0 callee := ⟨calleeReal,rfl,rfl,rfl⟩
 def freshIndex : NExpr := .cast ⟨64,false,false⟩ (.literal i32 2)
 def calleeRead : NExpr := .read i32 (.row (.local 1) atom (.cast ⟨64,false,false⟩ (.variable i32 2))) (.cast ⟨64,false,false⟩ (.variable i32 3))
 #guard owned0.params.map (·.owner) == [2,0]
 #guard owned0.nextBinding == 2 && outerOwned.nextBinding == 3
 #guard !(outerOwned.params.all (fun p => owned0.params.contains p))
'''

class DynamicOwnedFinishTests(unittest.TestCase):
    def test_reordered_prepare_owned_finish_and_complete_call(self):
        checks = fixture_checks()+[START]
        for before, after, stmt in [(0,1,'.declareVector i32 true'), (1,2,'.constructRows i32 true freshIndex'), (2,3,'.declareVector i32 true')]:
            initial = 'callee' if before == 0 else f'actual{before}'
            checks += [f'def stmt{after} : NStmt := {stmt}',
                f'def owned{after} := (Proofs.DynamicOwnedState.runConstruct stmt{after} owned{before}).getD owned{before}',
                f'def actual{after} := ((stmt{after}.run {initial}).getD ⟨{initial},none,false⟩).state',
                f'theorem real{after} : Proofs.DynamicOwnedState.Realizes owned{after} actual{after} := by',
                f'  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound owned{before} {initial} real{before} stmt{after} owned{after} (by cbv)',
                f'  have same : actual{after} = out := by simp [actual{after},ran]',
                '  rw [same]; exact real']
        checks += ['def stmt4 : NStmt := .appendRow (.local 5) i32',
            'def owned4 := (Proofs.DynamicOwnedAppend.run stmt4 owned3).getD owned3',
            'theorem room4 : Proofs.DynamicAppendAuto.RootRoom actual3 8 := ⟨(actual3.frame.state.storage.lookup 8).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
            'theorem avail4 : Proofs.DynamicOwnedAppend.Available owned3 actual3 stmt4 := by',
            '  intro p selected',
            '  have chosen : Proofs.DynamicStmt.mutableRoot owned3.params owned3.core 5 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true) := by decide +kernel',
            '  have same : p = Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)',
            '  subst p',
            '  have ownerEq : (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true).owner = 8 := by decide +kernel',
            '  rw [ownerEq]; exact room4',
            'def actual4 := ((stmt4.run actual3).getD ⟨actual3,none,false⟩).state',
            'theorem real4 : Proofs.DynamicOwnedState.Realizes owned4 actual4 := by',
            '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned3 actual3 real3 stmt4 owned4 (by cbv) avail4',
            '  have same : actual4 = out := by simp [actual4,ran]',
            '  rw [same]; exact real',
            'def stmt5 : NStmt := .append (.row (.local 5) atom freshIndex) i32 calleeRead',
            'def owned5 := (Proofs.DynamicOwnedAppend.run stmt5 owned4).getD owned4',
            'theorem room5 : Proofs.DynamicAppendValue.RoomAt actual4 8 2 := ⟨(actual4.frame.state.storage.lookup 8).getD ⟨0,[],0,64,0⟩,12,(actual4.frame.state.storage.lookup 12).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
            'theorem avail5 : Proofs.DynamicOwnedAppend.Available owned4 actual4 stmt5 := by',
            '  intro p k selected index',
            '  have chosen : Proofs.DynamicStmt.mutableRoot owned4.params owned4.core 5 (.vector atom) = some (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true) := by decide +kernel',
            '  have same : p = Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true := Option.some.inj (selected.symm.trans chosen)',
            '  subst p',
            '  have equal : (2 : Int) = k := Option.some.inj index',
            '  have pos : k = 2 := by omega',
            '  subst k',
            '  have ownerEq : (Proofs.DynamicOwnedState.newParameter owned1 (.vector atom) true).owner = 8 := by decide +kernel',
            '  rw [ownerEq]; exact room5',
            'def actual5 := ((stmt5.run actual4).getD ⟨actual4,none,false⟩).state',
            'theorem real5 : Proofs.DynamicOwnedState.Realizes owned5 actual5 := by',
            '  obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound owned4 actual4 real4 stmt5 owned5 (by cbv) avail5',
            '  have same : actual5 = out := by simp [actual5,ran]',
            '  rw [same]; exact real',
            'def returned : Ret := .vector 8 (.vector atom)',
            'def vectorKind : ResultKind := .vector (.vector atom)',
            'def rowsFinal := ((Proofs.DynamicOwnedFinish.finish outerOwned owned5 vectorKind (some returned)).getD (outerOwned,.unit)).1',
            'theorem pureFinish : Proofs.DynamicOwnedFinish.finish outerOwned owned5 vectorKind (some returned) = some (rowsFinal,returned) := by cbv',
            'theorem flags : ∃ extra, actual5.frame.rootWritable = state.frame.rootWritable ++ extra := ⟨[true,true,false,false,true,false],by decide +kernel⟩',
            'example (s t : NState) (before : Proofs.DynamicOwnedState.Realizes outerOwned s) (after : Proofs.DynamicOwnedState.Realizes owned5 t) (flags : ∃ extra, t.frame.rootWritable = s.frame.rootWritable ++ extra) := Proofs.DynamicOwnedFinish.sound outerOwned owned5 rowsFinal s t before after vectorKind (some returned) returned pureFinish flags',
            'def rowsOut := ((finish state actual5 vectorKind (some returned)).getD (state,.unit)).1',
            'theorem rowsReal : Proofs.DynamicOwnedState.Realizes rowsFinal rowsOut := by',
            '  obtain ⟨frame,out,_,ran,real,_⟩ := Proofs.DynamicOwnedFinish.sound outerOwned owned5 rowsFinal state actual5 outerReal real5 vectorKind (some returned) returned pureFinish flags',
            '  have same : rowsOut = out := by simp [rowsOut,ran]',
            '  rw [same]; exact real',
            '#guard rowsFinal.params == params && rowsFinal.nextOwner == 13 && rowsFinal.nextBinding == 3 && rowsFinal.scope == 2',
            '#guard rowsFinal.core.contents 8 == some (.rows i32 2 [[],[],[-3]])',
            '#guard rowsOut.frame.bindings == state.frame.bindings && rowsOut.scalars.memory == state.scalars.memory',
            '#guard [7,11].all (fun n => (rowsOut.frame.state.storage.lookup n).isNone)',
            '#guard [8,9,10,12].all (fun n => rowsOut.frame.state.forest.context n == some 2)',
            '#guard rowsOut.work == actual5.work+3',
            'def unitFinal := ((Proofs.DynamicOwnedFinish.finish outerOwned owned5 .unit none).getD (outerOwned,.unit)).1',
            'example := Proofs.DynamicOwnedFinish.sound outerOwned owned5 unitFinal state actual5 outerReal real5 .unit none .unit (by cbv) flags',
            'def scalarFinal := ((Proofs.DynamicOwnedFinish.finish outerOwned owned5 (.scalar i32) (some (.scalar 42))).getD (outerOwned,.unit)).1',
            'example := Proofs.DynamicOwnedFinish.sound outerOwned owned5 scalarFinal state actual5 outerReal real5 (.scalar i32) (some (.scalar 42)) (.scalar 42) (by cbv) flags',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned owned5 (.scalar i32) (some (.scalar 2147483648))).isNone',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned owned5 .unit (some .unit)).isNone',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned owned5 vectorKind (some (.vector 0 (.vector atom)))).isNone',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned owned5 vectorKind (some (.vector 8 atom))).isNone',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned {owned5 with core.locals.memory := []} vectorKind (some returned)).isNone',
            'def lostCaller := {owned5 with core.contents := putContents owned5.core.contents 2 (.flat i32 7 [77])}',
            '#guard (Proofs.DynamicOwnedFinish.finish outerOwned lostCaller vectorKind (some returned)).isNone',
            'open Proofs.DynamicResultRuns',
            'def body : Command := .sequence (.primitive stmt1) (.sequence (.primitive stmt2) (.sequence (.primitive stmt3) (.sequence (.primitive stmt4) (.sequence (.primitive stmt5) (.sequence (.primitive (.retVector 5)) (.primitive .skip))))))',
            'theorem generatedBody : FinishCallSource.rows.body = body := rfl']
        for before, after, room in [(0,1,None),(1,2,None),(2,3,None),(3,4,'avail4'),(4,5,'avail5')]:
            initial = 'callee' if before == 0 else f'actual{before}'
            ctor = f'Runs.primitive owned{before} {initial} real{before} stmt{after} ⟨owned{after},none,false⟩ (by cbv)' if room is None else f'Runs.append owned{before} {initial} real{before} stmt{after} owned{after} (by cbv) {room}'
            checks += [f'theorem part{after} : Runs (.primitive stmt{after}) owned{before} {initial} (fun p a => p = ⟨owned{after},none,false⟩ ∧ a.state = actual{after}) := by',
                f'  have run := ({ctor}).identify 1 ⟨actual{after},none,false⟩ (by cbv)',
                '  exact run.mono (fun p a ⟨ae,pe⟩ => ⟨pe,by rw [ae]⟩)']
        checks += ['theorem bodyRuns : Runs FinishCallSource.rows.body owned0 callee (fun p a => p = ⟨owned5,some returned,false⟩ ∧ a.state = actual5.charge 1 0) := by',
            '  rw [generatedBody]']
        for part in range(1,6):
            checks += [f'  apply Runs.seq; apply part{part}.mono', '  rintro p a ⟨pe,ae⟩; subst p; refine ⟨rfl,rfl,?_⟩; rw [ae]']
        checks += ['  apply Runs.sequence',
            '  have run := (Runs.retVector owned5 actual5 real5 5 returned (by cbv)).identify 1 ⟨actual5.charge 1 0,some returned,false⟩ (by cbv)',
            '  apply run.mono',
            '  rintro p a ⟨ae,pe,work⟩; subst p; exact Or.inl ⟨Or.inl rfl,rfl,by rw [ae]⟩',
            'theorem completeCall : ∃ (fuel : Nat) (final : Proofs.DynamicOwnedState.State) (next : NState) (value : Ret), FinishCallSource.rows.callFuel fuel state args = .finished (next,value) ∧ Proofs.DynamicOwnedState.Realizes final next := by',
            '  apply Proofs.DynamicResultCall.sound outerOwned state outerReal FinishCallSource.rows args rs pureArgs',
            '  intro initial ran real',
            '  have same : initial = callee := Option.some.inj (ran.symm.trans prepared)',
            '  subst initial',
            '  apply bodyRuns.mono',
            '  rintro p a ⟨pe,ae⟩; subst p',
            '  refine ⟨rfl,rowsFinal,returned,pureFinish,?_⟩',
            '  rw [ae]; exact flags',
            'def call := FinishCallSource.rows.callFuel 600 state args',
            '#guard (match call with | .finished (s,.vector root element) => root == 8 && element == .vector atom && s.frame.state.wellFormed && s.frame.bindings == state.frame.bindings && s.scalars.memory == state.scalars.memory && [7,11].all (fun n => (s.frame.state.storage.lookup n).isNone) && [8,9,10,12].all (fun n => s.frame.state.forest.context n == some 2) | _ => false)']
        checks += ["""
 def updateArgs : List NArgument := [.vectorReference 0]
 def updateRS : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 true]
 theorem updatePureArgs : Proofs.DynamicArguments.resolveAll params ⟨snapshot state,logical⟩ FinishCallSource.mutate.parameters updateArgs = some updateRS := by decide +kernel
 def updateInitial := (prepare state FinishCallSource.mutate.parameters updateArgs).getD state
 def update0 := Proofs.DynamicResultCall.initialState outerOwned state updateInitial updateRS
 theorem updateReal0 : Proofs.DynamicOwnedState.Realizes update0 updateInitial := by
   obtain ⟨t,ran,real,_⟩ := Proofs.DynamicPrepareExists.prepare params ⟨snapshot state,logical⟩ state realizes FinishCallSource.mutate.parameters updateArgs updateRS updatePureArgs
   have same : updateInitial = t := by simp [updateInitial,ran]
   refine ⟨?_,rfl,rfl,rfl⟩
   simpa only [same,update0,Proofs.DynamicResultCall.initialState,outerOwned] using real
 def update1 := (Proofs.DynamicOwnedState.runConstruct (.declareVector i32 true) update0).getD update0
 def updateActual1 := ((NStmt.declareVector i32 true).run updateInitial |>.getD ⟨updateInitial,none,false⟩).state
 theorem updateReal1 : Proofs.DynamicOwnedState.Realizes update1 updateActual1 := by
   obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedConstruct.sound update0 updateInitial updateReal0 (.declareVector i32 true) update1 (by cbv)
   have same : updateActual1 = out := by simp [updateActual1,ran]
   rw [same]; exact real
 def update2 := (Proofs.DynamicOwnedAppend.run (.appendRow (.local 0) i32) update1).getD update1
 theorem updateAvailable : Proofs.DynamicOwnedAppend.Available update1 updateActual1 (.appendRow (.local 0) i32) := by
   intro p selected
   have chosen : Proofs.DynamicStmt.mutableRoot update1.params update1.core 0 (.vector atom) = some p0 := by decide +kernel
   have same : p = p0 := Option.some.inj (selected.symm.trans chosen)
   subst p
   exact ⟨(updateActual1.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩
 def updateActual2 := ((NStmt.appendRow (.local 0) i32).run updateActual1 |>.getD ⟨updateActual1,none,false⟩).state
 theorem updateReal2 : Proofs.DynamicOwnedState.Realizes update2 updateActual2 := by
   obtain ⟨out,ran,real⟩ := Proofs.DynamicOwnedAppend.sound update1 updateActual1 updateReal1 (.appendRow (.local 0) i32) update2 (by cbv) updateAvailable
   have same : updateActual2 = out := by simp [updateActual2,ran]
   rw [same]; exact real
 def updateFinal := ((Proofs.DynamicOwnedFinish.finish outerOwned update2 .unit none).getD (outerOwned,.unit)).1
 example := Proofs.DynamicOwnedFinish.sound outerOwned update2 updateFinal state updateActual2 outerReal updateReal2 .unit none .unit (by cbv) (by exact ⟨[true,false],by decide +kernel⟩)
 #guard update0.nextBinding == 1 && updateFinal.nextBinding == 3 && updateFinal.nextOwner == 9
 #guard updateFinal.params == params && updateFinal.core.contents 0 == some (.rows i32 0 (values ++ [[]]))
 def updateCall := FinishCallSource.mutate.callFuel 100 state updateArgs
 #guard (match updateCall with | .finished (s,.unit) => s.frame.bindings == state.frame.bindings && s.frame.state.wellFormed && (s.frame.state.storage.lookup 7).isNone && s.frame.state.forest.context 8 == some 0 && (s.frame.state.storage.lookup 0).map (fun b => b.items.length) == some 5 | _ => false)
"""]
        with tempfile.TemporaryDirectory(prefix='dynamic-owned-finish-') as directory:
            scratch = Path(directory)
            source = scratch/'source.hpp'; source.write_text(SOURCE)
            generated = emit_lean(lower_source(source), 'FinishCallSource')
            checks[0] = 'import Proofs.DynamicResultCall\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n', '')
            proof = scratch/'checks.lean'; proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            check_compiler()
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>>g{{10,0},{17,-3},{},{}};std::vector<int>other{77};auto r=cp::rows(other,g,1,1);cp::mutate(g);std::cout<<r.size()<<" "<<r[2][0]<<" "<<other[0]<<" "<<g.size()<<std::endl;}')
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(exe)], cwd=ROOT, check=True)
            env = os.environ.copy(); env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)], cwd=ROOT, env=env, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), ['3 -3 77 5'])

if __name__ == '__main__':
    disable_network(); unittest.main()
