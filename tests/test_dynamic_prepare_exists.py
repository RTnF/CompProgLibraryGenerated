"""Pure arguments construct prepare, including immutable roots and old refs."""
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


class DynamicPrepareExistsTests(unittest.TestCase):
    def test_construct_prepare_without_runtime_success_premise(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicPrepareExists\n'+checks[0]
        checks += ['open Proofs.CppNestedCall Proofs.DynamicBoundArguments',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def difference : NExpr := .binary i32 .sub rowRead rowRead',
                   'def abi : List Proofs.CppVectorBindings.Parameter := [.nested i32 true,.scalar i32 false true,.nested i32 false,.scalar i32 true true,.vector i32 false,.scalar i32 false true]',
                   'def args : List NArgument := [.vectorReference 0,.value combined,.vectorReference 1,.scalarReference 3,.vectorReference 2,.value difference]',
                   'def rs : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 true,.scalar i32 true 1,.nestedRoot 0 0 i32 false,.scalarAddress i32 0 true,.vector 2 1 i32 false,.scalar i32 true 0]',
                   'theorem pureArgs : Proofs.DynamicArguments.resolveAll params st0 abi args = some rs := by decide +kernel',
                   'def preparation (s : NState) (real : Realizes params st0.locals st0.contents s) := Proofs.DynamicPrepareExists.prepare params st0 s real abi args rs pureArgs',
                   'def callee : NState := (prepare state abi args).getD state',
                   'def calleeParams := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 rs',
                   'theorem calleeReal : Realizes calleeParams (snapshot callee) logical callee := by',
                   '  obtain ⟨t,ran,real,_⟩ := preparation state realizes',
                   '  have same : callee = t := by simp [callee,ran]',
                   '  rw [same]; exact real',
                   '#guard callee.scalars.memory.length == 9',
                   '#guard callee.scalars.bindings == [⟨7,true⟩,⟨0,true⟩,⟨8,true⟩]',
                   '#guard callee.frame.rootWritable == state.frame.rootWritable',
                   '#guard callee.frame.bindings.map (·.writable) == [true,false,false]',
                   '#guard callee.scope == state.scope+1',
                   'example (params : List Parameter) (l : Locals) (h : ContentsHeap) (e : NExpr) (v : Int) (pure : Proofs.DynamicExpr.denote params l h e = some v) : e.resultType.valid v = true := Proofs.DynamicResultValid.expression params l h e v pure']
        typed_cases=[('combined',1),('rowRead',-3),('rowSize',2),('difference',0),
                     ('.cast ⟨8,false,false⟩ rowRead',253),('.cast ⟨1,false,true⟩ rowRead',1),
                     ('.targetCast i32 (.literal ⟨64,false,false⟩ 4294967295)',-1),
                     ('.targetCast ⟨64,true,false⟩ (.literal ⟨64,false,false⟩ 18446744073709551615)',-1),
                     ('.divrem i32 false rowRead (.literal i32 2)',-1),('.divrem i32 true rowRead (.literal i32 2)',-1),
                     ('.logical true (.literal i32 0) bad',0),('.logical false (.literal i32 1) bad',1)]
        for expr,value in typed_cases:
            checks += [f'example : (({expr}) : NExpr).resultType.valid ({value}) = true := Proofs.DynamicResultValid.expression params (snapshot state) logical _ _ (by decide +kernel)']
        checks += ['example : ¬ Boundable heap state (.scalar i32 true 2147483648) := by change ¬ i32.valid 2147483648 = true; decide +kernel',
                   'example : ¬ Boundable heap state (.scalarAddress i32 999 true) := by',
                   '  intro ⟨cell,found,_⟩; have missing : state.scalars.memory[999]? = none := by decide +kernel',
                   '  rw [missing] at found; contradiction',
                   'def pConst : Parameter := ⟨1,0,row,0,false,false⟩',
                   'def constCaller : NState := {state with frame := {state.frame with rootWritable := state.frame.rootWritable.set 0 false,bindings := state.frame.bindings.set 0 ⟨0,row,false,.root 0⟩}}',
                   'theorem constFamily : Family [pConst] heap constCaller.frame (resources constCaller.frame) := by',
                   '  refine ⟨family.valid,family.models,by decide +kernel,?_,?_,?_,?_,measured_resources _⟩',
                   '  · intro p hp; simp only [List.mem_singleton] at hp; subst p; decide +kernel',
                   '  · intro p hp; simp only [List.mem_singleton] at hp; subst p; decide +kernel',
                   '  · intro p hp; simp only [List.mem_singleton] at hp; subst p; simp [pConst]',
                   '  · intro p hp; simp only [List.mem_singleton] at hp; subst p; exact ⟨view,by decide +kernel,rfl,rfl⟩',
                   'def constState : Proofs.DynamicStmt.State := ⟨snapshot constCaller,logical⟩',
                   'theorem constReal : Realizes [pConst] constState.locals constState.contents constCaller := of_family [pConst] heap (resources constCaller.frame) constCaller constFamily',
                   'example := Proofs.DynamicPrepareExists.prepare [pConst] constState constCaller constReal [.nested i32 false] [.vectorReference 1] [.nestedRoot 0 0 i32 false] (by decide +kernel)',
                   'def constCallee := (prepare constCaller [.nested i32 false] [.vectorReference 1]).getD constCaller',
                   '#guard (constCallee.frame.bindings[0]?).map (·.writable) == some false',
                   '#guard (Proofs.DynamicFamilyInit.describe constCaller.frame.rootWritable 0 [.nestedRoot 0 0 i32 false]).map (·.maximum) == [false]',
                   '#guard (Proofs.DynamicArguments.resolveAll [pConst] constState [.nested i32 true] [.vectorReference 1]).isNone',
                   '#guard (prepare constCaller [.nested i32 true] [.vectorReference 1]).isNone',
                   'example : ¬ Boundable heap constCaller (.nestedRoot 0 0 i32 true) := by',
                   '  intro ⟨v,maximum,_,_,_,flag,permission⟩',
                   '  have known : constCaller.frame.rootWritable[0]? = some false := by decide +kernel',
                   '  have same : maximum = false := Option.some.inj (flag.symm.trans known)',
                   '  subst maximum; have bad : false = true := permission rfl; contradiction',
                   'example := Proofs.DynamicPrepareExists.prepare params st0 state realizes [] [] [] rfl',
                   'def empty := (prepare state [] []).getD state',
                   '#guard empty.slots.isEmpty && empty.frame.bindings.isEmpty',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 false true] [.value (.binary i32 .add (.literal i32 2147483647) combined)]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 true true] [.scalarReference 99]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 abi (args.drop 1)).isNone']
        source_text='''#include <vector>
namespace cp {int mixed(std::vector<std::vector<int>>& g,int x,const std::vector<std::vector<int>>& a,int& ref,const std::vector<int>& other,int y){ref=x+y+a[1][1];g[1].emplace_back(ref);return other[0]+g[1].size();}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-prepare-exists-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'PrepareExistsSource')
            checks[0]='import Proofs.DynamicPrepareExists\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicPrepareExists\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['#guard PrepareExistsSource.mixed.parameters == abi',
                       'def call := PrepareExistsSource.mixed.callFuel 300 state args',
                       '#guard (match call with | .finished (s,.scalar x) => x == 80 && s.scalars.memory == [⟨i32,-2⟩,⟨i32,1⟩] && s.slots == state.slots && s.frame.bindings == state.frame.bindings && s.frame.state.wellFormed && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-2)] && (s.frame.state.storage.lookup 4).map (·.capacity) == some 4 | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};int k=1,j=1;int result=cp::mixed(g,(int)g.size()+g[k][j],g,k,other,g[k][j]-g[k][j]);std::cout<<result<<" "<<k<<" "<<g[1].capacity()<<" "<<g[1].back()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['80 -2 4 -2'])


if __name__ == '__main__':
    disable_network(); unittest.main()
