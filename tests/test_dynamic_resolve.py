"""Resolve arguments without manually rebuilding the post-resolution family."""
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


class DynamicResolveTests(unittest.TestCase):
    def test_pure_argument_resolution_and_prepare(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicCallPrepare\n'+checks[0]
        checks += ['open Proofs.CppNestedCall',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def difference : NExpr := .binary i32 .sub rowRead rowRead',
                   'def abi : List Proofs.CppVectorBindings.Parameter := [.nested i32 true,.scalar i32 false true,.nested i32 false,.scalar i32 true true,.vector i32 false,.scalar i32 false true]',
                   'def args : List NArgument := [.vectorReference 0,.value combined,.vectorReference 1,.scalarReference 3,.vectorReference 2,.value difference]',
                   'def rs : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 true,.scalar i32 true 1,.nestedRoot 0 0 i32 false,.scalarAddress i32 0 true,.vector 2 1 i32 false,.scalar i32 true 0]',
                   'theorem pureArgs : Proofs.DynamicArguments.resolveAll params st0 abi args = some rs := by decide +kernel',
                   'theorem generic_resolution (s : NState) (real : Realizes params st0.locals st0.contents s) :',
                   '    ∃ h m last, Proofs.CppNestedCall.resolveAll s abi args = some (last,rs) ∧ Family params h last.frame m ∧ (∀ r ∈ rs, Proofs.DynamicFamilyInit.Compatible h r) ∧ Realizes params st0.locals st0.contents last ∧ Proofs.CppNestedStmt.GoodF s last (Proofs.DynamicArguments.totalWork abi args) (Proofs.DynamicArguments.totalWork abi args) := by',
                   '  obtain ⟨h,m,family,erased⟩ := real.heap',
                   '  obtain ⟨last,run,good,ext,after,compatible,lastReal⟩ := Proofs.DynamicResolve.all_sound params st0 h m s family real abi args rs pureArgs',
                   '  exact ⟨h,m,last,run,after,compatible,lastReal,good⟩',
                   'example (s callee : NState) (real : Realizes params st0.locals st0.contents s) (prepared : prepare s abi args = some callee) := Proofs.DynamicCallPrepare.sound params st0 s callee real abi args rs pureArgs prepared',
                   'def last := ((Proofs.CppNestedCall.resolveAll state abi args).getD (state,[])).1',
                   'def callee : NState := (prepare state abi args).getD state',
                   'theorem prepared : prepare state abi args = some callee := by decide +kernel',
                   'def calleeParams := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 rs',
                   'theorem calleeReal : Realizes calleeParams (snapshot callee) logical callee := by',
                   '  obtain ⟨h,m,last,erased,resolved,lastFamily,calleeFamily,real,rest⟩ := Proofs.DynamicCallPrepare.sound params st0 state callee realizes abi args rs pureArgs prepared',
                   '  exact real',
                   '#guard last.frame.bindings.length == state.frame.bindings.length+3',
                   '#guard last.scalars.memory == state.scalars.memory',
                   '#guard last.slots == state.slots',
                   '#guard last.frame.state == state.frame.state',
                   '#guard last.work ≤ state.work+Proofs.DynamicArguments.totalWork abi args',
                   '#guard Proofs.DynamicArguments.totalWork abi args == 2*combined.nodes+2*difference.nodes+4',
                   '#guard callee.slots == [.vector 0,.scalar 0,.vector 1,.scalar 1,.vector 2,.scalar 2]',
                   '#guard callee.scalars.memory.length == 9',
                   '#guard callee.scalars.bindings == [⟨7,true⟩,⟨0,true⟩,⟨8,true⟩]',
                   '#guard calleeParams.map (·.owner) == [0,0,2]',
                   '#guard calleeParams.map (·.writable) == [true,false,false]',
                   'def bodyE : NExpr := .binary i32 .add (.binary i32 .add (.variable i32 1) (.variable i32 5)) (.read i32 (.row (.local 2) atom (.literal i32 1)) (.literal i32 1))',
                   'example := Proofs.DynamicExprAuto.sound calleeParams (snapshot callee) logical bodyE (-2) (by decide +kernel) callee calleeReal',
                   'example := Proofs.DynamicResolve.all_sound params st0 heap (resources state.frame) state family realizes [] [] [] rfl',
                   'def reorderedAbi : List Proofs.CppVectorBindings.Parameter := [.nested i32 false,.nested i32 true]',
                   'def reorderedArgs : List NArgument := [.vectorReference 1,.vectorReference 0]',
                   'def reorderedRs : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 false,.nestedRoot 0 0 i32 true]',
                   'example := Proofs.DynamicResolve.all_sound params st0 heap (resources state.frame) state family realizes reorderedAbi reorderedArgs reorderedRs (by decide +kernel)',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.nested i32 true] [.vectorReference 1]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.vector i32 false] [.vectorReference 0]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 true true] [.scalarReference 99]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 abi (args.drop 1)).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 abi (args ++ [.value (.literal i32 0)])).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 false true,.nested i32 false] [.value rowRead,.vectorReference 5]).isNone',
                   '#guard (Proofs.CppNestedCall.resolveAll state [.scalar i32 false true,.nested i32 false] [.value rowRead,.vectorReference 5]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 false true,.scalar i32 false true] [.value (.literal i32 4),.value (.variable i32 5)]).isNone',
                   '#guard (Proofs.CppNestedCall.resolveAll state [.scalar i32 false true,.scalar i32 false true] [.value (.literal i32 4),.value (.variable i32 5)]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar i32 false true] [.value (.binary i32 .add (.literal i32 2147483647) combined)]).isNone',
                   '#guard (Proofs.DynamicArguments.resolveAll params st0 [.scalar ⟨64,false,false⟩ false true] [.value combined]).isNone']
        source_text='''#include <vector>
namespace cp {int mixed(std::vector<std::vector<int>>& g,int x,const std::vector<std::vector<int>>& a,int& ref,const std::vector<int>& other,int y){ref=x+y+a[1][1];g[1].emplace_back(ref);return other[0]+g[1].size();}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-resolve-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'ResolveSource')
            checks[0]='import Proofs.DynamicCallPrepare\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicCallPrepare\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['#guard ResolveSource.mixed.parameters == abi',
                       'def call := ResolveSource.mixed.callFuel 300 state args',
                       '#guard (match call with | .finished (s,.scalar x) => x == 80 && s.scalars.memory == [⟨i32,-2⟩,⟨i32,1⟩] && s.scalars.bindings == state.scalars.bindings && s.slots == state.slots && s.scope == state.scope && s.frame.bindings == state.frame.bindings && s.frame.state.wellFormed && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-2)] && (s.frame.state.storage.lookup 4).map (·.capacity) == some 4 && s.frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2 | _ => false)']
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
