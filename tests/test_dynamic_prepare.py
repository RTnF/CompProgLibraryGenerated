"""Build callee families from canonical binding with aliases and scalar refs."""
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


class DynamicPrepareTests(unittest.TestCase):
    def test_mixed_prepare_and_native_call(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicPrepare\n'+checks[0]
        checks += ['open Proofs.CppNestedCall Proofs.DynamicFamilyInit',
                   'def abi : List Proofs.CppVectorBindings.Parameter := [.nested i32 true,.scalar i32 false true,.nested i32 false,.scalar i32 true true,.vector i32 false]',
                   'def args : List NArgument := [.vectorReference 0,.value combined,.vectorReference 1,.scalarReference 3,.vectorReference 2]',
                   'def resolvedValues : List Proofs.CppNestedCall.Resolved := [.nestedRoot 0 0 i32 true,.scalar i32 true 1,.nestedRoot 0 0 i32 false,.scalarAddress i32 0 true,.vector 2 1 i32 false]',
                   'def last : NState := ((resolveAll state abi args).getD (state,[])).1',
                   'theorem resolvedRun : resolveAll state abi args = some (last,resolvedValues) := by decide +kernel',
                   'def callee : NState := (prepare state abi args).getD state',
                   'theorem prepared : prepare state abi args = some callee := by decide +kernel',
                   'theorem lastFamily : Family params heap last.frame (resources state.frame) := by',
                   '  apply family.transport last.frame (by decide +kernel) (by decide +kernel)',
                   '  intro p member; simp [params] at member; rcases member with rfl|rfl|rfl <;> decide +kernel',
                   'theorem compatible : ∀ r ∈ resolvedValues, Compatible heap r := by',
                   '  intro r member; simp [resolvedValues] at member; rcases member with rfl|rfl|rfl|rfl|rfl',
                   '  · exact ⟨view,by decide +kernel,rfl,rfl⟩',
                   '  · exact True.intro',
                   '  · exact ⟨view,by decide +kernel,rfl,rfl⟩',
                   '  · exact True.intro',
                   '  · exact ⟨.flat i32 1 [77],by decide +kernel,rfl,rfl⟩',
                   'def calleeParams := describe last.frame.rootWritable 0 resolvedValues',
                   'theorem calleeFamily : Family calleeParams heap callee.frame (resources state.frame) :=',
                   '  (Proofs.DynamicPrepare.prepared_family state last callee abi args resolvedValues (by decide +kernel) resolvedRun lastFamily compatible prepared).1',
                   'theorem calleeReal : Realizes calleeParams (snapshot callee) logical callee :=',
                   '  (Proofs.DynamicPrepare.prepared_family state last callee abi args resolvedValues (by decide +kernel) resolvedRun lastFamily compatible prepared).2.1',
                   '#guard callee.slots == [.vector 0,.scalar 0,.vector 1,.scalar 1,.vector 2]',
                   '#guard callee.scalars.memory.length == 8',
                   '#guard callee.scalars.bindings == [⟨7,true⟩,⟨0,true⟩]',
                   '#guard calleeParams.map (·.slot) == [0,1,2]',
                   '#guard calleeParams.map (·.owner) == [0,0,2]',
                   '#guard calleeParams.map (·.writable) == [true,false,false]',
                   '#guard calleeParams.all (·.maximum)',
                   '#guard callee.frame.rootWritable == state.frame.rootWritable',
                   '#guard callee.scope == state.scope+1',
                   '#guard last.frame.bindings.length == state.frame.bindings.length+1',
                   '#guard (Proofs.DynamicPrepare.initial state last abi).frame.bindings.isEmpty',
                   'def e : NExpr := .binary i32 .add (.variable i32 1) (.read i32 (.row (.local 2) atom (.literal i32 1)) (.literal i32 1))',
                   'example := Proofs.DynamicExprAuto.sound calleeParams (snapshot callee) logical e (-2) (by decide +kernel) callee calleeReal',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot callee,logical⟩',
                   'def st1 : Proofs.DynamicStmt.State := ⟨Proofs.DynamicStmt.assigned st0.locals ⟨0,true⟩ ⟨i32,1⟩ (-2),logical⟩',
                   'def assign : NStmt := .assign 3 i32 e',
                   'theorem assignPure : Proofs.DynamicStmt.run calleeParams assign st0 = some ⟨st1,none⟩ := by',
                   '  have value : Proofs.DynamicExpr.denote calleeParams st0.locals st0.contents e = some (-2) := by decide +kernel',
                   '  have cell : Proofs.DynamicStmt.scalarCell st0.locals 3 i32 = some (⟨0,true⟩,⟨i32,1⟩) := by decide +kernel',
                   '  have converted : i32.convert (-2) = some (-2) := by decide +kernel',
                   '  simp only [assign,Proofs.DynamicStmt.run,value,Bind.bind,Option.bind,cell,converted,ite_true]; rfl',
                   'example := Proofs.DynamicAppendAuto.sound calleeParams st0 callee calleeReal assign _ assignPure True.intro',
                   '#guard ((assign.run callee).getD ⟨callee,none,false⟩).state.scalars.memory[0]? == some ⟨i32,-2⟩',
                   '#guard ((assign.run callee).getD ⟨callee,none,false⟩).state.scalars.memory[7]? == some ⟨i32,1⟩',
                   'def reverseAbi : List Proofs.CppVectorBindings.Parameter := [.nested i32 false,.nested i32 true]',
                   'def reverseArgs : List NArgument := [.vectorReference 1,.vectorReference 0]',
                   'def reverse := (prepare state reverseAbi reverseArgs).getD state',
                   '#guard reverse.frame.bindings.map (·.writable) == [false,true]',
                   '#guard reverse.frame.rootWritable == state.frame.rootWritable',
                   '#guard (prepare state [.nested i32 true] [.vectorReference 1]).isNone',
                   '#guard (prepare state [.vector i32 false] [.vectorReference 0]).isNone',
                   '#guard (prepare state [.scalar i32 true true] [.scalarReference 99]).isNone',
                   '#guard (prepare state abi (args.drop 1)).isNone',
                   '#guard (prepare state abi (args ++ [.value (.literal i32 0)])).isNone',
                   'def constScalar : NState := {state with scalars := {state.scalars with bindings := [⟨0,false⟩,⟨1,true⟩]}}',
                   '#guard (prepare constScalar [.scalar i32 true true] [.scalarReference 3]).isNone',
                   '#guard (bindAll (Proofs.DynamicPrepare.initial state last abi) [.scalar i32 true 2147483648]).isNone',
                   '#guard (bindAll (Proofs.DynamicPrepare.initial state last abi) [.scalarAddress i32 999 true]).isNone',
                   'example : ¬ Compatible heap (.nestedRoot 0 99 i32 false) := by',
                   '  intro ⟨v,lookup,_,scope⟩',
                   '  have found : heap 0 = some view := by decide +kernel',
                   '  have same : v = view := Option.some.inj (lookup.symm.trans found)',
                   '  subst v; change (0 : Nat) = 99 at scope; omega']
        source_text='''#include <vector>
namespace cp {int mixed(std::vector<std::vector<int>>& g,int x,const std::vector<std::vector<int>>& a,int& ref,const std::vector<int>& other){ref=x+a[1][1];g[1].emplace_back(ref);return other[0]+g[1].size();}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-prepare-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'PrepareSource')
            checks[0]='import Proofs.DynamicPrepare\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicPrepare\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['#guard PrepareSource.mixed.parameters == abi',
                       'def call := PrepareSource.mixed.callFuel 300 state args',
                       '#guard (match call with | .finished (s,.scalar x) => x == 80 && s.scalars.memory == [⟨i32,-2⟩,⟨i32,1⟩] && s.scalars.bindings == state.scalars.bindings && s.slots == state.slots && s.scope == state.scope && s.frame.bindings == state.frame.bindings && s.frame.state.wellFormed && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-2)] && (s.frame.state.storage.lookup 4).map (·.capacity) == some 4 && s.frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2 | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};int k=1,j=1;int result=cp::mixed(g,(int)g.size()+g[k][j],g,k,other);std::cout<<result<<" "<<k<<" "<<g[1].capacity()<<" "<<g[1].back()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['80 -2 4 -2'])


if __name__ == '__main__':
    disable_network(); unittest.main()
