"""Successful pure append supplies all logical premises; limits stay explicit."""
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


class DynamicAppendAutoTests(unittest.TestCase):
    def test_success_based_primitives(self):
        checks=fixture_checks(); checks[0]='import Proofs.DynamicAppendAuto\n'+checks[0]
        checks += ['open Proofs.DynamicAppendAuto',
                   'def nested : NExpr := .read i32 (.row (.local 1) atom combined) combined',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def values1 := values.set 1 ([17,-3] ++ [-3])',
                   'def st1 : Proofs.DynamicStmt.State := ⟨snapshot state,putContents logical 0 (.rows i32 0 values1)⟩',
                   'def stmt : NStmt := .append (.row (.local 0) atom combined) i32 nested',
                   'theorem pure1 : Proofs.DynamicStmt.run params stmt st0 = some ⟨st1,none⟩ := by rfl',
                   'theorem avail (s : NState) (room : Proofs.DynamicAppendValue.RoomAt s 0 1) : Available params st0 s stmt := by',
                   '  intro p k selected index',
                   '  have chosen : Proofs.DynamicStmt.mutableRoot params st0 0 (.vector atom) = some p0 := by decide +kernel',
                   '  have same : p = p0 := Option.some.inj (selected.symm.trans chosen)',
                   '  subst p',
                   '  have iv : Proofs.DynamicExpr.denote params st0.locals st0.contents combined = some (1 : Int) := by decide +kernel',
                   '  have equal := Option.some.inj (index.symm.trans iv)',
                   '  have pos : k = 1 := by omega',
                   '  subst k; exact room',
                   'theorem room : Proofs.DynamicAppendValue.RoomAt state 0 1 := ⟨(state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,4,(state.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
                   'example (s : NState) (real : Realizes params st0.locals st0.contents s) (room : Proofs.DynamicAppendValue.RoomAt s 0 1) := child_sound params st0 s real 0 i32 i32 combined nested _ pure1 (avail s room)',
                   'example := runs params st0 state realizes stmt _ pure1 (avail state room)',
                   'def outer : NStmt := .appendRow (.local 0) i32',
                   'def stRoot : Proofs.DynamicStmt.State := ⟨snapshot state,putContents logical 0 (.rows i32 0 (values ++ [[]]))⟩',
                   'theorem rootPure : Proofs.DynamicStmt.run params outer st0 = some ⟨stRoot,none⟩ := by rfl',
                   'theorem rootAvail : Available params st0 state outer := by',
                   '  intro p selected',
                   '  have chosen : Proofs.DynamicStmt.mutableRoot params st0 0 (.vector atom) = some p0 := by decide +kernel',
                   '  have same : p = p0 := Option.some.inj (selected.symm.trans chosen)',
                   '  subst p',
                   '  exact ⟨(state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                   'example := root_sound params st0 state realizes 0 i32 _ rootPure rootAvail',
                   'example := runs params st0 state realizes outer _ rootPure rootAvail',
                   'def scalar : NStmt := .ret (.binary i32 .add nested (.read i32 (.local 2) (.literal i32 0)))',
                   'theorem scalarPure : Proofs.DynamicStmt.run params scalar st0 = some ⟨st0,some 74⟩ := by rfl',
                   'example := sound params st0 state realizes scalar _ scalarPure True.intro',
                   'example := sound params st0 state realizes .skip (⟨st0,none⟩ : Proofs.DynamicStmt.Step) rfl True.intro',
                   'theorem all_primitives (params : List Parameter) (st : Proofs.DynamicStmt.State) (s : NState) (real : Realizes params st.locals st.contents s) (stmt : NStmt) (result : Proofs.DynamicStmt.Step) (pure : Proofs.DynamicStmt.run params stmt st = some result) (available : Available params st s stmt) : ∃ actual, stmt.run s = some actual ∧ Proofs.DynamicScalarSound.Matches params result actual := sound params st s real stmt result pure available',
                   'def first := ((stmt.run state).getD ⟨state,none,false⟩).state',
                   '#guard (first.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3)]',
                   '#guard (first.frame.state.storage.lookup 4).map (·.capacity) == some 4',
                   '#guard first.frame.bindings == state.frame.bindings',
                   '#guard first.frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2',
                   'def rootResult := ((outer.run state).getD ⟨state,none,false⟩).state',
                   '#guard (rootResult.frame.state.storage.lookup 0).map (fun b => b.items.length) == some 5',
                   '#guard rootResult.frame.bindings == state.frame.bindings',
                   'def tightParent : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value := {(state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩ with limit := 4}',
                   'def tight : NState := {state with frame := {state.frame with state := {state.frame.state with storage := {state.frame.state.storage with objects := state.frame.state.storage.objects.set 0 (some tightParent)}}}}',
                   '#guard tight.frame.state.wellFormed',
                   '#guard (outer.run tight).isNone',
                   'theorem tightNoRoom : ¬ RootRoom tight 0 := by',
                   '  intro ⟨old,found,room⟩',
                   '  have lookup : tight.frame.state.storage.lookup 0 = some tightParent := by decide +kernel',
                   '  have same : old = tightParent := Option.some.inj (found.symm.trans lookup)',
                   '  subst old',
                   '  have length : tightParent.items.length = 4 := by decide +kernel',
                   '  have limit : tightParent.limit = 4 := rfl',
                   '  rw [length,limit] at room; omega',
                   'example : ¬ Available params st0 tight outer := by',
                   '  intro available; exact tightNoRoom (available p0 (by decide +kernel))',
                   '#guard (Proofs.DynamicStmt.run params outer st0).isSome',
                   'def refused : List NStmt := [.appendRow (.local 1) i32,.append (.row (.local 1) atom combined) i32 nested,.append (.row (.local 0) (.integer ⟨64,false,false⟩) combined) i32 nested,.append (.row (.local 0) atom nested) i32 combined]',
                   '#guard refused.all (fun stmt => (Proofs.DynamicStmt.run params stmt st0).isNone && (stmt.run state).isNone)',
                   '#guard (Proofs.DynamicStmt.run params (.constructRows i32 true (.literal i32 2)) st0).isNone']
        source_text='''#include <vector>
namespace cp {
int mutate(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& a,const std::vector<int>& other,int k,int j){g[(int)a.size()+a[k][j]].emplace_back(a[(int)a.size()+a[k][j]][(int)a.size()+a[k][j]]);return g[1].size()+other[0];}
int add(std::vector<std::vector<int>>& g){g.emplace_back();return g.size();}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-append-auto-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'AppendAutoSource')
            checks[0]='import Proofs.DynamicAppendAuto\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicAppendAuto\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['def mutateCall := AppendAutoSource.mutate.callFuel 400 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                       '#guard (match mutateCall with | .finished (s,.scalar x) => x == 80 && s.frame.bindings == base.bindings && s.frame.state.wellFormed && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3)] | _ => false)',
                       'def addCall := AppendAutoSource.add.callFuel 100 state [.vectorReference 0]',
                       '#guard (match addCall with | .finished (s,.scalar x) => x == 5 && s.frame.bindings == base.bindings && s.frame.state.wellFormed | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};std::cout<<cp::mutate(g,g,other,1,1)<<" "<<g[1].capacity()<<std::endl;std::cout<<cp::add(g)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['80 4','5'])


if __name__ == '__main__':
    disable_network(); unittest.main()
