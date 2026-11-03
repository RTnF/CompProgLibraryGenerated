"""General append targets, real buffer witnesses, and amortised composition."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_dynamic_index import index_checks
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT=Path(__file__).resolve().parent.parent


class DynamicAppendIndexTests(unittest.TestCase):
    def test_two_self_reading_appends(self):
        checks=index_checks(); checks[0]='import Proofs.DynamicAppendIndex\n'+checks[0]
        checks += ['open Proofs.DynamicAppendIndex',
                   'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
                   'def values1 := values.set 1 ([17,-3] ++ [-3])',
                   'def contents1 := putContents logical 0 (.rows i32 0 values1)',
                   'def st1 : Proofs.DynamicStmt.State := ⟨snapshot state,contents1⟩',
                   'def values2 := values1.set 1 ([17,-3,-3] ++ [-3])',
                   'def contents2 := putContents contents1 0 (.rows i32 0 values2)',
                   'def st2 : Proofs.DynamicStmt.State := ⟨snapshot state,contents2⟩',
                   'theorem rootReady1 : Ready params st1.locals st1.contents rootSize := known (by decide +kernel) (Proofs.DynamicExprAtoms.root_size params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 values1 (by decide +kernel) (by decide +kernel))',
                   'theorem readReady1 : Ready params st1.locals st1.contents rowRead := known (by decide +kernel) (Proofs.DynamicExprAtoms.row_read params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values1 [17,-3,-3] idx pos (-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
                   'theorem combinedReady1 : Ready params st1.locals st1.contents combined := Ready.binary _ _ _ _ (Ready.cast _ _ rootReady1) readReady1',
                   'theorem nestedReady1 : Ready params st1.locals st1.contents nestedRead := known (by decide +kernel) (Proofs.DynamicIndexAtoms.row_read params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values1 [17,-3,-3] combined combined (-3) (by decide +kernel) combinedReady1 (by decide +kernel) (by decide +kernel) combinedReady1 (by decide +kernel) (by decide +kernel))',
                   'def appendStmt : NStmt := .append (.row (.local 0) atom combined) i32 nestedRead',
                   'theorem two_appends (s : NState) (r : Realizes params st0.locals st0.contents s) (space : RoomFor s 0 1 2) :',
                   '    ∃ (old1 old2 : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (a b : Proofs.CppVector.Result Proofs.CppNestedVectorStore.Value Unit) (t u : NState),',
                   '      appendStmt.run s = some ⟨t,none,false⟩ ∧ appendStmt.run t = some ⟨u,none,false⟩ ∧',
                   '      Realizes params st2.locals st2.contents u ∧ RowUpdate s t 0 1 (-3) old1 a.buffer ∧ RowUpdate t u 0 1 (-3) old2 b.buffer ∧',
                   '      RoomFor u 0 1 0 ∧ u.work+Proofs.CppVectorGrowth.potential b.buffer ≤ s.work+4*combined.nodes+4*nestedRead.nodes+16+Proofs.CppVectorGrowth.potential old1 := by',
                   '  obtain ⟨_,old1,a,t,run1,match1,updated1,work1,_⟩ := Proofs.DynamicAppendIndex.appendChild params st0 s r 0 i32 p0 (by decide +kernel) 0 1 values [17,-3] (by decide +kernel) (by decide +kernel) combined nestedRead combinedReady (by decide +kernel) (-3) nestedReady (by decide +kernel) (by decide +kernel) (space.one (by omega))',
                   '  have real1 : Realizes params st1.locals st1.contents t := match1.state',
                   '  have left1 : RoomFor t 0 1 1 := updated1.remaining space',
                   '  obtain ⟨_,old2,b,u,run2,match2,updated2,work2,_⟩ := Proofs.DynamicAppendIndex.appendChild params st1 t real1 0 i32 p0 (by decide +kernel) 0 1 values1 [17,-3,-3] (by decide +kernel) (by decide +kernel) combined nestedRead combinedReady1 (by decide +kernel) (-3) nestedReady1 (by decide +kernel) (by decide +kernel) (left1.one (by omega))',
                   '  have total := updated1.two_work updated2 (2*combined.nodes+2*nestedRead.nodes+8) (2*combined.nodes+2*nestedRead.nodes+8) work1 work2',
                   '  exact ⟨old1,old2,a,b,t,u,run1,run2,match2.state,updated1,updated2,updated2.remaining left1,by omega⟩',
                   'theorem room2 : RoomFor state 0 1 2 := ⟨(state.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩,4,(state.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩',
                   'example := two_appends state realizes room2',
                   'def firstState := ((appendStmt.run state).getD ⟨state,none,false⟩).state',
                   'def secondState := ((appendStmt.run firstState).getD ⟨firstState,none,false⟩).state',
                   '#guard (firstState.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3)]',
                   '#guard (secondState.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3),.integer (-3)]',
                   '#guard (secondState.frame.state.storage.lookup 4).map (·.capacity) == some 4',
                   '#guard (secondState.frame.state.storage.lookup 4).map (·.epoch) == some 3',
                   '#guard secondState.frame.bindings == state.frame.bindings',
                   '#guard secondState.scalars.memory == state.scalars.memory',
                   '#guard secondState.frame.state.storage.lookup 0 == state.frame.state.storage.lookup 0',
                   '#guard secondState.frame.state.storage.lookup 2 == state.frame.state.storage.lookup 2',
                   '#guard secondState.frame.state.wellFormed',
                   '#guard (Proofs.DynamicStmt.run params appendStmt st0).map (fun p => p.state.contents 0) == some (some (.rows i32 0 values1))',
                   '#guard (Proofs.DynamicStmt.run params appendStmt st1).map (fun p => p.state.contents 0) == some (some (.rows i32 0 values2))',
                   'def tightRow : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value := {(state.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩ with limit := 3}',
                   'def tightOther : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value := {(state.frame.state.storage.lookup 2).getD ⟨0,[],0,64,0⟩ with limit := 1}',
                   'def tightState : NState := {state with frame := {state.frame with state := {state.frame.state with storage := {state.frame.state.storage with objects := (state.frame.state.storage.objects.set 4 (some tightRow)).set 2 (some tightOther)}}}}',
                   '#guard tightState.frame.state.wellFormed',
                   '#guard tightOther.items.length == tightOther.limit',
                   'def tightFirst := ((appendStmt.run tightState).getD ⟨tightState,none,false⟩).state',
                   '#guard (appendStmt.run tightState).isSome',
                   '#guard (tightFirst.frame.state.storage.lookup 4).map (·.capacity) == some 3',
                   '#guard (appendStmt.run tightFirst).isNone',
                   'def rejected : List NStmt := [.append (.row (.local 1) atom combined) i32 nestedRead,.append (.row (.local 0) atom nestedRead) i32 combined,.append (.row (.local 0) atom (.binary i32 .add combined (.cast i32 rootSize))) i32 combined,.append (.row (.local 0) atom combined) i32 (.binary i32 .add (.literal i32 2147483647) combined)]',
                   '#guard rejected.all (fun stmt => (Proofs.DynamicStmt.run params stmt st0).isNone && (stmt.run state).isNone)']
        source_text='''#include <vector>
namespace cp {int append2(std::vector<std::vector<int>>& g,const std::vector<std::vector<int>>& a,const std::vector<int>& other,int k,int j){
g[(int)a.size()+a[k][j]].emplace_back(a[(int)a.size()+a[k][j]][(int)a.size()+a[k][j]]);
g[(int)a.size()+a[k][j]].emplace_back(a[(int)a.size()+a[k][j]][(int)a.size()+a[k][j]]);
return g[1].size()+other[0];}}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-append-index-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'AppendIndexSource')
            checks[0]='import Proofs.DynamicAppendIndex\nimport Proofs.DynamicIndexAtoms\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicAppendIndex\n','').replace('import Proofs.DynamicIndexAtoms\n','').replace('import Proofs.DynamicReadSound\n','')
            checks += ['def call := AppendIndexSource.append2.callFuel 500 state [.vectorReference 0,.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                       '#guard (match call with | .finished (s,.scalar x) => x == 81 && s.frame.bindings == base.bindings && s.frame.state.wellFormed && s.scalars.memory == state.scalars.memory && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3),.integer (-3),.integer (-3)] && (s.frame.state.storage.lookup 4).map (·.capacity) == some 4 | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};std::cout<<cp::append2(g,g,other,1,1)<<" "<<g[1].capacity()<<" "<<g[1].back()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['81 4 -3'])


if __name__ == '__main__':
    disable_network(); unittest.main()
