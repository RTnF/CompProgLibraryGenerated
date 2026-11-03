"""Dynamic frame proofs and native checks for mixed outer/inner vector growth."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_append_row import initial
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
HEADER = '''import Proofs.CppRowsSteps
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.CppRowsFrame Proofs.CppRowsSteps
 def i32 : Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def row : Element := .vector atom
'''


class RowsStepsTests(unittest.TestCase):
    def test_statement_chain_resources_and_generated_calls(self):
        checks = [HEADER, f'def base := {initial(1,1)}',
                  'def parent := (base.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩',
                  'theorem data : Data base.state 0 i32 0 [1] 0 [[10,0]] := by',
                  '  refine ⟨⟨by decide +kernel,by decide +kernel,parent,by decide +kernel,by decide +kernel,by decide +kernel⟩,rfl,?_⟩',
                  '  intro k owner lookup',
                  '  have bound := (List.getElem?_eq_some_iff.mp lookup).1',
                  '  have zero : k = 0 := by simp at bound; omega',
                  '  subst k; simp at lookup; subst owner',
                  '  exact ⟨(base.state.storage.lookup 1).getD ⟨0,[],0,64,0⟩,by decide +kernel,by decide +kernel⟩',
                  'theorem fw : FWR base 0 0 i32 0 [1] 0 [[10,0]] true true (resources base) :=',
                  '  ⟨data,by decide +kernel,by decide +kernel,by decide +kernel,(fun h => h),measured_resources base⟩',
                  'def start : NState := {scalars := ⟨[],[],0,0,0⟩,frame := base,slots := [.vector 0],scope := 2,peak := 0}',
                  'def outer := ((NStmt.appendRow (.local 0) i32).run start |>.getD ⟨start,none,false⟩).state',
                  'def fresh := (outer.frame.state.storage.lookup 4).getD ⟨0,[],0,64,0⟩',
                  'def inner := ((NStmt.append (.row (.local 0) atom (.literal i32 1)) i32 (.literal i32 17)).run outer |>.getD ⟨outer,none,false⟩).state',
                  'example : ∃ r0 r1, FWR inner.frame 0 0 i32 0 [1,4] r0.buffer.epoch [[10,0],[17]] true true (afterRow (afterRoot (resources base) parent r0) fresh r1) := by',
                  '  obtain ⟨r0,t0,run0,post0,_⟩ := appendRoot_stmt start 0 0 0 i32 0 [1] 0 [[10,0]] (resources base) fw (by decide +kernel) parent (by decide +kernel) (by decide +kernel)',
                  '  have eq0 : outer = t0 := by simp [outer,run0]',
                  '  subst t0',
                  '  change FWR outer.frame 0 0 i32 0 [1,4] r0.buffer.epoch [[10,0],[]] true true (afterRoot (resources base) parent r0) at post0',
                  '  obtain ⟨r1,t1,run1,post1,_⟩ := appendChild_stmt outer 0 0 0 i32 0 [1,4] r0.buffer.epoch [[10,0],[]] (afterRoot (resources base) parent r0) post0 (by decide +kernel) (.literal i32 1) (.literal i32 17) 1 4 17 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) fresh (by decide +kernel) (by decide +kernel) (by decide +kernel)',
                  '  have eq1 : inner = t1 := by simp [inner,atom,run1]',
                  '  subst t1', '  exact ⟨r0,r1,post1⟩',
                  '#guard inner.frame.state.wellFormed',
                  '#guard inner.frame.bindings == start.frame.bindings',
                  '#guard inner.frame.state.storage.objects.length == 5',
                  '#guard (inner.frame.state.storage.lookup 4 |>.map (·.items)) == some [.integer 17]',
                  '#guard inner.frame.state.liveSpace - inner.frame.state.storage.baseSpace ≤ inner.frame.state.storage.peak']
        source_text = '''#include <vector>
namespace cp {int grow(std::vector<std::vector<int>>& g, int x){
  int k = g.size(); g.emplace_back(); g[k].emplace_back(x); g[0].emplace_back(x); return 0;
}}
'''
        native = ['#include "experiments/library/cpp/template/small_template.hpp"',
                  '#include "source.hpp"', '#include <iostream>', '#include <cassert>',
                  'int main(){std::vector<std::vector<int>> g(1);g[0]={10,0};g.reserve(1);',
                  'std::vector<int> other{77};']
        with tempfile.TemporaryDirectory(prefix='rows-steps-') as directory:
            scratch = Path(directory)
            fixture = scratch/'source.hpp'
            fixture.write_text(source_text)
            checks[0] = emit_lean(lower_source(fixture), 'GrowingRows')+HEADER.replace('import Proofs.CppRowsSteps\n','')
            # Extra imports must precede the generated namespace.
            checks[0] = 'import Proofs.CppRowsSteps\n'+checks[0]
            checks += ['def ast0 := start']
            expected = []
            root_capacity, first_capacity = 1, 2
            rows = [[10, 0]]
            for step in range(12):
                x = step-5
                if len(rows) == root_capacity:
                    root_capacity *= 2
                if len(rows[0]) == first_capacity:
                    first_capacity *= 2
                rows.append([x])
                rows[0].append(x)
                previous, name = f'ast{step}', f'ast{step+1}'
                checks += [f'def call{step} := GrowingRows.grow.callFuel 200 {previous} [.vectorReference 0,.value (.literal i32 ({x}))]',
                           f'#guard (match call{step} with | .finished (_,_) => true | _ => false)',
                           f'def {name} := (match call{step} with | .finished (s,_) => s | _ => {previous})',
                           f'#guard {name}.frame.state.wellFormed',
                           f'#guard {name}.frame.bindings == start.frame.bindings',
                           f'#guard {name}.frame.state.storage.objects.length == {5+step}',
                           f'#guard ({name}.frame.state.storage.lookup 0 |>.map (·.capacity)) == some {root_capacity}',
                           f'#guard ({name}.frame.state.storage.lookup 1 |>.map (·.capacity)) == some {first_capacity}',
                           f'#guard ({name}.frame.state.storage.lookup 2 |>.map (·.items)) == some [.integer 77]',
                           f'#guard {name}.frame.state.storage.lookup 3 == none',
                           f'#guard {name}.frame.state.liveSpace - {name}.frame.state.storage.baseSpace ≤ {name}.frame.state.storage.peak']
                record = [len(rows),root_capacity,first_capacity]
                for j, values in enumerate(rows):
                    owner = 1 if j == 0 else j+3
                    literal = '['+','.join(f'.integer ({v})' for v in values)+']'
                    checks += [f'#guard ({name}.frame.state.storage.lookup {owner} |>.map (·.items)) == some {literal}']
                    record += [len(values), *values]
                expected.append(record)
                native += [f'assert(cp::grow(g,{x})==0);assert(other[0]==77);',
                           'std::cout<<g.size()<<" "<<g.capacity()<<" "<<g[0].capacity();',
                           'for(const auto& v:g){std::cout<<" "<<v.size();for(int x:v)std::cout<<" "<<x;}std::cout<<"\\n";']
            native.append('}')
            proof = scratch/'checks.lean'
            proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            source, exe = scratch/'native.cpp', scratch/'native'
            source.write_text('\n'.join(native))
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer',
                            '-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env = os.environ.copy()
            env['ASAN_OPTIONS'] = 'detect_leaks=0'
            result = subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual([list(map(int,line.split())) for line in result.stdout.splitlines()],expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
