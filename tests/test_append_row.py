"""Empty row insertion, fresh ownership, header invalidation and nested space."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'verifier'))
from nested_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = '''import Proofs.CppNestedCall
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppAppendRow
def i32 : Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
'''


def initial(n, cap, limit=64):
    children = ','.join(map(str, range(1, n+1)))
    tags = [f'some ⟨row,none,some 0,[{children}]⟩']
    tags += ['some ⟨atom,some 0,none,[]⟩'] * n
    tags += ['some ⟨atom,none,some 1,[]⟩', 'none']
    buffers = [f'some ⟨0,[{",".join(f".child {i}" for i in range(1,n+1))}],{cap},{limit},0⟩']
    buffers += [f'some ⟨{i+1},[.integer {10+i},.integer ({-i})],2,64,0⟩' for i in range(n)]
    buffers += [f'some ⟨{n+1},[.integer 77],1,64,0⟩', 'none']
    flags = ['true'] + ['false'] * n + ['true', 'false']
    bindings = ['⟨0,row,true,.root 0⟩', '⟨0,row,false,.root 0⟩', f'⟨{n+1},atom,false,.root 1⟩']
    return (f'(⟨⟨⟨[{",".join(tags)}]⟩,⟨[{",".join(buffers)}],0,0,{cap+2*n+3}⟩⟩,'
            f'[{",".join(flags)}],[{",".join(bindings)}]⟩ : Frame)')


class AppendRowTests(unittest.TestCase):
    def test_fresh_rows_native_lifetimes_costs_and_destruction(self):
        checks = [HEADER]
        native = ['#include "experiments/library/cpp/template/small_template.hpp"',
                  '#include <vector>', '#include <iostream>', '#include <cassert>', 'int main(){']
        expected = []
        for case, (n, spare) in enumerate((n,s) for n in [0,1,3,5] for s in [0,3]):
            cap, epoch, work, peak = n+spare, 0, 0, 0
            base = cap + 2*n + 3
            name = f'f{case}_0'
            checks += [f'def start{case} := {initial(n,cap)}',
                       f'#guard start{case}.state.wellFormed']
            if n:
                checks.append(f'def {name} := (start{case}.bindChild 0 atom 0 true).map Prod.fst |>.getD start{case}')
            else:
                checks.append(f'def {name} := start{case}')
            native += [f'{{std::vector<std::vector<int>> g({n});g.reserve({cap});',
                       f'for(int i=0;i<{n};++i){{g[i]={{10+i,-i}};}}std::vector<int> other{{77}};',
                       'int* captured=g.empty()?nullptr:&g[0][0];']
            owners = list(range(1,n+1))
            for step in range(8):
                old = name
                fresh = n+3+step
                size = n+step
                full = size == cap
                newcap = max(1,2*size) if full else cap
                localpeak = cap+newcap+2 if full else cap+2
                work += size+4 if full else 3
                peak = max(peak, cap+2*n+3+localpeak-(cap+1)-base, 0)
                epoch += int(full)
                owners.append(fresh)
                name = f'f{case}_{step+1}'
                children = ','.join(map(str,owners))
                checks += [f'#guard ({old}.appendRow 0 i32).isSome',
                           f'def {name} := ({old}.appendRow 0 i32).getD {old}',
                           f'#guard {name}.state.wellFormed',
                           f'#guard {name}.state.storage.objects.length == {fresh+1}',
                           f'#guard {name}.state.forest.lookup 0 == some ⟨row,none,some 0,[{children}]⟩',
                           f'#guard {name}.state.forest.lookup {fresh} == some ⟨atom,some 0,none,[]⟩',
                           f'#guard ({name}.state.storage.lookup 0 |>.map (·.capacity)) == some {newcap}',
                           f'#guard ({name}.state.storage.lookup {fresh} |>.map (·.items)) == some []',
                           f'#guard {name}.state.forest.context {fresh} == some 0',
                           f'#guard {name}.state.storage.lookup {n+2} == none',
                           f'#guard {name}.state.forest.lookup {n+2} == none',
                           f'#guard {name}.state.storage.work == {work}',
                           f'#guard {name}.state.storage.peak == {peak}',
                           f'#guard {name}.state.liveSpace == {newcap+2*n+3}',
                           f'#guard {name}.appendRow 1 i32 == none',
                           f'#guard {name}.appendRow 2 i32 == none',
                           f'#guard {name}.appendRow 99 i32 == none',
                           f'#guard ({name}.state.storage.lookup {n+1} |>.map (·.items)) == some [.integer 77]',
                           f'#guard (({name}.bindChild 0 atom {size} true).bind fun p => '
                           f'p.1.appendGrowing p.2 i32 123 |>.bind fun f => f.state.storage.lookup {fresh} |>.map (·.items)) == some [.integer 123]']
                if n:
                    checks += [f'#guard {name}.read ⟨3,i32,true,⟨1,0,0⟩⟩ == some 10',
                               f'#guard ({name}.resolve 3 atom |>.isSome) == {str(epoch==0).lower()}']
                native += ['g.emplace_back();assert(other[0]==77);',
                           'if(captured)assert(captured==&g[0][0] && *captured==10);',
                           'std::cout<<g.size()<<" "<<g.capacity();',
                           'for(const auto& v:g){std::cout<<" "<<v.size();for(int x:v)std::cout<<" "<<x;}std::cout<<"\\n";']
                record = [size+1,newcap]
                for i in range(n):
                    record += [2,10+i,-i]
                record += [0]*(step+1)
                expected.append(record)
                cap = newcap
            checks += [f'def retired{case} := ({name}.state.transfer 0 row 0 2).bind (·.retireScope 2)',
                       f'#guard (retired{case}.map (·.wellFormed)) == some true',
                       f'#guard (retired{case}.bind (·.storage.lookup {n+1}) |>.map (·.items)) == some [.integer 77]',
                       f'#guard (retired{case}.bind (·.storage.lookup {owners[-1]})) == none']
            native.append('}')
        native.append('}')
        checks += [f'def capped := {initial(3,3,4)}',
                   'def capped1 := (capped.appendRow 0 i32).getD capped',
                   '#guard capped1.state.wellFormed',
                   '#guard (capped1.state.storage.lookup 0 |>.map (·.capacity)) == some 4',
                   '#guard capped1.appendRow 0 i32 == none',
                   '#guard ({capped with rootWritable := []} : Frame).appendRow 0 i32 == none',
                   '#guard capped.state.appendRow 999 i32 == none',
                   '#guard capped.state.appendRow 4 i32 == none']
        with tempfile.TemporaryDirectory(prefix='append-row-') as directory:
            scratch = Path(directory)
            fixture = scratch/'source.hpp'
            fixture.write_text('#include <vector>\nnamespace cp {int add_row(std::vector<std::vector<int>>& g){g.emplace_back();return 0;}}\n')
            generated = emit_lean(lower_source(fixture), 'RowSource')
            checks[0] = generated + HEADER.replace('import Proofs.CppNestedCall\n','')
            checks += [
                f'def caller : Proofs.CppNestedProgram.NState := {{scalars := ⟨[],[],0,0,0⟩,frame := {initial(1,1)},slots := [.vector 0],scope := 1,peak := 0}}',
                'def astCall := RowSource.add_row.callFuel 40 caller [.vectorReference 0]',
                '#guard (match astCall with | .finished (s,_) => (s.frame.state.storage.lookup 0).map (·.items) | _ => none) == some [.child 1,.child 4]',
                '#guard (match astCall with | .finished (s,_) => s.frame.state.wellFormed | _ => false)',
                '#guard (match astCall with | .finished (s,_) => (s.frame.state.storage.lookup 4).map (·.items) | _ => none) == some []',
            ]
            for insertion in ['g.emplace_back(3,7);','g.emplace_back(g[0]);']:
                refused = scratch/'refused.hpp'
                refused.write_text(fixture.read_text().replace('g.emplace_back();',insertion))
                with self.assertRaises(ValueError):
                    lower_source(refused)
            native.insert(1,'#include "source.hpp"')
            native.insert(-1,'{std::vector<std::vector<int>> g(1);assert(cp::add_row(g)==0);assert(g.size()==2 && g[1].empty());}')
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
            result = subprocess.run([str(exe)],env=env,check=True,capture_output=True,text=True)
            self.assertEqual([list(map(int,line.split())) for line in result.stdout.splitlines()],expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
