"""All successful pure commands preserve heap signatures and scalar types."""
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
namespace cp {int sweep(std::vector<std::vector<int>>&g,int&x,int n){
int t=0;while(t<n){{int z=t+1;x=x+z;}if(t==1)g.emplace_back();else g[0].emplace_back(x);t++;if(t==3)break;}return x;}}
'''

class DynamicPreserveTests(unittest.TestCase):
    def test_control_preservation_and_native_source(self):
        checks=fixture_checks()
        checks += ['open Proofs.DynamicPreserve Proofs.DynamicFinish Proofs.DynamicControl',
          'example (ps : List Parameter) (fuel : Nat) (c : Command) (st : Proofs.DynamicStmt.State) (out : Proofs.DynamicControl.Step) (ran : Proofs.DynamicControl.runFuel ps fuel c st = .finished out) : Preserved st out.state := Proofs.DynamicControlPreserve.run ps fuel c st out ran',
          'example (a b : Locals) (types : TypesPrefix a b) : a.memory.length ≤ b.memory.length ∧ (b.memory.take a.memory.length).map Proofs.CppState.Cell.type = a.memory.map Proofs.CppState.Cell.type := types.fields',
          'def st0 : Proofs.DynamicStmt.State := ⟨snapshot state,logical⟩',
          'def changed : Proofs.DynamicStmt.State := ⟨{st0.locals with memory := [⟨i32,9⟩,⟨i32,8⟩]},logical⟩',
          'example : TypesPrefix st0.locals changed.locals := ⟨[],by decide +kernel⟩',
          'example := leave_exists st0 changed (⟨[],by decide +kernel⟩ : TypesPrefix st0.locals changed.locals)',
          'def wrong : Locals := {st0.locals with memory := [⟨⟨64,false,false⟩,1⟩,⟨i32,1⟩]}',
          'example : ¬ TypesPrefix st0.locals wrong := by',
          '  intro types; have bad := types.fields.2; have unequal : (wrong.memory.take st0.locals.memory.length).map Proofs.CppState.Cell.type ≠ st0.locals.memory.map Proofs.CppState.Cell.type := by decide +kernel',
          '  exact unequal bad',
          'def short : Locals := {st0.locals with memory := [⟨i32,1⟩]}',
          'example : ¬ TypesPrefix st0.locals short := by',
          '  intro types; have bad := types.fields.1; have length : short.memory.length < st0.locals.memory.length := by decide +kernel',
          '  omega',
          'example (a b c : Proofs.DynamicStmt.State) (first : Preserved a b) (second : Preserved b c) : Preserved a c := first.trans second',
          'example : Proofs.DynamicControl.runFuel params 0 (.primitive .skip) st0 = .exhausted := rfl',
          'def unsupported : NStmt := .constructRows i32 true (.literal i32 0)',
          '#guard (Proofs.DynamicStmt.run params unsupported st0).isNone',
          'example : Proofs.DynamicControl.runFuel params 10 (.primitive unsupported) st0 = .fault := rfl']
        native=['#include "experiments/library/cpp/template/small_template.hpp"','#include "source.hpp"','#include <iostream>','int main(){']
        expected=[]
        with tempfile.TemporaryDirectory(prefix='dynamic-preserve-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'PreserveSource')
            checks[0]='import Proofs.DynamicCallAuto\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            for case,n in enumerate([0,1,2,3,5]):
                want=[1,2,4,7,7][case]
                rows=4+(n>=2); length=2+(n>=1)+(n>=3)
                checks += [f'def initial{case} := (Proofs.CppNestedCall.prepare state PreserveSource.sweep.parameters [.vectorReference 0,.scalarReference 3,.value (.literal i32 {n})]).getD state',
                  f'def ps{case} := Proofs.DynamicFamilyInit.describe state.frame.rootWritable 0 [.nestedRoot 0 0 i32 true,.scalarAddress i32 0 true,.scalar i32 true {n}]',
                  f'def start{case} : Proofs.DynamicStmt.State := ⟨snapshot initial{case},logical⟩',
                  f'def out{case} : Proofs.DynamicControl.Step := match Proofs.DynamicControl.runFuel ps{case} 300 PreserveSource.sweep.body start{case} with | .finished p => p | _ => ⟨start{case},none,false⟩',
                  f'theorem ran{case} : Proofs.DynamicControl.runFuel ps{case} 300 PreserveSource.sweep.body start{case} = .finished out{case} := by cbv',
                  f'theorem preserved{case} : Preserved start{case} out{case}.state := Proofs.DynamicControlPreserve.run _ _ _ _ _ ran{case}',
                  f'example := finish_exists start{case} out{case}.state preserved{case}.2 (.scalar i32) out{case}.returned (.scalar {want}) (by decide +kernel)',
                  f'#guard out{case}.returned == some {want}',
                  f'#guard (out{case}.state.locals.memory[0]?).map (·.value) == some {want}',
                  f'#guard (match out{case}.state.contents 0 with | some (.rows _ _ vs) => vs.length == {rows} && (vs[0]?.map List.length) == some {length} | _ => false)',
                  f'example : (out{case}.state.contents 2).map shape = (logical 2).map shape := preserved{case}.1 2',
                  f'example := leave_exists start{case} out{case}.state preserved{case}.2']
                native += [f'{{std::vector<std::vector<int>>g{{{{10,0}},{{17,-3}},{{}},{{}}}};int x=1;int r=cp::sweep(g,x,{n});std::cout<<r<<" "<<x<<" "<<g.size()<<" "<<g[0].size()<<std::endl;}}']
                expected.append(f'{want} {want} {rows} {length}')
            native.append('}')
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native';source.write_text('\n'.join(native))
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),expected)

if __name__=='__main__':
    disable_network();unittest.main()
