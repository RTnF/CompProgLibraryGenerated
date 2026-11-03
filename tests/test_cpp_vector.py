"""Vector primitive contracts, native correspondence and refusal boundaries."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT/'tools'))
sys.path.insert(0, str(ROOT/'verifier'))
from test_scalar_ir import lean_environment
from offline import disable_network
from check_public import check_compiler, FLAGS
from state_ir import lower_source


def lean_list(values):
    return '['+','.join(f'({value}:Int)' for value in values)+']'


def buffer(values, capacity, epoch=0, owner=7, limit=100):
    return f'(⟨{owner},{lean_list(values)},{capacity},{limit},{epoch}⟩ : Buffer Int)'


class VectorTests(unittest.TestCase):
    def check_lean(self, directory, text):
        proof = directory/'checks.lean'
        proof.write_text('import Proofs.CppVector\nopen Proofs.CppVector Proofs.CppScalar\n'
                         'def accept : Int → Bool := (⟨32,true,false⟩ : Ty).valid\n'+text)
        lake, env = lean_environment()
        result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_contents_capacity_alias_and_cost_contracts(self):
        checks=[]
        native=['#include "experiments/library/cpp/template/small_template.hpp"',
                '#include <cassert>', '#include <vector>', 'int main(){']
        cases=[[],[0],[1,-2],[2147483647,-2147483648,0],[3,3,1,0]]
        for values in cases:
            for spare in [0,1,4]:
                for request in [0,len(values),len(values)+2,len(values)+7]:
                    capacity=len(values)+spare
                    b=buffer(values,capacity)
                    grown=request>capacity
                    new_capacity=max(capacity,request)
                    epoch=int(grown)
                    after=buffer(values,new_capacity,epoch)
                    work=len(values)+1 if grown else 1
                    peak=capacity+request+2 if grown else capacity+1
                    checks.append(f'#guard reserve {b} accept true {request} == '
                                  f'some ⟨{after},(),{work},{peak}⟩\n')
                    native.append('{std::vector<int> v{'+','.join(map(str,values))+'};')
                    native.append(f'v.reserve({capacity}); assert(v.capacity()=={capacity});'
                                  f'v.reserve({request}); assert(v.capacity()=={new_capacity});'
                                  f'assert(v.size()=={len(values)});')
                    for index,value in enumerate(values):
                        checks.append(f'#guard read {after} accept {index} == '
                                      f'some ⟨{after},({value}:Int),1,{new_capacity+2}⟩\n')
                        native.append(f'assert(v[{index}]==({value}));')
                        # Retained refs work without growth; growing reserve invalidates.
                        checks.append(f'#guard readRef {after} accept ⟨7,0,{index}⟩ == '+
                            ('none\n' if grown else
                             f'some ⟨{after},({value}:Int),1,{new_capacity+2}⟩\n'))
                    if len(values)<new_capacity:
                        new_value=values[0] if values else -11
                        appended=buffer(values+[new_value],new_capacity,epoch)
                        checks.append(f'#guard appendReserved {after} accept true ({new_value}:Int) == '
                                      f'some ⟨{appended},(),2,{new_capacity+2}⟩\n')
                        if values:
                            native.append('const int* original=&v[0]; v.emplace_back(v[0]);'
                                          'assert(original==&v[0]); assert(*original==v.back());')
                            checks.append(f'#guard readRef {appended} accept ⟨7,{epoch},0⟩ == '
                                          f'some ⟨{appended},({values[0]}:Int),1,{new_capacity+2}⟩\n')
                        else:
                            native.append('v.emplace_back(-11);')
                        native.append(f'assert(v.back()==({new_value}));'
                                      f'assert(v.capacity()=={new_capacity});')
                    if values:
                        for index in range(len(values)):
                            replacement=17-index
                            changed=list(values);changed[index]=replacement
                            after_write=buffer(changed,new_capacity,epoch)
                            checks.append(f'#guard writeRef {after} accept true ⟨7,{epoch},{index}⟩ '
                                          f'({replacement}:Int) == '
                                          f'some ⟨{after_write},(),1,{new_capacity+2}⟩\n')
                            native.append('{std::vector<int> updated{'+','.join(map(str,values))+'};')
                            native.append(f'updated.reserve({new_capacity}); updated[{index}]={replacement};')
                            for at, expected in enumerate(changed):
                                native.append(f'assert(updated[{at}]==({expected}));')
                            native.append(f'assert(updated.size()=={len(values)}); '
                                          f'assert(updated.capacity()=={new_capacity});'+'}')
                    native.append('}')
        native.append('}')
        with tempfile.TemporaryDirectory(prefix='cpp-vector-') as directory:
            scratch=Path(directory)
            self.check_lean(scratch,''.join(checks))
            source=scratch/'native.cpp';source.write_text('\n'.join(native))
            check_compiler()
            executable=scratch/'native'
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(ROOT),str(source),'-o',str(executable)],cwd=ROOT,check=True)
            subprocess.run([str(executable)],check=True)
        print(f'vector primitive native correspondence: {len(checks)} Lean checks, 60 C++ sequences')

    def test_faults_and_unimplemented_translation_are_refused(self):
        b=buffer([4,8],3)
        checks=[]
        for index in [-1,2,3,2147483647]:
            checks.append(f'#guard elementRef {b} accept ({index}:Int) == none\n')
            checks.append(f'#guard read {b} accept ({index}:Int) == none\n')
        for reference in ['⟨8,0,0⟩','⟨7,1,0⟩','⟨7,0,2⟩']:
            checks.append(f'#guard readRef {b} accept {reference} == none\n')
            checks.append(f'#guard writeRef {b} accept true {reference} 1 == none\n')
        checks.extend([f'#guard reserve {b} accept false 7 == none\n',
                       f'#guard reserve {b} accept true 101 == none\n',
                       f'#guard appendReserved {b} accept false 1 == none\n',
                       f'#guard appendReserved {b} accept true 2147483648 == none\n',
                       f'#guard writeRef {b} accept true ⟨7,0,0⟩ (-2147483649) == none\n',
                       f'#guard writeRef {b} accept false ⟨7,0,0⟩ 1 == none\n',
                       f'#guard appendReserved {buffer([4,8],2)} accept true 1 == none\n'])
        for bad in [buffer([4,8],1),buffer([4],101),buffer([2147483648],2)]:
            checks.extend([f'#guard reserve {bad} accept true 3 == none\n',
                           f'#guard read {bad} accept 0 == none\n',
                           f'#guard appendReserved {bad} accept true 1 == none\n',
                           f'#guard writeRef {bad} accept true ⟨7,0,0⟩ 1 == none\n'])
        with tempfile.TemporaryDirectory(prefix='cpp-vector-faults-') as directory:
            scratch=Path(directory)
            self.check_lean(scratch,''.join(checks))
            source=scratch/'source.hpp'
            source.write_text('#include <vector>\nnamespace cp {int first(const std::vector<int>& v){return v[0];}}')
            with self.assertRaises(ValueError):
                lower_source(source)
        print(f'vector primitive rejection checks: {len(checks)}')


if __name__=='__main__':
    disable_network()
    unittest.main()
