"""Range assignment and fill construction: contracts and native checks."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT/'tools'))
from offline import disable_network
from check_public import check_compiler, FLAGS
from test_scalar_ir import lean_environment
from test_cpp_vector import buffer, lean_list


class RangeTests(unittest.TestCase):
    def lean(self, scratch, checks):
        path=scratch/'checks.lean'
        path.write_text('import Proofs.CppVectorRange\n'
            'open Proofs.CppVector Proofs.CppVectorRange Proofs.CppScalar\n'
            'def accept : Int → Bool := (⟨32,true,false⟩ : Ty).valid\n'+''.join(checks))
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,
                              text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_fill_and_all_subranges_match_native(self):
        checks=[]
        native=['#include "experiments/library/cpp/template/small_template.hpp"',
                '#include <cassert>', '#include <vector>', 'int main(){']
        sequences=0
        for count in [0,1,2,7,32]:
            for value in [-2147483648,-1,0,1,2147483647]:
                checks.append(f'#guard fill 7 100 {count} ({value}:Int) accept == '
                    f'some ⟨{buffer([value]*count,count)},(),{count+1},{count+2}⟩\n')
                native.append(f'{{std::vector<int> v({count},{value});'
                              f'assert(v.size()=={count});assert(v.capacity()=={count});'
                              f'for(int x:v)assert(x==({value}));}}')
                sequences+=1
        for values in [[],[0],[1,-2,3],[-2147483648,0,2147483647]]:
            source=buffer(values,len(values)+2,epoch=3,owner=9)
            for first in range(len(values)+1):
                for last in range(first,len(values)+1):
                    selected=values[first:last]
                    count=len(selected)
                    checks.append(f'#guard rangeBetween {source} accept {first} {last} == '
                                  f'some ⟨9,3,{first},{last}⟩\n')
                    for old in [[],[8],[4,4,4,4]]:
                        for spare in [0,3]:
                            capacity=len(old)+spare
                            target=buffer(old,capacity,epoch=4)
                            new_capacity=max(capacity,count)
                            updated=buffer(selected,new_capacity,epoch=5)
                            peak=capacity+count+2 if count>capacity else capacity+2
                            checks.append(f'#guard assignRange {target} {source} accept true '
                                f'⟨9,3,{first},{last}⟩ == some ⟨{updated},(),{count+1},{peak}⟩\n')
                            for index,value in enumerate(selected):
                                checks.append(f'#guard readRef {updated} accept ⟨7,5,{index}⟩ == '
                                    f'some ⟨{updated},({value}:Int),1,{new_capacity+2}⟩\n')
                            if old:
                                checks.append(f'#guard readRef {updated} accept ⟨7,4,0⟩ == none\n')
                            native.append('{std::vector<int> source{'+','.join(map(str,values))+'};'
                                'std::vector<int> target{'+','.join(map(str,old))+'};')
                            native.append(f'source.reserve({len(values)+2});target.reserve({capacity});'
                                f'target.assign(source.begin()+{first},source.begin()+{last});'
                                f'assert(target.size()=={count});assert(target.capacity()=={new_capacity});')
                            for index,value in enumerate(selected):
                                native.append(f'assert(target[{index}]==({value}));')
                            for index,value in enumerate(values):
                                native.append(f'assert(source[{index}]==({value}));')
                            native.append(f'assert(source.size()=={len(values)});'
                                          f'assert(source.capacity()=={len(values)+2});'+'}')
                            sequences+=1
        native.append('}')
        with tempfile.TemporaryDirectory(prefix='vector-ranges-') as directory:
            scratch=Path(directory);self.lean(scratch,checks)
            source=scratch/'native.cpp';source.write_text('\n'.join(native))
            check_compiler(); executable=scratch/'native'
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(ROOT),str(source),'-o',str(executable)],check=True,cwd=ROOT)
            subprocess.run([str(executable)],check=True)
        print(f'vector ranges: {len(checks)} Lean checks, {sequences} native sequences')

    def test_range_lifetime_alias_and_bounds_are_rejected(self):
        target=buffer([1],3,epoch=4)
        source=buffer([3,8],2,epoch=3,owner=9)
        checks=[]
        for first,last in [(-1,0),(2,1),(0,3),(3,3),(0,-1)]:
            checks.append(f'#guard rangeBetween {source} accept ({first}:Int) ({last}:Int) == none\n')
        for range_ in ['⟨9,2,0,2⟩','⟨10,3,0,2⟩','⟨9,3,2,1⟩','⟨9,3,0,3⟩']:
            checks.append(f'#guard assignRange {target} {source} accept true {range_} == none\n')
        checks.extend([f'#guard assignRange {source} {source} accept true ⟨9,3,0,2⟩ == none\n',
            f'#guard assignRange {target} {source} accept false ⟨9,3,0,2⟩ == none\n',
            f'#guard assignRange {buffer([],0,owner=7,limit=1)} {source} accept true ⟨9,3,0,2⟩ == none\n',
            '#guard fill 7 3 4 (0:Int) accept == none\n',
            '#guard fill 7 100 2 (2147483648:Int) accept == none\n'])
        for invalid_target in [buffer([1,2],1),buffer([2147483648],2)]:
            checks.append(f'#guard assignRange {invalid_target} {source} accept true ⟨9,3,0,1⟩ == none\n')
        for invalid in [buffer([1,2],1,owner=9),buffer([2147483648],2,owner=9)]:
            checks.append(f'#guard assignRange {target} {invalid} accept true ⟨9,0,0,1⟩ == none\n')
        with tempfile.TemporaryDirectory(prefix='vector-range-faults-') as directory:
            self.lean(Path(directory),checks)
        print(f'vector range rejection checks: {len(checks)}')


if __name__=='__main__':
    disable_network()
    unittest.main()
