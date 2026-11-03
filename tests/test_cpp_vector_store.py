"""Vector owner lifetimes, store operations and aggregate resource checks."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'tools'))
from test_scalar_ir import lean_environment
from test_cpp_vector import buffer
from check_public import FLAGS,check_compiler
from offline import disable_network


def store(objects,work,peak,base=0):
    slots=','.join('none' if obj is None else 'some '+buffer(**obj) for obj in objects)
    return f'(⟨[{slots}],{work},{peak},{base}⟩ : Store Int)'


class StoreTests(unittest.TestCase):
    def lean(self,scratch,checks):
        path=scratch/'checks.lean';path.write_text('import Proofs.CppVectorStore\n'
            'open Proofs.CppVector Proofs.CppVectorRange Proofs.CppVectorStore Proofs.CppScalar\n'
            'def accept : Int → Bool := (⟨32,true,false⟩ : Ty).valid\n'+''.join(checks))
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_construct_reserve_assign_read_write_and_reconstruct(self):
        checks=[];native=['#include "experiments/library/cpp/template/small_template.hpp"',
                         '#include <cassert>','#include <vector>','int main(){']
        for n in [0,1,3,7]:
            for m in [0,2,8]:
                for request in [0,m,m+3]:
                    for baseline in [0,n+1]:
                        work=0;peak=0;objects=[]
                        def current():return store(objects,work,peak,baseline)
                        def live():return sum(o['capacity']+1 for o in objects if o is not None)
                        def update(cost,extra):
                            nonlocal work,peak
                            work+=cost;peak=max(peak,max(0,live()+extra-baseline))
                        def construct(count,value):
                            before=current();owner=len(objects)
                            update(count+1,count+2)
                            objects.append(dict(values=[value]*count,capacity=count,owner=owner))
                            checks.append(f'#guard Store.construct {before} accept 100 {count} ({value}:Int) == '
                                          f'some ({current()},{owner})\n')
                        if baseline:
                            # Caller source exists at function entry; its initial
                            # live footprint defines the resource baseline.
                            objects.append(dict(values=[5]*n,capacity=n,owner=0))
                        else:
                            construct(n,5)
                        construct(m,-2)
                        before=current();target=objects[1];oldcap=target['capacity']
                        grows=request>oldcap
                        update(m+1 if grows else 1,request+1 if grows else 0)
                        target['capacity']=max(oldcap,request);target['epoch']=int(grows)
                        checks.append(f'#guard Store.reserve {before} accept true 1 {request} == some ({current()},())\n')
                        before=current();cap=target['capacity'];update(n+1,n+1 if n>cap else 1)
                        target.update(values=[5]*n,capacity=max(cap,n),epoch=target['epoch']+1)
                        checks.append(f'#guard Store.assign {before} accept true 1 ⟨0,0,0,{n}⟩ == some ({current()},())\n')
                        before=current();update(1,0);objects[0]=None
                        checks.append(f'#guard Store.destroy {before} 0 == some {current()}\n')
                        construct(n,11)
                        checks.append(f'#guard Store.readReference {current()} accept ⟨0,0,0⟩ == none\n')
                        if n:
                            before=current();update(1,1);objects[2]['values'][0]=17
                            checks.append(f'#guard Store.writeReference {before} accept true ⟨2,0,0⟩ 17 == some ({current()},())\n')
                            before=current();update(1,1)
                            checks.append(f'#guard Store.read {before} accept ⟨2,0,0⟩ == some ({current()},(17:Int))\n')
                        spare=target['capacity']>len(target['values'])
                        appended=5 if n else -3
                        if spare:
                            if n:
                                before=current();update(1,1)
                                checks.append(f'#guard Store.read {before} accept ⟨1,{target["epoch"]},0⟩ == some ({current()},(5:Int))\n')
                            before=current();update(2,1);target['values'].append(appended)
                            checks.append(f'#guard Store.appendReserved {before} accept true 1 ({appended}:Int) == some ({current()},())\n')
                        else:
                            checks.append(f'#guard Store.appendReserved {current()} accept true 1 5 == none\n')
                        # Native source/target lifetimes and allocation behavior.
                        native.append(f'{{std::vector<int> target({m},-2);target.reserve({request});'
                                      f'{{std::vector<int> source({n},5);target.assign(source.begin(),source.end());}}'
                                      f'assert(target.size()=={n});assert(target.capacity()=={max(m,request,n)});'
                                      'for(int x:target)assert(x==5);'
                                      f'{{std::vector<int> fresh({n},11);')
                        if n:native.append('fresh[0]=17;assert(fresh[0]==17);')
                        if spare:
                            if n:
                                native.append('const int* ref=&target[0];target.emplace_back(target[0]);assert(ref==&target[0]);assert(*ref==5);')
                            else:
                                native.append('target.emplace_back(-3);')
                            native.append(f'assert(target.size()=={n+1});assert(target.back()=={appended});')
                        native.append('}}')
        native.append('}')
        with tempfile.TemporaryDirectory(prefix='vector-store-') as directory:
            scratch=Path(directory);self.lean(scratch,checks)
            source=scratch/'native.cpp';source.write_text('\n'.join(native));exe=scratch/'native'
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT),
                            str(source),'-o',str(exe)],check=True,cwd=ROOT)
            subprocess.run([str(exe)],check=True)
        print(f'vector store: {len(checks)} Lean checks, 72 native lifetime scenarios')

    def test_tombstones_permissions_and_forged_results(self):
        checks=[];objects=[];work=0;peak=0
        for owner in range(24):
            n=owner%5;value=owner-12
            before=store(objects,work,peak);work+=n+1;peak=max(peak,n+2)
            objects.append(dict(values=[value]*n,capacity=n,owner=owner))
            checks.append(f'#guard Store.construct {before} accept 100 {n} ({value}:Int) == '
                          f'some ({store(objects,work,peak)},{owner})\n')
            before=store(objects,work,peak);work+=1;objects[-1]=None
            checks.append(f'#guard Store.destroy {before} {owner} == some {store(objects,work,peak)}\n')
            for old in range(owner+1):
                checks.append(f'#guard Store.readReference {store(objects,work,peak)} accept ⟨{old},0,0⟩ == none\n')
        checks.append(f'#guard Store.liveSpace {store(objects,work,peak)} == 0\n')
        live=store([dict(values=[3],capacity=2,owner=0)],2,4)
        wrong=buffer([8],2,owner=1)
        forged=buffer([3],99,owner=0)
        checks.extend([f'#guard Store.reserve {live} accept false 0 5 == none\n',
                       f'#guard Store.appendReserved {live} accept false 0 5 == none\n',
                       f'#guard Store.writeReference {live} accept false ⟨0,0,0⟩ 5 == none\n',
                       f'#guard Store.commit {live} 0 accept (⟨{wrong},(),1,4⟩ : Result Int Unit) == none\n',
                       f'#guard Store.commit {live} 0 accept (⟨{forged},(),1,4⟩ : Result Int Unit) == none\n',
                       f'#guard Store.commit {store(objects,work,peak)} 0 accept (⟨{forged},(),1,100⟩ : Result Int Unit) == none\n',
                       f'#guard Store.assign {live} accept true 0 ⟨0,0,0,1⟩ == none\n',
                       f'#guard Store.destroy {live} 1 == none\n'])
        with tempfile.TemporaryDirectory(prefix='vector-store-faults-') as directory:
            self.lean(Path(directory),checks)
        print(f'vector store lifetime/rejection checks: {len(checks)}')

if __name__=='__main__':
    disable_network();unittest.main()
