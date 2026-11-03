"""Copy assignment preserves live prefix references and retires erased elements."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_cpp_vector import buffer
from check_public import check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
HEADER = '''import Proofs.CppVectorCopyAssign
open Proofs.CppVector Proofs.CppVectorCopyAssign Proofs.CppScalar
 def accept : Int → Bool := (⟨32,true,false⟩ : Ty).valid
 example (t s : Tracked Int) (v : t.buffer.Valid accept) (w : s.buffer.Valid accept)
     (bound : s.buffer.items.length ≤ t.buffer.limit) := assigned_valid t s accept v w bound
 example (t s : Tracked Int) (r : Reference) (old : Retired t r) := retired_assigned t s r old
 example (t s : Tracked Int) (runs : Assignments accept t s) (r : Reference) (old : Retired t r) :
     read s accept r = none := Assignments.no_resurrection runs r old
 example (s : LifetimeStore Int) (a b : Nat) (valid : s.physical.Valid accept)
     (x y : Buffer Int) (fx : s.physical.lookup a = some x) (fy : s.physical.lookup b = some y)
     (bound : y.items.length ≤ x.limit) := store_runs s a b accept valid x y fx fy bound
'''
STORE = '''
 def ta : Buffer Int := ⟨0,[10,11,12],8,100,3⟩
 def sb : Buffer Int := ⟨1,[20],1,100,7⟩
 def tc : Buffer Int := ⟨3,[99],1,100,0⟩
 def st : LifetimeStore Int := ⟨⟨[some ta,some sb,none,some tc],9,70,4⟩,fun owner i => owner*10+i+2⟩
 def oldTail : Reference := ⟨⟨0,3,2⟩,4⟩
 def sourceRef : Reference := ⟨⟨1,7,0⟩,12⟩
 def next : LifetimeStore Int := (storeAssign st 0 1 accept true).getD st
 #guard next.physical.lookup 0 == some ⟨0,[20],8,100,3⟩
 #guard next.physical.work == 14 && next.physical.liveSpace == st.physical.liveSpace && next.physical.peak == 70
 #guard (storeRead next accept ⟨⟨0,3,0⟩,2⟩).map (·.value) == some 20
 #guard storeRead next accept oldTail == none
 #guard storeRead next accept sourceRef == storeRead st accept sourceRef
 #guard next.physical.lookup 1 == st.physical.lookup 1 && next.physical.lookup 2 == none &&
   next.physical.lookup 3 == st.physical.lookup 3
 def self : LifetimeStore Int := (storeAssign st 0 0 accept true).getD st
 #guard self.physical.lookup 0 == some ta && self.physical.work == st.physical.work+1
 #guard (storeRead self accept oldTail).map (·.value) == some 12
 #guard (storeAssign st 0 1 accept false).isNone
 #guard (storeAssign st 0 2 accept true).isNone
 #guard (storeAssign st 2 1 accept true).isNone
 def shrunk : Tracked Int := ⟨(next.physical.lookup 0).getD ta,next.generation 0⟩
 def longer : Tracked Int := ⟨⟨1,[30,31,32],3,100,7⟩,fun _ => 0⟩
 def regrown : Tracked Int := assigned shrunk longer
 #guard read regrown accept oldTail == none
 #guard reference regrown accept 2 == some ⟨⟨0,3,2⟩,5⟩
 #guard (read regrown accept ⟨⟨0,3,2⟩,5⟩).map (·.value) == some 32
 #guard (copyAssign (⟨⟨0,[],0,0,0⟩,fun _ => 0⟩ : Tracked Int) longer accept true).isNone
 #guard (copyAssign (⟨⟨0,[],0,100,0⟩,fun _ => 0⟩ : Tracked Int)
   (⟨⟨1,[2147483648],1,100,0⟩,fun _ => 0⟩ : Tracked Int) accept true).isNone
'''

class VectorCopyAssignTests(unittest.TestCase):
    def test_lifetimes_assignment_store_and_native(self):
        checks = [HEADER,STORE]
        native = [r'''#include <vector>
#include <cassert>
template<class T> void check(){
for(int a=0;a<=6;a++)for(int b=0;b<=6;b++)for(int spare: {0,3,8}){
 std::vector<T> t(a),s(b);for(int i=0;i<a;i++)t[i]=T(10+i);for(int i=0;i<b;i++)s[i]=T(20+i);
 t.reserve(a+spare);auto cap=t.capacity();auto before=t.data();auto src=s.data();auto values=s;
 T* prefix=(a&&b)?&t[0]:nullptr;
 t=s;assert(t==values&&s==values&&s.data()==src);assert(t.capacity()==(cap<s.size()?s.size():cap));
 if(prefix&&b<=cap)assert(&t[0]==prefix&&*prefix==20);
 if(b<=cap)assert(t.data()==before);
 auto own=t.data();auto selfCap=t.capacity();t=t;assert(t==values&&t.data()==own&&t.capacity()==selfCap);
}
// Only the prefix pointer is dereferenced after shrinking. Retired suffix pointers are never used.
std::vector<T> t{10,11,12};t.reserve(8);T* prefix=&t[0];std::vector<T> small{20},large{30,31,32};
t=small;assert(prefix==&t[0]&&*prefix==20);t=large;assert(prefix==&t[0]&&*prefix==30);assert(t[2]==32);
}
int main(){check<int>();check<long long>();}
''']
        for case,(old,new,spare) in enumerate((a,b,c) for a in [0,1,3,6] for b in [0,1,3,6] for c in [0,3]):
            xs=list(range(10,10+old));ys=list(range(20,20+new));cap=old+spare
            checks += [f'def t{case} : Tracked Int := ⟨{buffer(xs,cap,epoch=3,owner=0)},fun i => i+2⟩',
                       f'def s{case} : Tracked Int := ⟨{buffer(ys,new,epoch=7,owner=1)},fun i => i+100⟩',
                       f'#guard (copyAssign t{case} s{case} accept true).map (·.target.buffer) == some {buffer(ys,max(cap,new),epoch=4 if new>cap else 3,owner=0)}',
                       f'#guard (copyAssign t{case} s{case} accept true).map (·.work) == some {old+new+1}',
                       f'#guard (copyAssign t{case} s{case} accept true).map (·.peak) == some {cap+new+2 if new>cap else cap+2}',
                       f'#guard (copyAssign t{case} t{case} accept true).map (·.target.buffer) == some t{case}.buffer',
                       f'#guard (copyAssign t{case} t{case} accept true).map (·.work) == some 1']
            if min(old,new)>0 and new<=cap:
                checks.append(f'#guard (read (assigned t{case} s{case}) accept ⟨⟨0,3,0⟩,2⟩).map (·.value) == some 20')
            if new<old:
                checks += [f'#guard read (assigned t{case} s{case}) accept ⟨⟨0,3,{old-1}⟩,{old+1}⟩ == none',
                           f'#guard read (assigned (assigned t{case} s{case}) (⟨{buffer(xs,old,owner=1)},fun _ => 0⟩ : Tracked Int)) accept ⟨⟨0,3,{old-1}⟩,{old+1}⟩ == none']
            if new>cap and old>0:
                checks.append(f'#guard read (assigned t{case} s{case}) accept ⟨⟨0,3,0⟩,2⟩ == none')
        with tempfile.TemporaryDirectory(prefix='vector-copy-assign-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text('\n'.join(checks))
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            source=Path(directory)/'native.cpp';source.write_text('\n'.join(native))
            binary=Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True,env={**os.environ,"ASAN_OPTIONS":os.environ.get("ASAN_OPTIONS","")+":detect_leaks=0"})

if __name__=='__main__':
    disable_network()
    unittest.main()
