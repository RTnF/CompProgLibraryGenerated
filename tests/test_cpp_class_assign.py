"""Class assignment data, declaration order, actual scalar commands and ghost lifetimes."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from check_public import check_compiler
import test_cpp_frame_copy_assign as frame
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppClassCopy Proofs.CppClassAssign
 def state : NState := ⟨⟨[⟨i32,2⟩,⟨i32,3⟩,⟨i32,1⟩,⟨i32,1⟩,⟨i32,9876⟩,⟨i32,3⟩,⟨i32,3⟩],
   [⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,false⟩,⟨4,true⟩,⟨5,false⟩,⟨6,false⟩],10,0,0⟩,
   initial.frame,[.vector 3,.scalar 0,.scalar 1,.vector 4,.scalar 2,.scalar 3,.scalar 4,.vector 6,.vector 5,.scalar 5,.scalar 6],0,0⟩
 def target : ObjectRef := ⟨0,[1,2]⟩
 def smallSource : ObjectRef := ⟨3,[4,5]⟩
 def longSource : ObjectRef := ⟨8,[9,10]⟩
 def profile : Profile := ⟨i32,true,[(i32,true),(i32,true)]⟩
 def first := (trackedAssignClass state initial.generation target smallSource profile).getD ((state,target),initial.generation)
 def one : NState := first.1.1
 #guard (assignClass state target smallSource profile).isSome
 #guard (assignClass state target smallSource profile).map Prod.snd == some target
 #guard (assignClass state target smallSource profile).map (fun p => p.1.frame) == some one.frame
 #guard one.scalars.memory.map (·.value) == [1,1,1,1,9876,3,3]
 #guard one.scalars.bindings == state.scalars.bindings && one.slots == state.slots && one.scope == state.scope
 #guard one.work == 27 && one.frame.state.wellFormed
 #guard one.scalars.peak == 15 && one.peak == 39
 #guard one.frame.state.liveSpace == 28 && one.frame.state.storage.peak == 24
 #guard Proofs.CppFrameCopyAssign.read ⟨one.frame,first.2⟩ savedHead == some 20
 #guard Proofs.CppFrameCopyAssign.read ⟨one.frame,first.2⟩ suffix == none
 #guard Proofs.CppFrameCopyAssign.read ⟨one.frame,first.2⟩ sourceRef == some 20
 def second := (trackedAssignClass one first.2 target longSource profile).getD ((one,target),first.2)
 def two : NState := second.1.1
 #guard two.scalars.memory.map (·.value) == [3,3,1,1,9876,3,3]
 #guard two.work == 37 && two.frame.state.wellFormed
 #guard Proofs.CppFrameCopyAssign.read ⟨two.frame,second.2⟩ savedHead == some 30
 #guard Proofs.CppFrameCopyAssign.read ⟨two.frame,second.2⟩ suffix == none
 #guard (Proofs.CppFrameCopyAssign.write ⟨two.frame,second.2⟩ suffix 99).isNone
 def freshTail := (Proofs.CppFrameCopyAssign.elementRef ⟨two.frame,second.2⟩ 3 i32 2).getD suffix
 #guard freshTail.generation == 15 && Proofs.CppFrameCopyAssign.read ⟨two.frame,second.2⟩ freshTail == some 32
 #guard (assignClass state target target profile).map (fun p => p.1.scalars.memory) == some state.scalars.memory
 #guard (assignClass state target target profile).map (fun p => p.1.work) == some 23
 #guard (assignClass state target target profile).map Prod.snd == some target
 #guard (assignClass state ⟨7,[1,2]⟩ smallSource profile).isNone
 #guard (assignClass state ⟨0,[4,2]⟩ smallSource profile).isNone
 #guard (assignClass state target smallSource ⟨i32,false,[(i32,true),(i32,true)]⟩).isNone
 #guard (assignClass state target smallSource ⟨i32,true,[(i32,false),(i32,true)]⟩).isNone
 #guard (assignClass state target smallSource ⟨i32,true,[(i32,true)]⟩).isNone
 #guard (assignClass state target ⟨3,[6,10]⟩ profile).map (fun p => p.1.scalars.memory.map (·.value)) ==
   some [9876,3,1,1,9876,3,3]
 -- The second read observes the first write, rather than a snapshot of all source fields.
 #guard (assignFields state [1,2] [4,1] [(i32,true),(i32,true)]).map (fun s => s.scalars.memory.map (·.value)) ==
   some [1,1,1,1,9876,3,3]
 def ordered := (fieldsCommand [1,2] [4,1] [(i32,true),(i32,true)]).getD (.primitive .skip)
 #guard (match runFuel 3 ordered state with
   | .finished step => step.state.scalars.memory.map (·.value) == [1,1,1,1,9876,3,3] &&
       step.state.work == state.work+4 && step.returned.isNone && !step.breaking
   | _ => false)
 def highState : NState := {state with scalars := {state.scalars with baseMemory := 2,peak := 400},peak := 1000}
 #guard (assignClass highState target smallSource profile).map (fun p => (p.1.scalars.baseMemory,p.1.scalars.peak,p.1.peak)) == some (2,400,1000)
 example (s out : NState) (a b r : ObjectRef) (p : Profile) (ran : assignClass s a b p = some (out,r)) :=
   class_peak s out a b r p ran
 example (s out : NState) (a b r : ObjectRef) (p : Profile) (ran : assignClass s a b p = some (out,r)) :
   out.frame.state.wellFormed = true := class_wellFormed s out a b r p ran
 example (s : NState) (g : Generations) (a b : ObjectRef) (p : Profile) :
   (trackedAssignClass s g a b p).map Prod.fst = assignClass s a b p := tracked_class_data s g a b p
 example (s out : NState) (a b r : ObjectRef) (p : Profile) (g : Generations)
   (ran : assignClass s a b p = some (out,r)) := data_lifts s out g a b r p ran
 example (s out : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
   (ran : assignFields s targets sources fields = some out) := fields_program s out targets sources fields ran
 example (s : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
   (ready : Ready s targets sources fields) := fields_terminate s targets sources fields ready
 example (s : NState) (a b : ObjectRef) (p : Profile) (x y : Nat) (tb sb : Binding)
   (t v : Buffer Value) (permission : p.vectorWritable = true)
   (tx : s.vectorSlot a.vectorSlot = some x) (sy : s.vectorSlot b.vectorSlot = some y)
   (tr : s.frame.resolve x (.integer p.element) = some (tb,t))
   (sr : s.frame.resolve y (.integer p.element) = some (sb,v))
   (writable : tb.writable = true) (bound : v.items.length ≤ t.limit)
   (ready : Ready s a.scalarSlots b.scalarSlots p.scalarFields) :=
   class_terminate s a b p x y tb sb t v permission tx sy tr sr writable bound ready
 example (s out : NState) (g final : Generations) (runs : ClassAssignments s g out final)
   (ref : TrackedReference) (old : Retired ⟨s.frame,g⟩ ref) :
   Proofs.CppFrameCopyAssign.read ⟨out.frame,final⟩ ref = none := ClassAssignments.no_resurrection runs ref old
'''
NATIVE = r'''#include <vector>
#include <cassert>
#include <type_traits>
struct Packet {std::vector<int> data;int count,n;};
int main(){
 Packet target{{10,11,12},2,3};target.data.reserve(8);const Packet small{{20},1,1};const Packet larger{{30,31,32},3,3};
 int* head=&target.data[0];auto* sourceHead=small.data.data();
 static_assert(std::is_same<decltype(target=small),Packet&>::value);
 Packet* returned=&(target=small);assert(returned==&target&&target.data==small.data&&target.count==1&&target.n==1);
 assert(head==target.data.data()&&*head==20&&sourceHead==small.data.data());
 returned=&(target=larger);assert(returned==&target&&head==target.data.data()&&*head==30&&target.data[2]==32);
 assert(target.count==3&&target.n==3&&small.data[0]==20&&larger.data[2]==32);
 auto values=target.data;auto cap=target.data.capacity();target=target;assert(target.data==values&&target.data.capacity()==cap&&head==target.data.data());
 int a=2,b=3,c=1;a=c;b=a;assert(a==1&&b==1);
}
'''

class ClassAssignTests(unittest.TestCase):
    def test_class_data_scalar_commands_and_lifetime_lifting(self):
        with tempfile.TemporaryDirectory(prefix='class-assign-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppClassAssign\n'+frame.CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            source=Path(directory)/'native.cpp';source.write_text(NATIVE)
            binary=Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True,env={**os.environ,'ASAN_OPTIONS':os.environ.get('ASAN_OPTIONS','')+':detect_leaks=0'})

if __name__=='__main__':
    disable_network()
    unittest.main()
