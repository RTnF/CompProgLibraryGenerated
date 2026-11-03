"""Typed nested-frame copy assignment, stable grants and element lifetimes."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from check_public import check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''import Proofs.CppFrameCopyAssign
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppFrameCopyAssign
 def i32 : Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def rows : Element := .vector atom
 def initial : TrackedFrame := ⟨⟨⟨⟨[some ⟨rows,none,some 0,[1,2,3]⟩,
   some ⟨atom,some 0,none,[]⟩,some ⟨atom,some 0,none,[]⟩,some ⟨atom,some 0,none,[]⟩,
   some ⟨atom,none,some 1,[]⟩,none]⟩,
   ⟨[some ⟨0,[.child 1,.child 2,.child 3],5,64,0⟩,
     some ⟨1,[.integer 10,.integer 11,.integer 12],8,64,3⟩,
     some ⟨2,[.integer 20],1,64,0⟩,some ⟨3,[.integer 30,.integer 31,.integer 32],3,64,0⟩,
     some ⟨4,[.integer 100,.integer 101,.integer 102,.integer 103,.integer 104,.integer 105,.integer 106,.integer 107,.integer 108],9,64,0⟩,none],7,0,5⟩⟩,
     [true,false,false,false,true,false],
     [⟨0,rows,true,.root 0⟩,⟨0,rows,false,.root 0⟩,⟨4,atom,false,.root 1⟩,
      ⟨1,atom,true,.child ⟨0,0,0⟩⟩,⟨2,atom,false,.child ⟨0,0,1⟩⟩,
      ⟨3,atom,false,.child ⟨0,0,2⟩⟩,⟨1,atom,false,.child ⟨0,0,0⟩⟩]⟩,fun owner i => owner*10+i+2⟩
 #guard initial.frame.state.wellFormed
 #guard initial.frame.state.liveSpace == 28
 #guard initial.frame.state.storage.liveSpace == 31
 def savedHead : TrackedReference := ⟨⟨3,i32,true,⟨1,3,0⟩⟩,12⟩
 def suffix : TrackedReference := ⟨⟨3,i32,true,⟨1,3,2⟩⟩,14⟩
 def readonlyPrefix : TrackedReference := ⟨⟨6,i32,false,⟨1,3,0⟩⟩,12⟩
 def sourceRef : TrackedReference := ⟨⟨4,i32,false,⟨2,0,0⟩⟩,22⟩
 #guard elementRef initial 3 i32 0 == some savedHead
 #guard read initial savedHead == some 10 && read initial suffix == some 12
 def shrunk : TrackedFrame := (copyAssign initial 3 4 i32).getD initial
 #guard (copyAssign initial 3 4 i32).isSome
 #guard shrunk.frame.state.wellFormed
 #guard shrunk.frame.state.storage.lookup 1 == some ⟨1,[.integer 20],8,64,3⟩
 #guard shrunk.frame.state.liveSpace == 28 && shrunk.frame.state.storage.work == 12 && shrunk.frame.state.storage.peak == 24
 #guard shrunk.frame.state.storage.baseSpace == 5
 #guard read shrunk savedHead == some 20 && read shrunk readonlyPrefix == some 20
 #guard read shrunk sourceRef == some 20 && read shrunk suffix == none
 #guard (write shrunk readonlyPrefix 99).isNone && (write shrunk suffix 99).isNone
 #guard shrunk.frame.state.storage.lookup 0 == initial.frame.state.storage.lookup 0 &&
   shrunk.frame.state.storage.lookup 2 == initial.frame.state.storage.lookup 2 &&
   shrunk.frame.state.storage.lookup 3 == initial.frame.state.storage.lookup 3 &&
   shrunk.frame.state.storage.lookup 4 == initial.frame.state.storage.lookup 4 && shrunk.frame.state.storage.lookup 5 == none
 #guard shrunk.frame.bindings == initial.frame.bindings && shrunk.frame.rootWritable == initial.frame.rootWritable &&
   shrunk.frame.state.forest == initial.frame.state.forest
 def regrown : TrackedFrame := (copyAssign shrunk 3 5 i32).getD shrunk
 #guard (copyAssign shrunk 3 5 i32).isSome
 #guard regrown.frame.state.wellFormed && regrown.frame.state.storage.work == 17 && regrown.frame.state.storage.peak == 24
 #guard read regrown suffix == none && read regrown savedHead == some 30
 #guard (write regrown suffix 99).isNone
 def fresh : TrackedReference := (elementRef regrown 3 i32 2).getD suffix
 #guard fresh == ⟨⟨3,i32,true,⟨1,3,2⟩⟩,15⟩ && read regrown fresh == some 32
 def changed : TrackedFrame := (write regrown fresh 91).getD regrown
 #guard (write regrown fresh 91).isSome && read changed fresh == some 91 && read changed suffix == none
 def grown : TrackedFrame := (copyAssign initial 3 2 i32).getD initial
 #guard (copyAssign initial 3 2 i32).isSome
 #guard grown.frame.state.wellFormed && grown.frame.state.liveSpace == 29
 #guard grown.frame.state.storage.work == 20 && grown.frame.state.storage.peak == 33
 #guard read grown savedHead == none && read grown suffix == none
 #guard (grown.frame.state.storage.lookup 1).map (fun b => (b.capacity,b.epoch)) == some (9,4)
 def self : TrackedFrame := (copyAssign initial 3 6 i32).getD initial
 #guard (copyAssign initial 3 6 i32).isSome
 #guard self.frame.state.wellFormed && self.frame.state.storage.lookup 1 == initial.frame.state.storage.lookup 1
 #guard self.frame.state.storage.work == 8 && self.frame.state.storage.peak == 23 && read self suffix == some 12
 #guard (copyAssign initial 6 4 i32).isNone
 #guard (copyAssign initial 0 4 i32).isNone
 #guard (copyAssign initial 3 0 i32).isNone
 #guard (copyAssign initial 99 4 i32).isNone
 #guard (copyAssign initial 3 4 ⟨32,false,false⟩).isNone
 #guard (copyAssign ⟨{initial.frame with rootWritable := []},initial.generation⟩ 3 4 i32).isNone
 #guard read regrown {fresh with generation := 14} == none
 #guard read regrown {fresh with original := {fresh.original with slot := 4}} == none
 def movedHeader : TrackedFrame := ⟨(initial.frame.reserve 0 rows 17).getD initial.frame,initial.generation⟩
 #guard movedHeader.frame.state.wellFormed && read movedHeader savedHead == some 10
 #guard (copyAssign movedHeader 3 4 i32).isNone
 def high : TrackedFrame := ⟨{initial.frame with state := {initial.frame.state with storage := {initial.frame.state.storage with peak := 1000}}},initial.generation⟩
 #guard ((copyAssign high 3 2 i32).map (fun s => s.frame.state.storage.peak)) == some 1000
 example (s : TrackedFrame) (a b : Nat) (ty : Ty) (tb sb : Binding) (x y : Buffer Value)
   (fx : s.frame.resolve a (.integer ty) = some (tb,x)) (fy : s.frame.resolve b (.integer ty) = some (sb,y))
   (w : tb.writable = true) (bound : y.items.length ≤ x.limit) := assign_runs s a b ty tb sb x y fx fy w bound
 example (s t : TrackedFrame) (a b : Nat) (ty : Ty) (ran : copyAssign s a b ty = some t) := assign_success s t a b ty ran
 example (s t : TrackedFrame) (runs : Assignments s t) (ref : TrackedReference) (old : Retired s ref) :
   read t ref = none := Assignments.no_resurrection runs ref old
 example (s : TrackedFrame) (ref : TrackedReference) (v : Int) (old : Retired s ref) :
   write s ref v = none := write_retired s ref v old
 example (s : TrackedFrame) (owner : Nat) (old : Buffer Value) (tag : Tag)
   (result : Proofs.CppVectorCopyAssign.Assignment Value)
   (f : s.frame.state.storage.lookup owner = some old) (t : s.frame.state.forest.lookup owner = some tag) :=
   after_space s owner old tag result f t
'''
NATIVE = r'''#include <vector>
#include <cassert>
int main(){
 std::vector<std::vector<int>> rows{{10,11,12},{20},{30,31,32}};rows.reserve(5);rows[0].reserve(8);
 std::vector<int> big{100,101,102,103,104,105,106,107,108};
 auto source=rows[1];int* savedHead=&rows[0][0];const int* sourceRef=&rows[1][0];
 rows[0]=rows[1];assert(rows[0]==source&&savedHead==&rows[0][0]&&*savedHead==20&&*sourceRef==20&&rows[0].capacity()==8);
 rows[0]=rows[2];assert(savedHead==&rows[0][0]&&*savedHead==30&&rows[0][2]==32);rows[0][2]=91;
 assert(rows[1]==source&&rows[2][2]==32);rows.reserve(17);assert(savedHead==&rows[0][0]&&*savedHead==30);
 rows[0]=big;assert(rows[0]==big&&rows[0].capacity()==9&&rows[1]==source&&*sourceRef==20);
 auto own=rows[0].data();rows[0]=rows[0];assert(rows[0]==big&&rows[0].data()==own);
}
'''

class FrameCopyAssignTests(unittest.TestCase):
    def test_typed_nested_frame_assignment_lifetimes_and_space(self):
        with tempfile.TemporaryDirectory(prefix='frame-copy-assign-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text(CHECKS)
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
