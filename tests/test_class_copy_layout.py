"""Audited field layouts, generated UF entry equality and const/mutable copies."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools'), str(ROOT/'tests')]
import class_copy_layout as layout
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from offline import disable_network

PACKET = '''#include <vector>
namespace other {
struct Packet {
  std::vector<long long> data;
  const long long stamp;
  mutable unsigned int count;
  mutable bool ready;
  Packet(unsigned long n, long long value):data(n,value),stamp(value+1),count(0),ready(false) {
    unsigned int count=3; this->count=count;
  }
  unsigned int bump() const { ++count; ready=true; return count; }
};
}
'''

class ClassLayoutTests(unittest.TestCase):
    def check_lean(self, text, directory):
        path = Path(directory)/'checks.lean'
        path.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_union_find_generated_export_matches_existing_entry_for_all_states(self):
        source = ROOT/'experiments/verification/data_structure/union_find.hpp'
        generated = layout.emit_class_layout(source,'cp::UnionFind','DraftUFLayout')
        checks = r'''
example : DraftUFLayout.profile = Proofs.UfClassCopyBridge.profile := rfl
example : DraftUFLayout.UnionFind_construct1 =
    Proofs.UnionFindConstructionInstance.UnionFind_construct1 := rfl
example (fuel : Nat) (caller : Proofs.CppNestedProgram.NState)
    (args : List Proofs.CppNestedCall.NArgument) :
    DraftUFLayout.UnionFind_construct1_exportFuel fuel caller args =
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel fuel caller args
        1 (.integer ⟨32,true,false⟩) [⟨2,⟨32,true,false⟩⟩,⟨3,⟨32,true,false⟩⟩] := rfl
example (s : Proofs.CppNestedProgram.NState) (r : Proofs.UfReceiverState.Layout) :
    DraftUFLayout.copy s ⟨r.vectorSlot,[r.countSlot,r.nSlot]⟩ =
      (Proofs.UfCopyFields.copyReceiver s r).map (fun p =>
        (p.1,Proofs.CppConstructorFinish.reference s 2)) :=
  Proofs.UfClassCopyBridge.copy_equiv s r
'''
        with tempfile.TemporaryDirectory(prefix='class-layout-uf-') as directory:
            self.check_lean('import Proofs.UfClassCopyBridge\nimport Proofs.Generated.UnionFindConstruction\n'+
                            generated+checks,directory)

    def test_declared_const_vector_in_const_method_keeps_one_qualification(self):
        with tempfile.TemporaryDirectory(prefix='class-layout-const-vector-') as directory:
            source = Path(directory)/'fixed.hpp'
            source.write_text('#include <vector>\nnamespace other {struct Fixed {'
                              'const std::vector<int> payload;int tag;'
                              'Fixed():payload(),tag(0){}'
                              'unsigned long size() const{return payload.size();}};}\n')
            ir = lower_source(source)
            method = next(f for f in ir['functions'] if f['name']=='Fixed_size')
            self.assertFalse(method['parameters'][0]['writable'])
            generated = layout.emit_class_layout(source,'other::Fixed','DraftFixedLayout')
            self.check_lean(generated+'\nexample : DraftFixedLayout.profile.vectorWritable = false := rfl\n',
                            directory)

    def test_initializer_call_temporary_and_profile_callee_name(self):
        with tempfile.TemporaryDirectory(prefix='class-layout-call-') as directory:
            source = Path(directory)/'box.hpp'
            source.write_text('#include <vector>\nnamespace cp {int profile(int n){return n+1;}'
                              'struct Box {std::vector<int> data;int count;'
                              'Box(int n):data(),count(profile(n)){} };}\n')
            generated = layout.emit_class_layout(source,'cp::Box','DraftCallLayout')
            checks = r'''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
def callLayoutCaller : NState :=
  ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
#guard DraftCallLayout.Box_construct0_vectorSlot = 1
#guard DraftCallLayout.Box_construct0_scalarFields = [⟨3,⟨32,true,false⟩⟩]
def callLayoutCreated : Option (NState × Proofs.CppConstructorFinish.ObjectRef) :=
  match DraftCallLayout.Box_construct0_exportFuel 64 callLayoutCaller
      [.value (.literal ⟨32,true,false⟩ 1)] with
  | .finished r => some r
  | _ => none
#guard callLayoutCreated.map (fun r => r.1.scalars.memory.map (fun c => c.value)) = some [2]
'''
            self.check_lean(generated+checks,directory)

    def test_const_fields_mutable_const_method_extra_local_and_native_values(self):
        with tempfile.TemporaryDirectory(prefix='class-layout-packet-') as directory:
            source = Path(directory)/'packet.hpp'
            source.write_text(PACKET)
            generated = layout.emit_class_layout(source,'other::Packet','DraftPacketLayout')
            methods = lower_source(source)
            bump = next(f for f in methods['functions'] if f['name']=='Packet_bump')
            self.assertTrue(bump['parameters'][2]['writable'])
            self.assertTrue(bump['parameters'][2]['reference'])
            methods_lean = emit_lean(methods,'DraftPacketMethods').replace('import Proofs.CppNestedCall\n','')
            checks = r'''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
def emptyLayoutCaller : NState :=
  ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def packetCreated : Option (NState × Proofs.CppConstructorFinish.ObjectRef) :=
  match DraftPacketLayout.Packet_construct0_exportFuel 64 emptyLayoutCaller
      [.value (.literal ⟨64,false,false⟩ 2),.value (.literal ⟨64,true,false⟩ 7)] with
  | .finished r => some r
  | _ => none
#guard packetCreated.isSome
#guard DraftPacketLayout.Packet_construct0_vectorSlot == 2
#guard DraftPacketLayout.Packet_construct0_scalarFields =
  [⟨3,⟨64,true,false⟩⟩,⟨4,⟨32,false,false⟩⟩,⟨5,⟨1,false,true⟩⟩]
#guard packetCreated.map (fun r => r.1.scalars.memory.map (fun c => c.value)) == some [8,3,0]
#guard packetCreated.map (fun r => r.2.scalarSlots) == some [1,2,3]
#guard packetCreated.map (fun r => r.1.scalars.bindings.map (fun b => b.writable)) == some [false,true,true]
def bumpPacket (r : NState × Proofs.CppConstructorFinish.ObjectRef) :
    Option (NState × Proofs.CppConstructorFinish.ObjectRef × Int) :=
  match DraftPacketMethods.Packet_bump.callFuel 64 r.1
      [.vectorReference r.2.vectorSlot,.value (.literal ⟨64,true,false⟩ 8),
       .scalarReference r.2.scalarSlots[1]!,.scalarReference r.2.scalarSlots[2]!] with
  | .finished (next,.scalar value) => some (next,r.2,value)
  | _ => none
def packetBumped := packetCreated.bind bumpPacket
#guard packetBumped.map (fun r => r.2.2) == some 4
#guard packetBumped.map (fun r => r.1.scalars.memory.map (fun c => c.value)) == some [8,4,1]
def packetCopied := packetBumped.bind fun r => DraftPacketLayout.copyConst r.1 r.2.1
#guard packetCopied.isSome
#guard packetCopied.map (fun r => r.1.frame.bindings.map (fun b => b.writable)) == some [true,false]
#guard packetCopied.map (fun r => r.1.scalars.memory.map (fun c => c.value)) == some [8,4,1,8,4,1]
def copiedBumped := packetCopied.bind bumpPacket
#guard copiedBumped.map (fun r => r.2.2) == some 5
#guard copiedBumped.map (fun r => r.1.scalars.memory.map (fun c => c.value)) == some [8,4,1,8,5,1]
'''
            self.check_lean(generated+methods_lean+checks,directory)
            main = Path(directory)/'native.cpp'
            main.write_text('#include "packet.hpp"\n#include <iostream>\n'
                            'int main(){other::Packet p(2,7);'
                            'std::cout<<p.data[1]<<" "<<p.stamp<<" "<<p.count<<" "<<p.ready<<" "'
                            '<<p.bump()<<" "<<p.ready<<" ";'
                            'const other::Packet q(p);std::cout<<q.count<<" "<<q.ready<<" "<<q.bump()<<" "'
                            '<<q.ready<<"\\n";}\n')
            binary = Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',str(main),'-o',str(binary)],check=True)
            result = subprocess.run([str(binary)],check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout,'7 8 3 0 4 1 4 1 5 1\n')

if __name__ == '__main__':
    disable_network()
    unittest.main()
