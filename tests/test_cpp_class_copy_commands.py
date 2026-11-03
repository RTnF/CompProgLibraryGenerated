"""Ordinary member-copy commands, old references, guards and generated profiles."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/"verifier"),str(ROOT/"tools"),str(ROOT/"tests")]
from test_cpp_nested_copy import HEADER,CHECKS as FIXTURE
from test_append_row import initial
from test_scalar_ir import lean_environment
from test_class_copy_layout import PACKET
from class_copy_layout import emit_class_layout
from nested_ir import lower_source,emit_lean
from check_public import check_compiler
from offline import disable_network

class ClassCopyCommandTests(unittest.TestCase):
    def check_lean(self, text, directory):
        path=Path(directory)/'checks.lean'
        path.write_text(text)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,
                              capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_memberwise_layout_refs_resources_and_initial_source_guard(self):
        with tempfile.TemporaryDirectory(prefix='class-copy-commands-') as directory:
            self.check_lean('import Proofs.CppClassCopyCommands\n'+HEADER+
                            f'\ndef initial := {initial(3,8)}\n'+FIXTURE+CHECKS,directory)

    def test_audited_profile_command_copy_then_const_method(self):
        with tempfile.TemporaryDirectory(prefix='class-copy-command-profile-') as directory:
            source=Path(directory)/'packet.hpp';source.write_text(PACKET)
            generated=emit_class_layout(source,'other::Packet','GeneratedCopyCommands')
            methods=emit_lean(lower_source(source),'CopyCommandMethods').replace(
                'import Proofs.CppNestedCall\n','')
            checks=r'''
namespace GeneratedCommandChecks
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def constructed : Option (NState × ObjectRef) :=
  match GeneratedCopyCommands.Packet_construct0_exportFuel 64 empty
      [.value (.literal ⟨64,false,false⟩ 2),.value (.literal ⟨64,true,false⟩ 7)] with
  | .finished r => some r
  | _ => none
#guard constructed.isSome
def pair := constructed.getD (empty,⟨999,[]⟩)
def normal : Option NState :=
  match GeneratedCopyCommands.runCopyFuel 16 pair.1 pair.2 true with
  | .finished step => some step.state
  | _ => none
def direct := GeneratedCopyCommands.copyConst pair.1 pair.2
#guard normal.isSome
#guard normal.map (fun s => s.frame) = direct.map (fun r => r.1.frame)
#guard normal.map (fun s => s.scalars.memory) = direct.map (fun r => r.1.scalars.memory)
#guard normal.map (fun s => s.scalars.bindings) = direct.map (fun r => r.1.scalars.bindings)
#guard normal.map (fun s => s.slots) = direct.map (fun r => r.1.slots)
#guard normal.map (fun s => s.work) = direct.map (fun r => r.1.work+4)
def target : ObjectRef := reference pair.1 3
def mutated : Option (NState × Ret) := normal.bind fun s =>
  match CopyCommandMethods.Packet_bump.callFuel 64 s
      [.vectorReference target.vectorSlot,.value (.literal ⟨64,true,false⟩ 8),
       .scalarReference target.scalarSlots[1]!,.scalarReference target.scalarSlots[2]!] with
  | .finished r => some r
  | _ => none
#guard mutated.map (fun r => r.2) = some (.scalar 4)
#guard mutated.map (fun r => r.1.scalars.memory.map (fun c => c.value)) = some [8,3,0,8,4,1]
end GeneratedCommandChecks
'''
            self.check_lean(generated+methods+checks,directory)
            native=Path(directory)/'native.cpp'
            native.write_text('#include "packet.hpp"\n#include <iostream>\nint main(){'
                              'other::Packet p(2,7);const other::Packet q(p);'
                              'std::cout<<q.bump()<<" "<<p.count<<" "<<p.ready<<" "'
                              '<<q.count<<" "<<q.ready<<"\\n";}\n')
            check_compiler()
            binary=Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',str(native),'-o',str(binary)],
                           check=True)
            result=subprocess.run([str(binary)],capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout,'4 3 0 4 1\n')


CHECKS = r'''
namespace CopyCommandsProbe
open Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppClassCopy
open Proofs.CppClassCopyCommands Proofs.CppLoop
def entry : NState := (⟨⟨[⟨i32,1⟩,⟨i32,2⟩],[⟨0,false⟩,⟨1,true⟩],0,0,0⟩,before,
  (List.range before.bindings.length).map (fun i => .vector i)++[.scalar 0,.scalar 1],9,0⟩ : NState).charge 0 0
def profile : Profile := ⟨i32,false,[(i32,false),(i32,true)]⟩
def good : ObjectRef := ⟨2,[5,6]⟩
def malformed : ObjectRef := ⟨2,[5,entry.slots.length+1]⟩
def stateOf : Outcome NStep → Option NState
  | .finished step => some step.state
  | _ => none
def copied := copyClass entry good profile
def commands := stateOf (runCopyFuel 16 entry good profile)
#guard copied.isSome
#guard commands.isSome
#guard commands.map (fun s => s.frame) = copied.map (fun r => r.1.frame)
#guard commands.map (fun s => s.scalars.memory) = copied.map (fun r => r.1.scalars.memory)
#guard commands.map (fun s => s.scalars.bindings) = copied.map (fun r => r.1.scalars.bindings)
#guard commands.map (fun s => s.slots) = copied.map (fun r => r.1.slots)
#guard commands.map (fun s => s.work) = copied.map (fun r => r.1.work+3)
#guard commands.map (fun s => s.scalars.peak) = copied.map (fun r => r.1.scalars.peak)
#guard commands.map (fun s => s.peak) = copied.map (fun r => r.1.peak)
#guard commands.map (fun s => s.frame.read saved) = some (some (-1))
def unguarded := (copyCommand malformed profile).bind fun command => stateOf (runFuel 16 command entry)
#guard (copyClass entry malformed profile).isNone
#guard unguarded.isSome
#guard unguarded.map (fun s => s.scalars.memory.map (fun c => c.value)) = some [1,2,1,1]
#guard runCopyFuel 16 entry malformed profile = .fault
def vectorOnlyProfile : Profile := ⟨i32,false,[]⟩
def vectorOnlySource : ObjectRef := ⟨2,[]⟩
def vectorOnlyCopied := copyClass entry vectorOnlySource vectorOnlyProfile
def vectorOnlyCommands := stateOf (runCopyFuel 16 entry vectorOnlySource vectorOnlyProfile)
#guard vectorOnlyCommands.isSome
#guard vectorOnlyCommands.map (fun s => s.frame) = vectorOnlyCopied.map (fun r => r.1.frame)
#guard vectorOnlyCommands.map (fun s => s.work) = vectorOnlyCopied.map (fun r => r.1.work+1)
#guard vectorOnlyCommands.map (fun s => s.scalars.peak) = vectorOnlyCopied.map (fun r => r.1.scalars.peak+1)
#guard vectorOnlyCommands.map (fun s => s.peak) = vectorOnlyCopied.map (fun r => r.1.peak+1)
end CopyCommandsProbe
'''

if __name__=='__main__':
    disable_network()
    unittest.main()

