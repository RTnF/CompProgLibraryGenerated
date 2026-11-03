"""Same-TU external class receivers through actual generated method calls."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
import class_call_ir as calls
from class_copy_layout import emit_class_layout
from test_scalar_ir import lean_environment
from test_union_find_original_api import SOURCE
from test_union_find_receiver_trace import OPS, EXPECTED
from test_class_copy_layout import PACKET
from offline import disable_network


class ClassCallerTests(unittest.TestCase):
    def check_lean(self,text,directory):
        imports=[line for line in text.splitlines() if line.startswith('import ')]
        body=[line for line in text.splitlines() if not line.startswith('import ')]
        proof=Path(directory)/'checks.lean';proof.write_text('\n'.join(imports+body)+'\n')
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def native(self,source,main,directory):
        path=Path(directory)/'native.cpp';binary=Path(directory)/'native'
        path.write_text(f'#include "{source}"\n#include <iostream>\nint main(){{{main}}}')
        subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(path),'-o',str(binary)],check=True)
        return subprocess.run([str(binary)],check=True,capture_output=True,text=True).stdout

    def test_all_five_methods_external_receiver_and_early_return(self):
        with tempfile.TemporaryDirectory(prefix='class-caller-uf-') as directory:
            source=Path(directory)/'source.hpp'
            declarations=''.join(f'int r{i}=u.{name}({",".join(map(str,args))});' for i,(name,args) in enumerate(OPS))
            answer='+'.join(f'{i+1}*r{i}' for i in range(len(OPS)))
            expected=sum((i+1)*v for i,v in enumerate(EXPECTED))
            source.write_text(SOURCE.read_text()+f'\nnamespace wrapper {{int trace(cp::UnionFind &u){{{declarations}return {answer};}}'+
                'int loop(cp::UnionFind &u,int n){for(int i=0;i<n;++i){if(i==2) break;u.unite(i,i);}int g=u.num_groups();return g;}}\n')
            generated=calls.emit_class_callers(source,'cp::UnionFind','GeneratedCalls')
            constructors=emit_class_layout(source,'cp::UnionFind','Constructors')
            checks=r'''
import Proofs.Generated.UnionFindCandidate
example : GeneratedCalls.Methods.UnionFind_unite = Proofs.UnionFindCandidateInstance.UnionFind_unite := rfl
example : GeneratedCalls.Methods.UnionFind_same = Proofs.UnionFindCandidateInstance.UnionFind_same := rfl
example : GeneratedCalls.Methods.UnionFind_root = Proofs.UnionFindCandidateInstance.UnionFind_root := rfl
example : GeneratedCalls.Methods.UnionFind_size = Proofs.UnionFindCandidateInstance.UnionFind_size := rfl
example : GeneratedCalls.Methods.UnionFind_num_groups = Proofs.UnionFindCandidateInstance.UnionFind_num_groups := rfl
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
def i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def constructed : Option (NState × ObjectRef) :=
  match Constructors.UnionFind_construct1_exportFuel 16 empty [.value (.literal i32 4)] with
  | .finished pair => some pair
  | _ => none
#guard constructed.isSome
def executed : Option (NState × Ret) := do
  let (s,obj) ← constructed
  let args ← GeneratedCalls.wrapper_trace_arguments obj
  match GeneratedCalls.wrapper_trace.callFuel 2048 s args with
  | .finished pair => some pair
  | _ => none
#guard (match executed with
  | some (s,.scalar value) => value == EXPECTED &&
      s.scalars.memory == [⟨i32,1⟩,⟨i32,4⟩] &&
      (s.frame.state.storage.lookup 0).map (·.items) == some ([-4,0,0,0].map Proofs.CppNestedVectorStore.Value.integer) &&
      s.slots.length == 3 && s.scope == 0
  | _ => false)
#guard (GeneratedCalls.wrapper_trace_arguments ⟨0,[1]⟩).isNone
#guard GeneratedCalls.wrapper_trace.callFuel 0 empty [] == .fault
#guard (match constructed with
  | some (s,obj) => match GeneratedCalls.wrapper_loop_arguments obj (.value (.literal i32 4)) with
    | some args => match GeneratedCalls.wrapper_loop.callFuel 2048 s args with
      | .finished (out,.scalar value) => value == 4 && out.slots == s.slots &&
          out.scalars.memory == s.scalars.memory && out.frame.state.storage == s.frame.state.storage
      | _ => false
    | _ => false
  | _ => false)
'''.replace('value == EXPECTED',f'value == ({expected} : Int)')
            self.check_lean(generated+constructors+checks,directory)
            self.assertEqual(self.native(source,'cp::UnionFind u(4);std::cout << wrapper::trace(u) << " " << u.num_groups(); cp::UnionFind v(4);std::cout << " " << wrapper::loop(v,4);',directory),f'{expected} 1 4')

    def test_const_mutable_fields_and_two_receiver_aliases(self):
        with tempfile.TemporaryDirectory(prefix='class-caller-const-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(PACKET+'''namespace wrapper {
unsigned int twice(const other::Packet &a,const other::Packet &b) {
  unsigned int x=a.bump(); unsigned int y=b.bump(); return x*10+y;
}
}''')
            generated=calls.emit_class_callers(source,'other::Packet','ConstCalls')
            constructors=emit_class_layout(source,'other::Packet','ConstConstructors')
            checks=r'''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def executed : Option (NState × Ret) := do
  let (s,obj) ← match ConstConstructors.Packet_construct0_exportFuel 64 empty
      [.value (.literal ⟨64,false,false⟩ 2),.value (.literal ⟨64,true,false⟩ 7)] with
    | .finished pair => some pair | _ => none
  let args ← ConstCalls.wrapper_twice_arguments obj obj
  match ConstCalls.wrapper_twice.callFuel 256 s args with
  | .finished pair => some pair | _ => none
#guard (match executed with
  | some (s,.scalar value) => value == 45 &&
      s.scalars.memory.map (·.value) == ([8,5,1] : List Int) && s.slots.length == 4
  | _ => false)
'''
            self.check_lean(generated+constructors+checks,directory)
            self.assertEqual(self.native(source,'const other::Packet p(2,7);std::cout << wrapper::twice(p,p);',directory),'45')

    def test_method_identity_mixed_dump_and_condition_rejected(self):
        with tempfile.TemporaryDirectory(prefix='class-caller-reject-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(PACKET+'unsigned int use(const other::Packet &a){return a.bump();}')
            real=calls.translation_unit
            def mixed(*args,**kwargs):
                result=real(*args,**kwargs)
                kwargs['class_callers'][0]['_copy_translation_unit']='other-dump'
                return result
            with mock.patch.object(calls,'translation_unit',side_effect=mixed):
                with self.assertRaisesRegex(ValueError,'translation unit'):
                    calls.lower_class_callers(source,'other::Packet')
            def wrong_method(*args,**kwargs):
                result=real(*args,**kwargs)
                for node in calls.walk(kwargs['class_callers'][0]):
                    if node.get('kind')=='MemberExpr':node['referencedMemberDecl']='foreign-method'
                return result
            with mock.patch.object(calls,'translation_unit',side_effect=wrong_method):
                with self.assertRaisesRegex(ValueError,'method declaration'):
                    calls.lower_class_callers(source,'other::Packet')
            source.write_text(PACKET+'unsigned int use(const other::Packet &a){if(a.bump()) return 1; return 0;}')
            with self.assertRaisesRegex(ValueError,'outside conditions'):
                calls.lower_class_callers(source,'other::Packet')

    def test_same_arity_overloads_and_field_name_shadowing(self):
        with tempfile.TemporaryDirectory(prefix='class-caller-overloads-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('''#include <vector>
namespace other {
struct Meter {
  std::vector<int> values;
  int count;
  Meter():values(2,0),count(0){}
  int bump(int count){this->count+=count;return this->count;}
  int bump(unsigned int count){this->count+=static_cast<int>(count)*2;return this->count;}
};
}
int use(other::Meter &m){int a=m.bump(1);int b=m.bump(1u);return a*10+b;}
int loop(other::Meter &m){int i=0;for(;i<3;i=m.bump(1)){}return i;}
''')
            generated=calls.emit_class_callers(source,'other::Meter','OverloadCalls')
            constructors=emit_class_layout(source,'other::Meter','OverloadConstructors')
            checks=r'''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
#guard (match OverloadConstructors.Meter_construct0_exportFuel 64 empty [] with
  | .finished (s,obj) => match OverloadCalls.use_arguments obj with
    | some args => match OverloadCalls.use.callFuel 256 s args with
      | .finished (out,.scalar value) => value == 13 &&
          out.scalars.memory.map (·.value) == ([3] : List Int)
      | _ => false
    | _ => false
  | _ => false)
'''
            checks+=r"""
#guard (match OverloadConstructors.Meter_construct0_exportFuel 64 empty [] with
  | .finished (s,obj) => match OverloadCalls.loop_arguments obj with
    | some args => match OverloadCalls.loop.callFuel 512 s args with
      | .finished (out,.scalar value) => value == 3 && out.slots == s.slots &&
          out.scalars.memory.map (·.value) == ([3] : List Int)
      | _ => false
    | _ => false
  | _ => false)
"""
            self.check_lean(generated+constructors+checks,directory)
            self.assertEqual(self.native(source,'other::Meter m;std::cout << use(m);other::Meter n;std::cout << " " << loop(n);',directory),'13 3')

if __name__=='__main__':
    disable_network()
    unittest.main()
