"""Same-TU FieldDecl Context receivers, original UF models, mixed types and rejection."""
from pathlib import Path
import copy
import hashlib
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
import context_method_ir
from context_method_ir import emit_context_methods
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from check_public import check_compiler
from offline import disable_network
SOURCE=ROOT/'experiments/verification/data_structure/union_find.hpp'

CHECKS = r'''

namespace ContextMethodReceiverExamples
open Proofs.CppNestedCall Proofs.CppNestedProgram UfMoveCallExamples
example : PrototypeContextMethods.Methods.«UnionFind_root» = Proofs.UnionFindCandidateInstance.UnionFind_root := rfl
example : PrototypeContextMethods.Methods.«UnionFind_same» = Proofs.UnionFindCandidateInstance.UnionFind_same := rfl
example : PrototypeContextMethods.Methods.«UnionFind_size» = Proofs.UnionFindCandidateInstance.UnionFind_size := rfl
example : PrototypeContextMethods.Methods.«UnionFind_unite» = Proofs.UnionFindCandidateInstance.UnionFind_unite := rfl
example : PrototypeContextMethods.Methods.«UnionFind_num_groups» = Proofs.UnionFindCandidateInstance.UnionFind_num_groups := rfl
example : PrototypeContextMethods.«UnionFind_root_arguments» ⟨3,[4,5]⟩ [.value (.literal ty 3)] =
  some [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)] := rfl
#guard (PrototypeContextMethods.«UnionFind_root_arguments» ⟨3,[]⟩ [.value (.literal ty 3)]).isNone
#guard (PrototypeContextMethods.«UnionFind_root_arguments» ⟨3,[4,5]⟩ []).isNone
#guard (match PrototypeContextMethods.«UnionFind_root_callFuel» 128 moved.1 ⟨3,[4,5]⟩ [.value (.literal ty 3)] with
 | .finished (out,result) => result == .scalar 0 && (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,0]
 | _ => false)
#guard (match PrototypeContextMethods.«UnionFind_num_groups_callFuel» 16 moved.1 ⟨0,[1,2]⟩ [] with
 | .finished (_,result) => result == .scalar 1
 | _ => false)

#guard PrototypeContextMethods.fieldNames == ["_ps","_num_groups","_n"]
example (fuel : Nat) (caller : Proofs.CppMoveContext.Context) :
  PrototypeContextMethods.«UnionFind_root_callFuel» fuel caller ⟨3,[4,5]⟩ [.value (.literal ty 3)] =
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_root fuel caller ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)] :=
  PrototypeContextMethods.«UnionFind_root_call_of_arguments» fuel caller ⟨3,[4,5]⟩ [.value (.literal ty 3)] _ rfl
end ContextMethodReceiverExamples
'''

MIXED_SOURCE = r'''

#include <vector>
namespace renamed {struct Packet {
  std::vector<long long> data;
  unsigned int count;
  long stamp;
  bool marked;
  unsigned int read_count(){return count;}
  long read_stamp(){return stamp;}
  bool read_marked(){return marked;}
  long long touch(long long value){data[0]=value;count=count+1u;marked=true;return data[0];}
};}
'''

MIXED_CHECKS = r'''

namespace GeneratedMixedContextExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram
abbrev vTy : Proofs.CppScalar.Ty := ⟨64,true,false⟩
abbrev uTy : Proofs.CppScalar.Ty := ⟨32,false,false⟩
abbrev bTy : Proofs.CppScalar.Ty := ⟨1,false,true⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit vTy
def initial : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩],
  [some ⟨⟨0,[7],1,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩]⟩,
  ⟨[⟨uTy,2^32-1⟩,⟨vTy,-(2^63)⟩,⟨bTy,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.scalar 2],0,0⟩
#guard MixedContextMethods.fieldNames == ["data","count","stamp","marked"]
#guard (match MixedContextMethods.«Packet_read_count_callFuel» 16 initial ⟨0,[1,2,3]⟩ [] with
  | .finished (_,r) => r == .scalar (2^32-1) | _ => false)
#guard (match MixedContextMethods.«Packet_read_stamp_callFuel» 16 initial ⟨0,[1,2,3]⟩ [] with
  | .finished (_,r) => r == .scalar (-(2^63)) | _ => false)
#guard (match MixedContextMethods.«Packet_read_marked_callFuel» 16 initial ⟨0,[1,2,3]⟩ [] with
  | .finished (_,r) => r == .scalar 0 | _ => false)
#guard (match MixedContextMethods.«Packet_touch_callFuel» 32 initial ⟨0,[1,2,3]⟩ [.value (.literal vTy 5)] with
  | .finished (out,r) => r == .scalar 5 && out.scalars.memory.map (·.value) == [0,-(2^63),1] &&
      (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [5]
  | _ => false)
end GeneratedMixedContextExamples
'''

NATIVE = r'''

#include <cassert>
#include <limits>
int main(){
  renamed::Packet value{{7},std::numeric_limits<unsigned int>::max(),std::numeric_limits<long>::min(),false};
  assert(value.read_count()==std::numeric_limits<unsigned int>::max());
  assert(value.read_stamp()==std::numeric_limits<long>::min() && !value.read_marked());
  assert(value.touch(5)==5 && value.count==0 && value.marked && value.data[0]==5);
  assert(value.stamp==std::numeric_limits<long>::min());
}
'''

class ContextMethodIRTests(unittest.TestCase):
    def check_lean(self,text):
        with tempfile.TemporaryDirectory(prefix='context-method-ir-') as directory:
            proof=Path(directory)/'check.lean';proof.write_text(text)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_original_fields_all_models_and_generated_call(self):
        original=SOURCE.read_bytes()
        generated=emit_context_methods(SOURCE,'cp::UnionFind','PrototypeContextMethods')
        self.assertIn(hashlib.sha256(original).hexdigest(),generated)
        self.check_lean('import Proofs.UfClassCopyBridge\nimport Proofs.UfFieldsSame\n'
            'import Proofs.UfFieldsSize\nimport Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n'+generated+UF_CHECKS+CHECKS)
        self.assertEqual(SOURCE.read_bytes(),original)

    def test_mixed_scalar_modes_types_and_native(self):
        with tempfile.TemporaryDirectory(prefix='context-method-mixed-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(MIXED_SOURCE)
            generated=emit_context_methods(source,'renamed::Packet','MixedContextMethods')
            self.check_lean(generated+MIXED_CHECKS)
            check_compiler()
            cpp=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            cpp.write_text(MIXED_SOURCE+NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

    def test_mutable_reference_can_alias_receiver_field(self):
        source_text="#include <vector>\nstruct Alias {std::vector<int> data;int count;int inspect(int& value){value=9;return count;}int view()const{return count;}};\n"
        with tempfile.TemporaryDirectory(prefix='context-method-alias-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(source_text)
            generated=emit_context_methods(source,'Alias','AliasContextMethods')
            checks=r"""
namespace ReceiverAliasExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram
abbrev ty : Proofs.CppScalar.Ty := ⟨32,true,false⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit ty
def initial : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩],
  [some ⟨⟨0,[7],1,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩]⟩,
  ⟨[⟨ty,4⟩],[⟨0,true⟩],0,0,0⟩,[.vector 0,.scalar 0],0,0⟩
example : AliasContextMethods.«Alias_inspect_arguments» ⟨0,[1]⟩ [.scalarReference 1] =
  some [.vectorReference 0,.scalarReference 1,.scalarReference 1] := rfl
#guard (match AliasContextMethods.«Alias_inspect_callFuel» 16 initial ⟨0,[1]⟩ [.scalarReference 1] with
  | .finished (out,result) => result == .scalar 9 && out.scalars.memory.map (·.value) == [9]
  | _ => false)
#guard (match AliasContextMethods.«Alias_view_callFuel» 16 initial ⟨0,[1]⟩ [] with
  | .finished (out,result) => result == .scalar 4 && out.scalars.memory.map (·.value) == [4]
  | _ => false)
end ReceiverAliasExamples
"""
            self.check_lean(generated+checks)
            check_compiler()
            cpp=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            cpp.write_text(source_text+'#include <cassert>\nint main(){Alias value{{7},4};assert(value.view()==4);assert(value.inspect(value.count)==9);assert(value.count==9&&value.view()==9&&value.data[0]==7); }\n')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

    def test_unsupported_source_profiles_and_bodies(self):
        cases={
            'resize':'struct Case {std::vector<int> data;int count;int grow(){data.reserve(8);return count;}};',
            'unit':'struct Case {std::vector<int> data;int count;void update(){count=1;}};',
            'defaults':'struct Case {std::vector<int> data;int count;int get(int delta=1){return count+delta;}};',
            'static':'struct Case {std::vector<int> data;int count;static int get(){return 1;}};',
        }
        with tempfile.TemporaryDirectory(prefix='context-method-reject-') as directory:
            for name,body in cases.items():
                with self.subTest(name=name):
                    source=Path(directory)/(name+'.hpp');source.write_text('#include <vector>\n'+body+'\n')
                    with self.assertRaises(ValueError):emit_context_methods(source,'Case','RejectedContext')

    def test_field_identity_mode_and_permission_mutations(self):
        original_bindings=context_method_ir.bindings_from_audit
        for mutation in ['reference','permission','type']:
            def changed(*args,**kwargs):
                result=copy.deepcopy(original_bindings(*args,**kwargs))
                if mutation=='reference':result['functions'][0]['parameters'][1]['reference']=False
                elif mutation=='permission':result['functions'][0]['parameters'][0]['writable']=False
                else:result['functions'][0]['parameters'][1]['element']['width']=64
                return result
            with self.subTest(mutation=mutation),patch('context_method_ir.bindings_from_audit',side_effect=changed):
                with self.assertRaises(ValueError):emit_context_methods(SOURCE,'cp::UnionFind','RejectedMutation')
        original_audit=context_method_ir.audit_copy_record
        def alien(*args,**kwargs):
            result=copy.deepcopy(original_audit(*args,**kwargs));result['fields'][1]['field_id']='alien-field';return result
        with patch('context_method_ir.audit_copy_record',side_effect=alien):
            with self.assertRaises(ValueError):emit_context_methods(SOURCE,'cp::UnionFind','RejectedIdentity')

    def test_namespace_and_source_change_rejections(self):
        with self.assertRaises(ValueError):emit_context_methods(SOURCE,'cp::UnionFind','Bad;namespace')
        original_probes=context_method_ir.verify_type_probes
        with tempfile.TemporaryDirectory(prefix='context-method-source-change-') as directory:
            source=Path(directory)/'source.hpp';source.write_bytes(SOURCE.read_bytes())
            def changed(*args,**kwargs):
                result=original_probes(*args,**kwargs)
                source.write_text(source.read_text()+'\n// source changed after lowering\n')
                return result
            with patch('context_method_ir.verify_type_probes',side_effect=changed):
                with self.assertRaisesRegex(ValueError,'source changed'):emit_context_methods(source,'cp::UnionFind','RejectedChange')

            source.write_bytes(SOURCE.read_bytes())
            original_lower=context_method_ir.lower_context_methods
            def changed_after_lower(*args,**kwargs):
                result=original_lower(*args,**kwargs)
                source.write_text(source.read_text()+'\n// changed after completed lowering\n')
                return result
            with patch('context_method_ir.lower_context_methods',side_effect=changed_after_lower):
                with self.assertRaisesRegex(ValueError,'source changed'):emit_context_methods(source,'cp::UnionFind','RejectedLateChange')

if __name__=='__main__':
    disable_network()
    unittest.main()
