"""Audited C++ parameter schema generation and typed runtime vector bindings."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from vector_bindings import lower_bindings,emit_lean,merge_type_probes,verify_type_probes
from test_scalar_ir import lean_environment
from offline import disable_network
from check_public import FLAGS,check_compiler


class BindingTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode==0,succeeds,result.stdout+result.stderr)

    def test_actual_parameters_rename_and_const_mutation(self):
        source_text='''#include <vector>
namespace cp {
unsigned long f(const std::vector<int>& v,long long& x,const unsigned int y){return v.size()+y;}
unsigned long g(std::vector<unsigned long>& v,int x){return v.size()+x;}
}'''
        with tempfile.TemporaryDirectory(prefix='vector-binding-schema-') as directory:
            scratch=Path(directory);source=scratch/'source.cpp';source.write_text(source_text)
            ir=lower_bindings(source)
            self.assertEqual(ir['coverage'],'parameter_bindings_only')
            self.assertEqual(ir['functions'][0]['parameters'][0],
                {'kind':'vector','element':{'width':32,'signed':True,'boolean':False},'writable':False})
            self.lean(scratch,emit_lean(ir)+'''\nexample : VectorBindingInstances.f =
 [.vector ⟨32,true,false⟩ false,.scalar ⟨64,true,false⟩ true true,.scalar ⟨32,false,false⟩ false false] := rfl
example : VectorBindingInstances.g = [.vector ⟨64,false,false⟩ true,.scalar ⟨32,true,false⟩ false true] := rfl
''')
            source.write_text(source_text.replace(' f(',' renamed(').replace(' v',' values').replace('v.','values.'))
            renamed=lower_bindings(source);expected=copy.deepcopy(ir);expected['functions'][0]['name']='renamed'
            self.assertEqual(renamed,expected)
            source.write_text(source_text.replace('const std::vector<int>','std::vector<int>'))
            changed=lower_bindings(source)
            self.lean(scratch,emit_lean(changed)+'''\nexample : VectorBindingInstances.f =
 [.vector ⟨32,true,false⟩ false,.scalar ⟨64,true,false⟩ true true,.scalar ⟨32,false,false⟩ false false] := rfl
''',False)
            doubling=lower_bindings(ROOT/'library/array/doubling.hpp')
            self.assertEqual(doubling,json.loads((ROOT/'experiments/verification/array/doubling_bindings_ir.json').read_text()))
            self.assertEqual(emit_lean(doubling,'DoublingBindingInstance'),
                (ROOT/'Proofs/Generated/DoublingBindings.lean').read_text())
            self.lean(scratch,emit_lean(doubling)+'''\nexample : VectorBindingInstances.doubling =
 [.vector ⟨32,true,false⟩ false,.scalar ⟨64,false,false⟩ false true] := rfl
''')

    def test_template_instances_share_one_identity_probe(self):
        guard='\n#if defined(std)\n#error no macros\n#endif\n'
        probe=lambda entity,ty:f'{guard}static_assert(__is_same(decltype({entity}),{ty}),"canonical");\n'
        merged=merge_type_probes([(5,probe('v','const ::std::vector<long long> &')),(5,probe('((cs))','::std::vector<long long> &')),
            (5,probe('v','const ::std::vector<int> &')),(5,probe('v','const ::std::vector<int> &')),(9,'other'),(9,'other')])
        self.assertEqual(merged,[(5,f'{guard}static_assert(__is_same(decltype(v),const ::std::vector<long long> &) || '
            '__is_same(decltype(v),const ::std::vector<int> &),"canonical");\n'),
            (5,probe('((cs))','::std::vector<long long> &')),(9,'other')])
        text=('#include <vector>\nnamespace cp {template<class T> struct S {int f(const std::vector<T>& v){return 0;}};\n'
              'template struct S<long long>;template struct S<int>;template struct S<short>;}\n')
        with tempfile.TemporaryDirectory(prefix='vector-binding-template-') as directory:
            source=Path(directory)/'source.cpp';source.write_text(text)
            offset=text.index('{return')+1
            both=[(offset,probe('v',f'const ::std::vector<{t}> &')) for t in ('long long','int','short')]
            verify_type_probes(source,both)
            with self.assertRaisesRegex(ValueError,'identity probe failed'):
                verify_type_probes(source,both[:2])

    def test_lexical_names_cannot_fake_parameter_identity(self):
        text='#include <vector>\nnamespace fake {template<class T>struct vector{};}\nnamespace cp {namespace std=fake;int f(const std::vector<int>& v){return 0;}}\nint actual(::std::vector<int>& v){return v[0];}'
        with tempfile.TemporaryDirectory(prefix='vector-binding-identity-') as directory:
            scratch=Path(directory);source=scratch/'source.cpp';source.write_text(text)
            with self.assertRaises(ValueError):lower_bindings(source)
            source.write_text('#include <vector>\n#define __is_same(...) true\nnamespace cp {int f(std::vector<int>& v){return v[0];}}')
            with self.assertRaises(ValueError):lower_bindings(source)

    def test_typed_owners_permissions_stale_refs_and_resources(self):
        checks='''import Proofs.CppVectorBindings
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorBindings
 def i32 : Ty := ⟨32,true,false⟩
 def u64 : Ty := ⟨64,false,false⟩
 def initial : Frame := ⟨⟨[some ⟨0,[3,8],2,100,0⟩],0,0,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],0⟩
#guard initial.elementRef 0 i32 0 == some ⟨0,i32,true,⟨0,0,0⟩⟩
#guard initial.elementRef 1 i32 0 == some ⟨1,i32,false,⟨0,0,0⟩⟩
#guard initial.resolve 0 u64 == none
#guard initial.elementRef 0 i32 (-1) == none
#guard initial.elementRef 0 i32 2 == none
#guard initial.write ⟨1,i32,true,⟨0,0,0⟩⟩ 5 == none
#guard initial.write ⟨0,i32,false,⟨0,0,0⟩⟩ 5 == none
#guard initial.read ⟨0,i32,true,⟨1,0,0⟩⟩ == none
#guard initial.write ⟨0,i32,true,⟨1,0,0⟩⟩ 5 == none
#guard initial.reserve 1 i32 7 == none
#guard initial.appendReserved 1 i32 7 == none
#guard initial.write ⟨0,i32,true,⟨0,0,0⟩⟩ 2147483648 == none
#guard initial.read ⟨1,i32,false,⟨0,0,0⟩⟩ == some
 (⟨⟨[some ⟨0,[3,8],2,100,0⟩],1,1,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],4⟩,(3:Int))
#guard initial.write ⟨0,i32,true,⟨0,0,0⟩⟩ 5 == some
 ⟨⟨[some ⟨0,[5,8],2,100,0⟩],1,1,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],4⟩
#guard initial.reserve 0 i32 5 == some
 ⟨⟨[some ⟨0,[3,8],5,100,1⟩],3,6,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],9⟩
 def grown : Frame := ⟨⟨[some ⟨0,[3,8],5,100,1⟩],3,6,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],9⟩
#guard grown.appendReserved 0 i32 11 == some
 ⟨⟨[some ⟨0,[3,8,11],5,100,1⟩],5,6,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩,⟨0,i32,false⟩],9⟩
#guard grown.read ⟨0,i32,true,⟨0,0,0⟩⟩ == none
#guard grown.write ⟨0,i32,true,⟨0,0,0⟩⟩ 5 == none
#guard grown.elementRef 0 i32 0 == some ⟨0,i32,true,⟨0,1,0⟩⟩
 def readonlyObject : Frame := ⟨initial.store,[⟨i32,false⟩],[],0⟩
#guard readonlyObject.bind 0 i32 true == none
#guard readonlyObject.bind 0 i32 false == some ⟨initial.store,[⟨i32,false⟩],[⟨0,i32,false⟩],1⟩
#guard (⟨initial.store,[⟨i32,false⟩],[⟨0,i32,true⟩],0⟩ : Frame).resolve 0 i32 == none
#guard (⟨initial.store,[⟨u64,true⟩],[⟨0,i32,true⟩],0⟩ : Frame).resolve 0 i32 == none
#guard (⟨⟨[none],0,0,0⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],0⟩ : Frame).resolve 0 i32 == none
 def empty : Frame := ⟨⟨[],0,0,0⟩,[],[],0⟩
 def constructed : Frame := ⟨⟨[some ⟨0,[3,3],2,100,0⟩],3,4,0⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],5⟩
#guard empty.construct i32 true 100 2 3 == some (constructed,0)
#guard constructed.size 0 i32 == some
 (⟨⟨[some ⟨0,[3,3],2,100,0⟩],4,4,0⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],6⟩,(2:Int))
 def pair : Frame := ⟨⟨[some ⟨0,[3,3],2,100,0⟩,some ⟨1,[],0,100,0⟩],4,5,0⟩,
 [⟨i32,true⟩,⟨i32,true⟩],[⟨0,i32,true⟩,⟨1,i32,true⟩],7⟩
#guard constructed.construct i32 true 100 0 0 == some (pair,1)
#guard pair.assign 1 0 i32 ⟨0,0,0,2⟩ == some
 ⟨⟨[some ⟨0,[3,3],2,100,0⟩,some ⟨1,[3,3],2,100,1⟩],7,7,0⟩,
 [⟨i32,true⟩,⟨i32,true⟩],[⟨0,i32,true⟩,⟨1,i32,true⟩],10⟩
#guard pair.assign 1 0 i32 ⟨1,0,0,0⟩ == none
#guard pair.assign 0 0 i32 ⟨0,0,0,2⟩ == none
#guard empty.construct i32 true 100 2 2147483648 == none
#guard empty.construct i32 true 1 2 3 == none
#guard empty.construct ⟨1,false,true⟩ true 100 2 1 == none
#guard empty.construct i32 true 18446744073709551615 0 0 == none
#guard (⟨initial.store,[],[],0⟩ : Frame).construct i32 true 100 2 3 == none
#guard sizeLimit i32 == 2305843009213693951
#guard sizeLimit u64 == 1152921504606846975
'''
        with tempfile.TemporaryDirectory(prefix='vector-binding-runtime-') as directory:
            scratch=Path(directory);self.lean(scratch,checks)
            source=scratch/'native.cpp'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n'
                '#include <cassert>\n#include <vector>\nint main(){\n'+
                ''.join(f'assert(std::vector<{ty}>().max_size()=={limit}ULL);\n' for ty,limit in
                    [('int',2305843009213693951),('unsigned int',2305843009213693951),
                     ('long',1152921504606846975),('unsigned long',1152921504606846975),
                     ('long long',1152921504606846975),('unsigned long long',1152921504606846975)])+
                'std::vector<int> v{3,8}; const std::vector<int>& view=v; v[0]=17;'
                'assert(view[0]==17);v.reserve(5);assert(view[0]==17);assert(v.capacity()==5);}')
            check_compiler();executable=scratch/'native'
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT),
                            str(source),'-o',str(executable)],check=True,cwd=ROOT)
            subprocess.run([str(executable)],check=True)
        print('typed vector frame: 37 runtime checks, six native max_size profiles and const alias')

if __name__=='__main__':
    disable_network();unittest.main()
