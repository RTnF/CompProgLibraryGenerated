"""Actual same-TU vector callee IDs, pristine bodies and refusal tests."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from vector_stl import audit_vector_operations
import vector_stl
from offline import disable_network

class VectorCalleeTests(unittest.TestCase):
    def audit(self,text):
        with tempfile.TemporaryDirectory(prefix='vector-callees-') as directory:
            source=Path(directory)/'source.cpp';source.write_text(text)
            return audit_vector_operations(source)

    def test_actual_ids_rename_nested_and_range_methods(self):
        text='''#include <vector>
namespace cp {
int f(std::vector<int>& v,const std::vector<int>& source){
 v.reserve(8);v.emplace_back(2);v.push_back(3);
 v.assign(source.begin(),source.end());return v[0]+v.size();}
int nested(std::vector<std::vector<int>>& v){v[0].reserve(8);return v[0][0];}
}'''
        result=self.audit(text)
        self.assertEqual(result['coverage'],'callee_identity_only')
        operations=[r['operation'] for r in result['operations']]
        self.assertEqual(operations,['reserve','emplace_back','push_back','assign','begin','end',
                                     'operator[]','size','reserve','operator[]','operator[]','operator[]'])
        self.assertTrue(all(r['callee_id'] and r['pattern_id'] for r in result['operations']))
        renamed=self.audit(text.replace('nested','other').replace('int f(','int changed(')
                           .replace(' v',' values').replace('v.','values.').replace('v[','values['))
        self.assertEqual([(r['operation'],r['element']) for r in result['operations']],
                         [(r['operation'],r['element']) for r in renamed['operations']])

    def test_actual_doubling_calls_and_verified_assert_arguments(self):
        result=audit_vector_operations(ROOT/'library/doubling.hpp')
        self.assertEqual(result['coverage'],'callee_identity_only')
        self.assertEqual([r['operation'] for r in result['operations']],
            ['size','size','operator[]','operator[]','assign','operator[]','begin','end',
             'reserve','operator[]','emplace_back','operator[]','operator[]','operator[]',
             'operator[]','operator[]'])
        self.assertIn('std::vector<int>',[r['element'] for r in result['operations']])
        text='#include <vector>\n#include <cassert>\nnamespace cp {int f(std::vector<int>& v){assert(v.size()>0);return v[0];}}'
        self.assertEqual([r['operation'] for r in self.audit(text)['operations']],['size','operator[]'])

    def test_incompatible_abi_is_refused_before_ast_loading(self):
        command=vector_stl.clang_command()
        with patch.object(vector_stl,'clang_command',return_value=command+['-m32']):
            with self.assertRaisesRegex(ValueError,'unsupported vector ABI'):
                self.audit('#include <vector>\nnamespace cp {int f(std::vector<int>& v){return v[0];}}')

    def test_namesakes_specializations_proxy_allocator_macros_and_changes(self):
        sources=[
          '#include <vector>\nstruct Other{int size(){return 1;}};namespace cp {int f(Other& v){return v.size();}}',
          '#include <vector>\nnamespace std {template<> vector<int>::reference vector<int>::operator[](size_type) noexcept {static int x=0;return x;}} namespace cp {int f(std::vector<int>& v){return v[0];}}',
          '#include <vector>\ntemplate<> std::vector<int>::reference std::vector<int>::operator[](size_type) noexcept {static int x=0;return x;} namespace cp {int f(std::vector<int>& v){return v[0];}}',
          '#include <vector>\ntemplate<> template<> std::vector<int>::reference std::vector<int>::emplace_back<int>(int&&){static int x=0;return x;} namespace cp {int f(std::vector<int>& v){v.emplace_back(2);return 1;}}',
          '#include <vector>\ntemplate<> class std::vector<int>{public:int size() const{return 5;}};namespace cp {int f(std::vector<int>& v){return v.size();}}',
          '#include <vector>\nnamespace cp {bool f(std::vector<bool>& v){return v[0];}}',
          '#include <vector>\ntemplate<class T>struct A:std::allocator<T>{using value_type=T;template<class U>struct rebind{using other=A<U>;};};namespace cp {int f(std::vector<int,A<int>>& v){return v.size();}}',
          '#include <vector>\nstruct X{};namespace cp {int f(std::vector<X>& v){return v.size();}}',
          '#include <vector>\nnamespace cp {int f(std::vector<int>& v){v.clear();return 1;}}',
          '#include <vector>\n#define ACCESS(v) v[0]\nnamespace cp {int f(std::vector<int>& v){return ACCESS(v);}}',
          '#include <bits/c++config.h>\n#undef __N\n#define __N(msgid) "tampered"\n#include <vector>\nnamespace cp {int f(std::vector<int>& v){v.reserve(7);return 0;}}',
        ]
        for text in sources:
            with self.subTest(source=text):
                with self.assertRaises(ValueError):self.audit(text)
        with tempfile.TemporaryDirectory(prefix='vector-header-origin-') as directory:
            root=Path(directory)
            (root/'dependency.hpp').write_text('#include <vector>\nnamespace std {template<> vector<int>::reference vector<int>::operator[](size_type) noexcept {static int x=0;return x;}}')
            source=root/'main.cpp';source.write_text('#include "dependency.hpp"\nnamespace cp {int f(std::vector<int>& v){return v[0];}}')
            with self.assertRaises(ValueError):audit_vector_operations(source)

if __name__=='__main__':
    disable_network();unittest.main()
