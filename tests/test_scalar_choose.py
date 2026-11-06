"""Pinned std::min/max copied values; reference and evaluation boundaries."""
import copy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools'), str(ROOT/'tests')]
from nested_ir import lower_source, emit_lean
from scalar_choose import lower_scalar_choices
import vector_stl
from offline import disable_network
import test_scalar_class_delegation as helpers

PREFIX = '#include <algorithm>\n#include <vector>\n'
SOURCE = PREFIX+'''namespace cp {
long long largest(long long a,long long b){long long r=std::max(a,b);return r;}
long long smallest(long long a,long long b){long long r=std::min(a,b);return r;}
unsigned long long largest_u(unsigned long long a,unsigned long long b){auto r=std::max(a,b);return r;}
unsigned long long smallest_u(unsigned long long a,unsigned long long b){auto r=std::min(a,b);return r;}
int largest_i(int a,int b){using std::max;int r=max(a,b);return r;}
unsigned int smallest_ui(unsigned int a,unsigned int b){auto r=std::min(a,b);return r;}
long long snapshot(long long &a,const long long &b){long long r=std::max(a,b);a=17;return r;}
}
'''


class ScalarChoiceTests(unittest.TestCase):
    def test_values_unsigned_and_alias_snapshot(self):
        with tempfile.TemporaryDirectory(prefix='scalar-choice-') as directory:
            directory = Path(directory)
            source = directory/'source.hpp'
            source.write_text(SOURCE)
            ir = lower_source(source)
            self.assertEqual(ir['callees'], [])
            proof = emit_lean(ir, 'ScalarChoices')+(ROOT/'tests/lean/scalar_choose_values.lean').read_text()
            roots = ['ScalarChoiceAudit.'+name for name in
                     ('signed_max','signed_min','unsigned_max','unsigned_min',
                      'signed32_max','unsigned32_min','snapshot_alias')]
            helpers.ScalarDelegationTests().kernel(directory,'ScalarChoiceCheck',roots,proof)
            driver = directory/'native.cpp'
            driver.write_text('''#include "source.hpp"
#include <iostream>
#include <limits>
int main(){
 long long s[]={std::numeric_limits<long long>::min(),-1,0,std::numeric_limits<long long>::max()};
 for(auto a:s)for(auto b:s)std::cout<<cp::largest(a,b)<<" "<<cp::smallest(a,b)<<"\\n";
 unsigned long long u[]={0,1,std::numeric_limits<unsigned long long>::max()};
 for(auto a:u)for(auto b:u)std::cout<<cp::largest_u(a,b)<<" "<<cp::smallest_u(a,b)<<"\\n";
 int si[]={std::numeric_limits<int>::min(),-1,0,std::numeric_limits<int>::max()};
 for(auto a:si)for(auto b:si)std::cout<<cp::largest_i(a,b)<<"\\n";
 unsigned int ui[]={0,1,std::numeric_limits<unsigned int>::max()};
 for(auto a:ui)for(auto b:ui)std::cout<<cp::smallest_ui(a,b)<<"\\n";
 long long value=4;auto out=cp::snapshot(value,value);std::cout<<out<<" "<<value<<"\\n";
}
''')
            executable = directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(driver),'-o',str(executable)], check=True)
            ran = subprocess.run([str(executable)], capture_output=True, text=True, check=True)
            signed = [-(1<<63),-1,0,(1<<63)-1]
            unsigned = [0,1,(1<<64)-1]
            expected = [f'{max(a,b)} {min(a,b)}' for values in (signed,unsigned) for a in values for b in values]
            signed32 = [-(1<<31),-1,0,(1<<31)-1]
            unsigned32 = [0,1,(1<<32)-1]
            expected += [str(max(a,b)) for a in signed32 for b in signed32]
            expected += [str(min(a,b)) for a in unsigned32 for b in unsigned32]
            self.assertEqual(ran.stdout, '\n'.join([*expected,'4 17'])+'\n')

    def test_reference_effects_short_circuit_and_loop_are_rejected(self):
        bodies = [
            'const long long &r=std::max(a,b);return r;',
            'long long r=std::max(++a,b);return r;',
            'long long r=std::max((++a,a),b);return r;',
            'long long r=std::max(a+1,b);return r;',
            'bool r=false && std::max(a,b);return r;',
            'while(std::max(a,b)>0){--a;--b;}return a;',
        ]
        with tempfile.TemporaryDirectory(prefix='scalar-choice-reject-') as directory:
            source = Path(directory)/'source.hpp'
            for body in bodies:
                with self.subTest(body=body):
                    source.write_text(PREFIX+'namespace cp {long long f(long long a,long long b){'+body+'}}\n')
                    with self.assertRaises(ValueError):
                        lower_source(source)

    def test_user_namesake_is_not_a_standard_choice(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(PREFIX+'namespace cp {long long max(long long a,long long b){return 99;} '
                              'long long f(long long a,long long b){long long r=max(a,b);return r;}}\n')
            ir = lower_source(source)
            self.assertIn('max', [f['name'] for f in ir['callees']])

    def test_user_standard_specialization_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(PREFIX+'''namespace std {template<> const long long &max<long long>(
const long long &a,const long long &b){return b;}}
namespace cp {long long f(long long a,long long b){long long r=std::max(a,b);return r;}}
''')
            with self.assertRaisesRegex(ValueError, 'user declarations in standard library namespaces'):
                lower_source(source)

    def test_primary_body_and_instance_identity_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(PREFIX+'namespace cp {long long f(long long a,long long b){long long r=std::max(a,b);return r;}}\n')
            functions, roots = vector_stl.translation_unit(source)
            def nodes(node):
                yield node
                for child in node.get('inner', []):
                    yield from nodes(child)
            for alteration in ('body','identity'):
                changed = copy.deepcopy(roots)
                edited = False
                for root in changed:
                    for node in nodes(root):
                        if node.get('kind') != 'FunctionTemplateDecl' or node.get('name') != 'max':
                            continue
                        for function in node.get('inner', []):
                            if function.get('kind') != 'FunctionDecl':
                                continue
                            if alteration == 'identity' and function.get('TemplateInstantiationPattern'):
                                function['TemplateInstantiationPattern'] = 'not-the-pinned-primary'
                                edited = True
                            elif alteration == 'body' and not function.get('TemplateInstantiationPattern'):
                                returned = [child for child in nodes(function) if child.get('kind') == 'ReturnStmt']
                                if len(returned) >= 2:
                                    returned[0]['inner'] = copy.deepcopy(returned[-1]['inner'])
                                    edited = True
                self.assertTrue(edited)
                with self.subTest(alteration=alteration), self.assertRaises(ValueError):
                    lower_scalar_choices(copy.deepcopy(functions),changed)


if __name__ == '__main__':
    disable_network()
    unittest.main()
