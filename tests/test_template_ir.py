"""Primary syntax, arithmetic conversions and Clang specialization agreement."""
from pathlib import Path
import json
import re
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
import template_ir
import state_ir
from offline import disable_network

HEADER=ROOT/'experiments/verification/template/update_extrema.hpp'

class TemplateTests(unittest.TestCase):
    def test_all_supported_integral_specializations_match_clang(self):
        primary=template_ir.lower_source(HEADER)
        self.assertEqual(primary,json.loads((HEADER.parent/'update_extrema_primary.json').read_text()))
        self.assertEqual([t['coverage'] for t in primary['templates']],['primary_syntax_only']*2)
        types=list(template_ir.TYPES)
        with tempfile.TemporaryDirectory(prefix='primary-instances-') as directory:
            source=Path(directory)/'instances.cpp'
            text=f'#include "{HEADER}"\n'
            expected={}
            for t in primary['templates']:
                for left in types:
                    for right in types:
                        text+=f'template bool cp::{t["name"]}<{left},{right}>({left}&,const {right}&);\n'
                        f=template_ir.specialize(t,[left,right])
                        expected[f['name']]=f
            source.write_text(text)
            actual=state_ir.lower_source(source)
            self.assertEqual(len(actual['functions']),98)
            for f in actual['functions']:
                with self.subTest(function=f['name']):self.assertEqual(f,expected[f['name']])
            # An explicit target conversion policy must agree too, while
            # checked remains the default and is never silently upgraded.
            actual_target=state_ir.lower_source(source,signed_conversion=template_ir.SIGNED_CONVERSIONS[1])
            expected_target={f['name']:f for t in primary['templates'] for left in types for right in types
                for f in [template_ir.specialize(t,[left,right],template_ir.SIGNED_CONVERSIONS[1])]}
            for f in actual_target['functions']:
                with self.subTest(target_function=f['name']):self.assertEqual(f,expected_target[f['name']])
            self.assertNotEqual(expected['chmax__int__unsigned_long'],expected_target['chmax__int__unsigned_long'])

    def test_primary_renaming_mutation_and_unrelated_template(self):
        original=template_ir.lower_source(HEADER)
        text=HEADER.read_text()
        with tempfile.TemporaryDirectory(prefix='primary-renaming-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(re.sub(r'\b(S|T|a|b)\b',lambda m:{'S':'Left','T':'Right','a':'destination','b':'source'}[m[0]],text))
            self.assertEqual(template_ir.lower_source(source),original)
            source.write_text(text.replace('a < b','a <= b'))
            self.assertNotEqual(template_ir.lower_source(source),original)
            source.write_text('namespace cp {template<class X,class Y>bool choose(X& x,const Y& y){if(y>=x){x=y;return true;}return false;}}')
            t=template_ir.lower_source(source)['templates'][0]
            cpp=Path(directory)/'instances.cpp'
            cpp.write_text(f'#include "{source}"\ntemplate bool cp::choose<long long,unsigned int>(long long&,const unsigned int&);\n')
            self.assertEqual(template_ir.specialize(t,['long long','unsigned int']),state_ir.lower_source(cpp)['functions'][0])
            for path in ['experiments/library/cpp/template/template.cpp',
                         'experiments/library3/cpp/Template/Template.cpp']:
                for filter_ in ['chmax','chmin']:
                    imported=template_ir.lower_source(ROOT/path,filter_)
                    candidate=next(t for t in original['templates'] if t['name']==filter_)
                    # using namespace std introduces unresolved operator candidates.
                    # Keep that context; builtin arguments cannot select an overload.
                    self.assertNotEqual(imported['templates'],[candidate])
                    expected={}
                    declarations=f'#include "{ROOT/path}"\n'
                    for left in template_ir.TYPES:
                        for right in template_ir.TYPES:
                            args=[left,right]
                            function=template_ir.specialize(imported['templates'][0],args)
                            self.assertEqual(function,template_ir.specialize(candidate,args))
                            expected[function['name']]=function
                            declarations+=f'template bool {filter_}<{left},{right}>({left}&,const {right}&);\n'
                    cpp.write_text(declarations)
                    actual=state_ir.lower_source(cpp,filter_)
                    self.assertEqual(len(actual['functions']),49)
                    for function in actual['functions']:
                        self.assertEqual(function,expected[function['name']])

    def test_unresolved_and_unsupported_features_are_refused(self):
        primary=template_ir.lower_source(HEADER)['templates'][0]
        for args in [['std::string','std::string'],['double','double'],['int'],['short','short']]:
            with self.subTest(arguments=args),self.assertRaises(ValueError):template_ir.specialize(primary,args)
        with self.assertRaises(ValueError):template_ir.specialize(primary,['int','int'],'unknown-target')
        sources=[
            'template<class T=int>bool f(T&a){return true;}',
            'template<class... T>bool f(T&...a){return true;}',
            'template<int N>bool f(int&a){return true;}',
            'template<class T>bool f(T a){return true;}',
            'template<class T>T f(T&a){return a;}',
            'template<class T>bool f(volatile T&a){return true;}',
            'template<class T>bool f(T&&a){return true;}',
            'template<class T>bool f(T&a){a+=1;return true;}',
            'template<class T>bool f(T&a){T x=a;return true;}',
            'template<class T>bool f(T&a){while(a>0){a=0;}return true;}',
            'template<class T>bool f(T&a){return g(a);}',
            'template<class T>bool f(const T&a){a=1;return true;}',
            'template<class T>bool f(T&a)noexcept{return true;}',
            'template<class T>bool f_λ(T&a){return true;}',
        ]
        with tempfile.TemporaryDirectory(prefix='primary-rejection-') as directory:
            source=Path(directory)/'source.cpp'
            for text in sources:
                with self.subTest(source=text):
                    source.write_text('namespace cp {'+text+'}')
                    with self.assertRaises(ValueError):template_ir.lower_source(source)
            # Existing state/public routes still require resolved instances.
            source.write_text('namespace cp {template<class T>bool f(T&a){return true;}}')
            with self.assertRaises(ValueError):state_ir.lower_source(source)
            source.write_text('namespace cp {template<class T>bool f(T&a){return true;}}\ntemplate bool cp::f<int>(int&);')
            with self.assertRaises(ValueError):template_ir.lower_source(source)

if __name__=='__main__':
    disable_network();unittest.main()
