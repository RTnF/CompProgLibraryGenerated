"""Implicit class-copy witnesses, declaration ownership and mutation rejection."""
from pathlib import Path
import copy
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'));sys.path.insert(0,str(ROOT/'tools'))
from class_copy import materialize_copy, audit_copy_record, audit_class_copy
from vector_stl import vector_declarations
from nested_ir import lower_source
from offline import disable_network
SOURCE=ROOT/'experiments/verification/data_structure/union_find.hpp'


def ctor(record):
    return next(n for n in record['inner'] if n.get('kind')=='CXXConstructorDecl' and
                any(c.get('kind')=='ParmVarDecl' and 'const ' in c.get('type',{}).get('qualType','') and
                    '&' in c.get('type',{}).get('qualType','') for c in n.get('inner',[])))


def initializers(record):
    return [n for n in ctor(record)['inner'] if n.get('kind')=='CXXCtorInitializer']


class ClassCopyAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record,cls.roots=materialize_copy(SOURCE,'cp::UnionFind')

    def test_real_union_find_order_and_standard_constructor_identity(self):
        before=SOURCE.read_bytes()
        plan=audit_copy_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),self.roots)
        self.assertEqual(plan['coverage'],'member_identity_only')
        self.assertEqual([(f['name'],f['kind'],f.get('type',f.get('element')),f['writable']) for f in plan['fields']],
                         [('_ps','vector_copy','int',True),('_num_groups','scalar_copy','int',True),('_n','scalar_copy','int',True)])
        self.assertEqual(len({f['field_id'] for f in plan['fields']}),3)
        self.assertTrue(plan['fields'][0]['constructor_id'])
        self.assertEqual(SOURCE.read_bytes(),before)

    def test_multiple_vector_member_audit_preserves_each_declaration_identity(self):
        with tempfile.TemporaryDirectory(prefix='multi-vector-copy-audit-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('#include <vector>\nstruct Duo {int n;std::vector<int> a;'
                              'const long stamp;mutable std::vector<unsigned long> b;};\n')
            record,roots=materialize_copy(source,'Duo')
            plan=audit_copy_record(source,'Duo',copy.deepcopy(record),roots,
                                   vector_anywhere=True,multiple_vectors=True)
            self.assertEqual([(f['name'],f['kind'],f.get('type',f.get('element')),f['writable'])
                              for f in plan['fields']],
                             [('n','scalar_copy','int',True),('a','vector_copy','int',True),
                              ('stamp','scalar_copy','long',False),('b','vector_copy','unsigned long',True)])
            with self.assertRaisesRegex(ValueError,'exactly one flat vector'):
                audit_copy_record(source,'Duo',copy.deepcopy(record),roots,vector_anywhere=True)
            changed=copy.deepcopy(record)
            expr=initializers(changed)[3]['inner'][0]['inner'][0]
            if expr.get('kind')=='ImplicitCastExpr':
                expr=expr['inner'][0]
            expr['referencedMemberDecl']=plan['fields'][1]['field_id']
            with self.assertRaisesRegex(ValueError,'matching source member'):
                audit_copy_record(source,'Duo',changed,roots,
                                   vector_anywhere=True,multiple_vectors=True)
            for options in ({'multiple_vectors':True},
                            {'multiple_vectors':1,'vector_anywhere':True}):
                with self.subTest(options=options), self.assertRaisesRegex(ValueError,'multiple vector audit'):
                    audit_copy_record(source,'Duo',copy.deepcopy(record),roots,**options)

    def test_names_counts_types_const_and_mutable_are_not_hardcoded(self):
        text='''#include <vector>
using Values=std::vector<long long>;
namespace renamed {struct Packet {mutable Values payload;unsigned int number;const long stamp;mutable bool marked;};
struct Only {std::vector<unsigned long> data;};struct ConstOnly {const Values storage;};}
'''
        with tempfile.TemporaryDirectory(prefix='class-copy-names-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(text)
            plan=audit_class_copy(source,'renamed::Packet')
            self.assertEqual([(f['name'],f['kind'],f.get('type',f.get('element')),f['writable']) for f in plan['fields']],
                [('payload','vector_copy','long long',True),('number','scalar_copy','unsigned int',True),
                 ('stamp','scalar_copy','long',False),('marked','scalar_copy','bool',True)])
            plan=audit_class_copy(source,'renamed::Only')
            self.assertEqual([(f['name'],f['element']) for f in plan['fields']],[('data','unsigned long')])
            plan=audit_class_copy(source,'renamed::ConstOnly')
            self.assertEqual([(f['name'],f['element'],f['writable']) for f in plan['fields']],[('storage','long long',False)])

    def test_invalid_record_and_member_mutations(self):
        def mutate(label, change):
            with self.subTest(label=label):
                record=copy.deepcopy(self.record);change(record)
                with self.assertRaises(ValueError):
                    audit_copy_record(SOURCE,'cp::UnionFind',record,self.roots)
        mutate('user copy',lambda r:ctor(r).__setitem__('isImplicit',False))
        mutate('deleted copy',lambda r:ctor(r).__setitem__('explicitlyDeleted',True))
        mutate('not used',lambda r:ctor(r).__setitem__('isUsed',False))
        mutate('constructor name',lambda r:ctor(r).__setitem__('name','Other'))
        mutate('body statement',lambda r:next(n for n in ctor(r)['inner'] if n['kind']=='CompoundStmt').__setitem__('inner',[{'kind':'NullStmt'}]))
        mutate('base class',lambda r:r.__setitem__('bases',[{'type':{'qualType':'Base'}}]))
        mutate('field id',lambda r:initializers(r)[0]['anyInit'].__setitem__('id','foreign'))
        mutate('field member id',lambda r:initializers(r)[0]['inner'][0]['inner'][0].__setitem__('referencedMemberDecl','foreign'))
        mutate('source parameter',lambda r:initializers(r)[0]['inner'][0]['inner'][0]['inner'][0]['referencedDecl'].__setitem__('id','foreign'))
        mutate('scalar load',lambda r:initializers(r)[1]['inner'][0].__setitem__('castKind','IntegralCast'))
        mutate('source qualifier',lambda r:next(n for n in ctor(r)['inner'] if n['kind']=='ParmVarDecl')['type'].__setitem__('qualType','UnionFind &'))
        def reorder(r):
            c=ctor(r); positions=[i for i,n in enumerate(c['inner']) if n['kind']=='CXXCtorInitializer']
            a,b=positions[1:];c['inner'][a],c['inner'][b]=c['inner'][b],c['inner'][a]
        mutate('initializer order',reorder)
        def stale(r):
            expr=initializers(r)[0]['inner'][0]
            expr.update(verifiedVectorConstructor='copy',verifiedVectorElement='int',verifiedVectorConstructorDecl='stale')
            expr['ctorType']['qualType']='void (int)'
        mutate('stale vector markers',stale)
        mutate('foreign source location',lambda r:r['loc'].__setitem__('file','/tmp/foreign.hpp'))

    def test_standard_helper_and_cross_dump_identity(self):
        with self.assertRaisesRegex(ValueError,'qualified class identity'):
            audit_copy_record(SOURCE,'other::UnionFind',copy.deepcopy(self.record),self.roots)
        roots=copy.deepcopy(self.roots)
        _,instances=vector_declarations(roots)
        instance=next(i for i in instances if [c.get('type',{}).get('qualType') for c in i.get('inner',[])
                       if c.get('kind')=='TemplateArgument']==['int','std::allocator<int>'])
        selected=next(n for n in instance['inner'] if n.get('kind')=='CXXConstructorDecl' and
                      n.get('type',{}).get('qualType')=='void (const vector<int> &)')
        selected['TemplateInstantiationPattern']='foreign'
        with self.assertRaisesRegex(ValueError,'specialization'):
            audit_copy_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),roots)
        _,other_roots=materialize_copy(SOURCE,'cp::UnionFind')
        with self.assertRaisesRegex(ValueError,'same translation unit'):
            audit_copy_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),other_roots)

    def test_source_origin_content_and_witness_identifiers(self):
        with tempfile.TemporaryDirectory(prefix='class-copy-origin-') as directory:
            scratch=Path(directory)
            body='#include <vector>\nnamespace cp {struct Value {std::vector<int> data;int count;};}\n'
            source=scratch/'source.hpp';source.write_text(body)
            record,roots=materialize_copy(source,'cp::Value')
            other=scratch/'other.hpp';other.write_text(body)
            with self.assertRaisesRegex(ValueError,'source identity'):
                audit_copy_record(other,'cp::Value',record,roots)
            source.write_text(body+'// modified\n')
            with self.assertRaisesRegex(ValueError,'contents changed'):
                audit_copy_record(source,'cp::Value',record,roots)
            source.write_text('#include "other.hpp"\n')
            with self.assertRaisesRegex(ValueError,'original forced source'):
                audit_class_copy(source,'cp::Value')
            source.write_text(body)
            for name in ['cp::Value; int injected','cp::Value\n','cp::Value<int>']:
                with self.subTest(name=name),self.assertRaises(ValueError):
                    audit_class_copy(source,name)

    def test_unsupported_cpp_profiles_and_lowering_remain_rejected(self):
        declarations=[
            'struct Value {std::vector<int> data;int n;Value(const Value& x):data(x.data),n(x.n) {}};',
            'struct Value {std::vector<int> data;int n;Value(const Value&)=default;};',
            'struct Value {std::vector<int> data;int n;Value(const Value&)=delete;};',
            'struct Value {std::vector<int> data;int n;~Value(){}};',
            'struct Base {};struct Value:Base {std::vector<int> data;int n;};',
            'struct Value {int n;std::vector<int> data;};',
            'struct Value {std::vector<std::vector<int>> data;int n;};',
            'struct Value {std::vector<bool> data;int n;};',
            'struct Value {std::vector<int> data;int& n;};',
            'struct Value {std::vector<int> data;int n:3;};',
            'struct Value {std::vector<int> data;volatile int n;};',
            'struct Value {std::vector<int> data;virtual void f(){};int n;};',
            '#define DECL struct Value {std::vector<int> data;int n;};\nDECL',
            'template<class T> struct Alloc:std::allocator<T>{template<class U>struct rebind {using other=Alloc<U>;};};\nstruct Value {std::vector<int,Alloc<int>> data;int n;};',
        ]
        with tempfile.TemporaryDirectory(prefix='class-copy-rejected-') as directory:
            source=Path(directory)/'source.hpp'
            for text in declarations:
                with self.subTest(text=text):
                    source.write_text('#include <vector>\nnamespace cp {\n'+text+'\n}\n')
                    with self.assertRaises(ValueError):
                        audit_class_copy(source,'cp::Value')
            source.write_text('#include <vector>\nnamespace std {template<> class vector<int>{public: vector(){} vector(const vector&){};};}\nnamespace cp {struct Value {std::vector<int> data;int n;};}\n')
            with self.assertRaisesRegex(ValueError,'standard library namespaces'):
                audit_class_copy(source,'cp::Value')
            source.write_text('#include <vector>\ntemplate<> std::vector<int>::vector(const std::vector<int>&) {}\nnamespace cp {struct Value {std::vector<int> data;int n;};}\n')
            with self.assertRaises(ValueError):
                audit_class_copy(source,'cp::Value')
            source.write_text('#include <vector>\nunsigned long f(const std::vector<int>& source){std::vector<int> target(source);return target.size();}\n')
            generated=lower_source(source)
            self.assertEqual(generated['functions'][0]['body'][0]['kind'],'copy_vector')

if __name__=='__main__':
    disable_network()
    unittest.main()
