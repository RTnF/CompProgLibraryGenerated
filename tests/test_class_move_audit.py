"""Actual implicit move AST identities and opt-in standard move audit."""
from pathlib import Path
import copy
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'),str(ROOT/'tools')]
from class_move import materialize_move, audit_move_record, audit_class_move
from class_copy import audit_class_copy
from class_assign import audit_class_assignment
from vector_stl import audit_vector_nodes, translation_unit, vector_declarations
from scalar_stl import walk
from offline import disable_network
SOURCE = ROOT/'experiments/verification/data_structure/union_find.hpp'


def member(record,kind):
    return next(n for n in record['inner'] if n.get('kind') == ('CXXConstructorDecl' if kind=='construct' else 'CXXMethodDecl') and
                n.get('name') == (record['name'] if kind=='construct' else 'operator=') and
                any(p.get('kind')=='ParmVarDecl' and '&&' in p.get('type',{}).get('qualType','') for p in n.get('inner',[])))


def actions(record,kind):
    m=member(record,kind)
    return ([n for n in m['inner'] if n.get('kind')=='CXXCtorInitializer'] if kind=='construct' else
            next(n for n in m['inner'] if n.get('kind')=='CompoundStmt')['inner'])


def source_field(record,kind,index):
    a=actions(record,kind)[index]
    if kind=='construct':a=a['inner'][0]
    else:a=a['inner'][1]
    if index:a=a['inner'][0]
    elif kind=='construct':a=a['inner'][0]
    return a


class MoveAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.units={kind:materialize_move(SOURCE,'cp::UnionFind',kind) for kind in ('construct','assign')}

    def test_original_move_members_and_modes(self):
        for kind,(record,roots) in self.units.items():
            with self.subTest(kind=kind):
                plan=audit_move_record(SOURCE,'cp::UnionFind',copy.deepcopy(record),roots,kind)
                self.assertEqual(plan['coverage'],'member_identity_only')
                self.assertEqual([(f['name'],f['kind']) for f in plan['fields']],
                    [('_ps','vector_move'),('_num_groups','scalar_move'),('_n','scalar_move')])
                self.assertEqual(len({f['field_id'] for f in plan['fields']}),3)
                self.assertTrue(plan['fields'][0]['callee_id'])
                self.assertEqual(plan['operation'],'move_'+kind)
        record,roots=self.units['assign']
        for mode in ({},{'copy_assignment':True}):
            with self.assertRaises(ValueError):audit_vector_nodes(SOURCE,[copy.deepcopy(member(record,'assign'))],roots,**mode)
        with self.assertRaises(ValueError):audit_vector_nodes(SOURCE,[],[],copy_assignment=True,move_assignment=True)
        with self.assertRaises(ValueError):translation_unit(SOURCE,move_kind='construct')
        with self.assertRaises(ValueError):materialize_move(SOURCE,'cp::UnionFind','both')

    def test_source_cast_field_order_and_member_flags_rejected(self):
        for kind,(original,roots) in self.units.items():
            def source_id(r):source_field(r,kind,0)['referencedMemberDecl']='foreign'
            def category(r):source_field(r,kind,1)['valueCategory']='lvalue'
            def cast(r):source_field(r,kind,0)['inner'][0]['castKind']='BitCast'
            def cast_class(r):source_field(r,kind,0)['inner'][0]['type']['qualType']='Other'
            def parameter(r):source_field(r,kind,0)['inner'][0]['inner'][0]['referencedDecl']['id']='foreign'
            def field_type(r):source_field(r,kind,1)['type']['qualType']='long'
            def used(r):member(r,kind)['isUsed']=False
            def implicit(r):member(r,kind)['isImplicit']=False
            def defaulted(r):member(r,kind)['explicitlyDefaulted']='deleted'
            def result(r):member(r,kind)['type']['qualType']='const UnionFind &(UnionFind &&)'
            def order(r):
                acts=actions(r,kind)
                if kind=='construct':
                    m=member(r,kind);indices=[i for i,n in enumerate(m['inner']) if n.get('kind')=='CXXCtorInitializer']
                    m['inner'][indices[1]],m['inner'][indices[2]]=m['inner'][indices[2]],m['inner'][indices[1]]
                else:acts[1],acts[2]=acts[2],acts[1]
            for mutate in (source_id,category,cast,cast_class,parameter,field_type,used,implicit,defaulted,result,order):
                with self.subTest(kind=kind,mutation=mutate.__name__):
                    record=copy.deepcopy(original);mutate(record)
                    with self.assertRaises(ValueError):audit_move_record(SOURCE,'cp::UnionFind',record,roots,kind)

    def test_vector_callee_destination_initializer_and_return_rejected(self):
        record,roots=self.units['assign']
        def callee(r):actions(r,'assign')[0]['inner'][0]['referencedMemberDecl']='foreign'
        def target(r):actions(r,'assign')[1]['inner'][0]['referencedMemberDecl']='foreign'
        def this(r):actions(r,'assign')[1]['inner'][0]['inner'][0]['type']['qualType']='Other *'
        def opcode(r):actions(r,'assign')[1]['opcode']='+='
        def returned(r):actions(r,'assign')[-1]['inner'][0]['opcode']='&'
        for mutate in (callee,target,this,opcode,returned):
            with self.subTest(mutation=mutate.__name__):
                changed=copy.deepcopy(record);mutate(changed)
                with self.assertRaises(ValueError):audit_move_record(SOURCE,'cp::UnionFind',changed,roots,'assign')
        record,roots=self.units['construct']
        for mode in ('field','signature','body'):
            with self.subTest(mode=mode):
                changed=copy.deepcopy(record)
                if mode=='field':actions(changed,'construct')[0]['anyInit']['id']='foreign'
                elif mode=='signature':actions(changed,'construct')[0]['inner'][0]['ctorType']['qualType']='void (const vector<int> &)'
                else:next(n for n in member(changed,'construct')['inner'] if n.get('kind')=='CompoundStmt')['inner']=[{'kind':'NullStmt'}]
                with self.assertRaises(ValueError):audit_move_record(SOURCE,'cp::UnionFind',changed,roots,'construct')

    def test_foreign_unit_source_and_standard_specialization_rejected(self):
        first,roots=self.units['construct'];_,other=self.units['assign']
        with self.assertRaisesRegex(ValueError,'same translation unit'):
            audit_move_record(SOURCE,'cp::UnionFind',copy.deepcopy(first),other,'construct')
        plan=audit_move_record(SOURCE,'cp::UnionFind',copy.deepcopy(first),roots,'construct')
        unusedRoots=copy.deepcopy(roots)
        _,instances=vector_declarations(unusedRoots)
        constructor=next(n for instance in instances for n in walk(instance)
                         if n.get('id')==plan['fields'][0]['callee_id'])
        constructor['isUsed']=False
        with self.assertRaises(ValueError):
            audit_move_record(SOURCE,'cp::UnionFind',copy.deepcopy(first),unusedRoots,'construct')
        assignment,assignmentRoots=self.units['assign']
        changedRoots=copy.deepcopy(assignmentRoots)
        _,instances=vector_declarations(changedRoots)
        identifier=actions(assignment,'assign')[0]['inner'][0]['referencedMemberDecl']
        selected=next(n for instance in instances for n in walk(instance) if n.get('id')==identifier)
        selected['TemplateInstantiationPattern']='foreign'
        with self.assertRaisesRegex(ValueError,'specialization'):
            audit_move_record(SOURCE,'cp::UnionFind',copy.deepcopy(assignment),changedRoots,'assign')
        with tempfile.TemporaryDirectory(prefix='move-source-') as directory:
            source=Path(directory)/'source.hpp';source.write_bytes(SOURCE.read_bytes())
            with self.assertRaisesRegex(ValueError,'source identity'):
                audit_move_record(source,'cp::UnionFind',copy.deepcopy(first),roots,'construct')
            source.write_text('''#include <vector>
namespace std {template<> vector<int>& vector<int>::operator=(vector<int>&&) noexcept{return *this;}}
namespace changed {struct Packet {std::vector<int> data;int n;};}
''')
            with self.assertRaisesRegex(ValueError,'specialization|pristine|standard library namespaces'):
                audit_class_move(source,'changed::Packet','assign')

    def test_renamed_types_const_scalar_and_unsupported_members(self):
        with tempfile.TemporaryDirectory(prefix='move-shapes-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('''#include <vector>
namespace renamed {struct Packet {mutable std::vector<long long> data;unsigned int n;long stamp;bool marked;};}
''')
            for kind in ('construct','assign'):
                plan=audit_class_move(source,'renamed::Packet',kind)
                self.assertEqual([f.get('type',f.get('element')) for f in plan['fields']],['long long','unsigned int','long','bool'])
            self.assertEqual(len(audit_class_assignment(source,'renamed::Packet')['fields']),4)
            source.write_text('''#include <vector>
namespace renamed {struct Packet {std::vector<int> data;const int n=2;};}
''')
            plan=audit_class_move(source,'renamed::Packet','construct')
            self.assertFalse(plan['fields'][1]['writable'])
            with self.assertRaises(ValueError):audit_class_move(source,'renamed::Packet','assign')
            # Move audit remains separate from the unchanged copy-only entry paths.
            self.assertEqual(len(audit_class_copy(source,'renamed::Packet')['fields']),2)
            unsupported=[
                'struct Packet {std::vector<int> v;int n;Packet(Packet&&)=default;};',
                'struct Packet {std::vector<int> v;int n;~Packet(){}};',
                'struct Packet {std::vector<int> v;int &n;};',
                'struct Packet {std::vector<bool> v;int n;};',
                'struct Packet {const std::vector<int> v;int n;};',
                'struct Packet {std::vector<int> v;int n;Packet& operator=(Packet&&x){v=static_cast<std::vector<int>&&>(x.v);n=x.n;return *this;}};',
            ]
            for declaration in unsupported:
                with self.subTest(declaration=declaration):
                    source.write_text('#include <vector>\nnamespace renamed {'+declaration+'}\n')
                    with self.assertRaises(ValueError):audit_class_move(source,'renamed::Packet','construct' if 'operator=' not in declaration else 'assign')

    def test_fixed_native_allocation_transfer_and_self_move(self):
        with tempfile.TemporaryDirectory(prefix='move-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text('#include "'+str(SOURCE)+'"\n'+r'''
#include <cassert>
#include <utility>
int main(){
  std::vector<int> source{10,11},target{99};
  int* saved=&source[0];auto& object=source;auto& destination=target;
  target=std::move(source);
  assert(&object==&source && &destination==&target);
  assert(target.data()==saved && *saved==10 && source.empty() && source.capacity()==0);
  source.push_back(3);assert(source[0]==3 && *saved==10);
  target=std::move(target);assert(target.empty() && target.capacity()==0);
  std::vector<int> original{7,8};int* element=&original[1];
  std::vector<int> constructed(std::move(original));
  assert(constructed.data()+1==element && *element==8 && original.empty());
  for(int n : {0,1,2,17}){
    cp::UnionFind a(n),b(4);cp::UnionFind moved(std::move(a));
    assert(moved.num_groups()==n && a.num_groups()==n);
    b=std::move(moved);assert(b.num_groups()==n && moved.num_groups()==n);
    b=std::move(b);assert(b.num_groups()==n);
    cp::UnionFind fresh(n);b=fresh;
    if(n)assert(b.size(0)==1);
  }
}
''')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)


if __name__=='__main__':
    disable_network()
    unittest.main()
