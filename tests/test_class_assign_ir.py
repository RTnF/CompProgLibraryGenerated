"""Implicit assignment identities, audited std::vector entry and generated evaluator."""
from pathlib import Path
import copy
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
from class_assign import materialize_assignment, audit_assignment_record, audit_class_assignment, emit_class_assignment
from class_copy import audit_class_copy
from vector_stl import vector_declarations, audit_vector_nodes, translation_unit
from scalar_stl import walk
from test_scalar_ir import lean_environment
from check_public import check_compiler
from offline import disable_network
SOURCE = ROOT/'experiments/verification/data_structure/union_find.hpp'


def assignment(record):
    return next(n for n in record['inner'] if n.get('kind')=='CXXMethodDecl' and n.get('name')=='operator=' and
                any(p.get('kind')=='ParmVarDecl' and 'const ' in p.get('type',{}).get('qualType','') for p in n.get('inner',[])))


def actions(record):
    return next(n for n in assignment(record)['inner'] if n.get('kind')=='CompoundStmt')['inner']


class ClassAssignIRTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record,cls.roots=materialize_assignment(SOURCE,'cp::UnionFind')

    def test_original_identity_order_and_generated_union_find_profile(self):
        before=SOURCE.read_bytes()
        plan=audit_assignment_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),self.roots)
        self.assertEqual(plan['coverage'],'member_identity_only')
        self.assertEqual([(f['name'],f['kind'],f.get('type',f.get('element'))) for f in plan['fields']],
                         [('_ps','vector_assign','int'),('_num_groups','scalar_assign','int'),('_n','scalar_assign','int')])
        self.assertEqual(len({f['field_id'] for f in plan['fields']}),3)
        self.assertTrue(plan['fields'][0]['callee_id'])
        generated=emit_class_assignment(SOURCE,'cp::UnionFind','DraftAssignUF')
        checks='''
open Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppClassAssign
example : DraftAssignUF.profile = Proofs.UfClassCopyBridge.profile := rfl
example (s : NState) (target source : ObjectRef) :
  DraftAssignUF.assign s target source = assignClass s target source Proofs.UfClassCopyBridge.profile := rfl
example (s : NState) (g : Generations) (target source : ObjectRef) :
  (DraftAssignUF.trackedAssign s g target source).map Prod.fst = DraftAssignUF.assign s target source :=
  DraftAssignUF.tracked_data s g target source
'''
        self.check_lean('import Proofs.UfClassCopyBridge\n'+generated+checks)
        self.assertEqual(SOURCE.read_bytes(),before)

    def check_lean(self,text):
        with tempfile.TemporaryDirectory(prefix='assignment-generated-') as directory:
            proof=Path(directory)/'check.lean';proof.write_text(text)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_mutated_this_source_fields_order_return_and_flags_rejected(self):
        def swap(record):
            a=actions(record);a[1],a[2]=a[2],a[1]
        def dest(record): actions(record)[1]['inner'][0]['referencedMemberDecl']='foreign'
        def src(record): actions(record)[1]['inner'][1]['inner'][0]['referencedMemberDecl']='foreign'
        def parameter(record): actions(record)[1]['inner'][1]['inner'][0]['inner'][0]['referencedDecl']['id']='foreign'
        def wrong_this(record): actions(record)[1]['inner'][0]['inner'][0]['type']['qualType']='foreign::UnionFind *'
        def arrow(record): actions(record)[1]['inner'][0]['isArrow']=False
        def cast(record): actions(record)[1]['inner'][1]['castKind']='IntegralCast'
        def opcode(record): actions(record)[2]['opcode']='+='
        def returned(record): actions(record)[-1]['inner'][0]['opcode']='&'
        def callee(record): actions(record)[0]['inner'][0]['referencedMemberDecl']='foreign'
        def used(record): assignment(record)['isUsed']=False
        def implicit(record): assignment(record)['isImplicit']=False
        def signature(record): assignment(record)['type']['qualType']='const UnionFind &(const UnionFind &)'
        for mutation in (swap,dest,src,parameter,wrong_this,arrow,cast,opcode,returned,callee,used,implicit,signature):
            with self.subTest(mutation=mutation.__name__):
                record=copy.deepcopy(self.record);mutation(record)
                with self.assertRaises(ValueError):audit_assignment_record(SOURCE,'cp::UnionFind',record,self.roots)

    def test_foreign_tu_and_specialized_std_entry_rejected(self):
        _,otherRoots=materialize_assignment(SOURCE,'cp::UnionFind')
        with self.assertRaisesRegex(ValueError,'same translation unit'):
            audit_assignment_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),otherRoots)
        roots=copy.deepcopy(self.roots)
        _,instances=vector_declarations(roots)
        identifier=actions(self.record)[0]['inner'][0]['referencedMemberDecl']
        selected=next(n for inst in instances for n in walk(inst) if n.get('kind')=='CXXMethodDecl' and n.get('id')==identifier)
        selected['TemplateInstantiationPattern']='foreign'
        with self.assertRaisesRegex(ValueError,'specialization'):
            audit_assignment_record(SOURCE,'cp::UnionFind',copy.deepcopy(self.record),roots)
        # Ordinary vector lowering still refuses operator=; the new audit is opt-in.
        with self.assertRaisesRegex(ValueError,'unsupported vector operation'):
            audit_vector_nodes(SOURCE,[copy.deepcopy(assignment(self.record))],self.roots)

    def test_renamed_mutable_mixed_types_and_assignment_without_copy_constructor(self):
        with tempfile.TemporaryDirectory(prefix='assignment-shapes-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('#include <vector>\nusing Data=std::vector<long long>;\nnamespace renamed {'
                              'struct Packet {mutable Data values;unsigned int count;long stamp;mutable bool marked;};}\n')
            plan=audit_class_assignment(source,'renamed::Packet')
            self.assertEqual([(f['name'],f.get('type',f.get('element'))) for f in plan['fields']],
                             [('values','long long'),('count','unsigned int'),('stamp','long'),('marked','bool')])
            generated=emit_class_assignment(source,'renamed::Packet','DraftMixedAssignment')
            self.check_lean(generated+'\nexample : DraftMixedAssignment.profile.scalarFields.length = 3 := rfl\n')
            source.write_text('#include <vector>\nnamespace renamed {struct Packet {std::vector<int> values;int n;'
                              'Packet()=default;Packet(const Packet&)=delete;};}\n')
            plan=audit_class_assignment(source,'renamed::Packet')
            self.assertEqual(len(plan['fields']),2)
            with self.assertRaises(ValueError):audit_class_copy(source,'renamed::Packet')
            source.write_text('#include <vector>\nnamespace renamed {struct Packet {std::vector<int> values;const int n=0;};}\n')
            # The old default copy-only witness remains usable for const fields.
            self.assertEqual(len(audit_class_copy(source,'renamed::Packet')['fields']),2)
            with self.assertRaises(ValueError):audit_class_assignment(source,'renamed::Packet')

    def test_unsupported_assignment_profiles_and_source_fingerprint(self):
        declarations=[
            'struct Packet {std::vector<int> v;int n;Packet& operator=(const Packet& x){v=x.v;n=x.n;return *this;}};',
            'struct Packet {std::vector<int> v;int n;Packet& operator=(const Packet&)=default;};',
            'struct Packet {std::vector<int> v;int n;Packet& operator=(const Packet&)=delete;};',
            'struct Packet {int n;std::vector<int> v;};',
            'struct Packet {std::vector<bool> v;int n;};',
            'struct Packet {std::vector<std::vector<int>> v;int n;};',
            'struct Packet {std::vector<int> v;volatile int n;};',
            'struct Packet {std::vector<int> v;int n:3;};',
            'struct Base {};struct Packet:Base {std::vector<int> v;int n;};',
            'struct Packet {std::vector<int> v;int n;~Packet(){}};',
            'struct Packet {std::vector<int> v;virtual void f(){};int n;};',
        ]
        with tempfile.TemporaryDirectory(prefix='assignment-reject-') as directory:
            source=Path(directory)/'source.hpp'
            for decl in declarations:
                with self.subTest(declaration=decl):
                    source.write_text('#include <vector>\nnamespace other {'+decl+'}\n')
                    with self.assertRaises(ValueError):audit_class_assignment(source,'other::Packet')
            source.write_text('#include <vector>\nnamespace other {struct Packet {std::vector<int> v;int n;};}\n')
            record,roots=materialize_assignment(source,'other::Packet')
            source.write_text(source.read_text()+'// changed\n')
            with self.assertRaisesRegex(ValueError,'contents changed'):
                audit_assignment_record(source,'other::Packet',record,roots)
            source.write_text('#include <vector>\ntemplate<> std::vector<int>& std::vector<int>::operator=(const std::vector<int>&){return *this;}\nnamespace other {struct Packet {std::vector<int> v;int n;};}\n')
            with self.assertRaises(ValueError):audit_class_assignment(source,'other::Packet')
            for name in ('other::Packet; int injected','other::Packet\n','other::Packet<int>'):
                with self.subTest(name=name),self.assertRaises(ValueError):audit_class_assignment(source,name)
            with self.assertRaises(ValueError):translation_unit(source,copy_assignment=True)
            with self.assertRaises(ValueError):emit_class_assignment(source,'other::Packet','Bad;namespace')

    def test_native_original_and_candidate_special_members(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='assignment-native-') as directory:
            binary=Path(directory)/'special'
            subprocess.run(['g++','-std=c++17','-O1','-fno-access-control','-fsanitize=undefined',
                '-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),str(ROOT/'tests/imports/union_find_special_members.cpp'),'-o',str(binary)],check=True)
            counts=[0,1,2,4,17]
            result=subprocess.run([str(binary)],input="\n".join(map(str,counts))+"\n",capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),[f"{n} {int(n>0)} {int(n>0)} {int(n>0)}" for n in counts])

if __name__=='__main__':
    disable_network()
    unittest.main()
