"""Implicit destructor provenance, reverse fields and independent materialization."""
from pathlib import Path
import copy
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'),str(ROOT/'tools')]
from class_destroy import materialize_destroy, audit_destroy_record, audit_class_destroy
from vector_stl import translation_unit, vector_declarations
from offline import disable_network

SOURCE = ROOT/'experiments/verification/data_structure/union_find.hpp'


def destructor(record):
    return next(n for n in record['inner'] if n.get('kind') == 'CXXDestructorDecl')


class DestroyAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record, cls.roots = materialize_destroy(SOURCE, 'cp::UnionFind')

    def test_original_reverse_plan_and_modes(self):
        plan = audit_destroy_record(SOURCE, 'cp::UnionFind', copy.deepcopy(self.record), self.roots)
        self.assertEqual(plan['coverage'], 'member_identity_only')
        self.assertEqual(plan['operation'], 'destroy')
        self.assertEqual(plan['member_id'], destructor(self.record)['id'])
        self.assertEqual([(f['name'], f['kind']) for f in plan['fields']],
                         [('_n','scalar_lifetime_end'),('_num_groups','scalar_lifetime_end'),('_ps','vector_destroy')])
        self.assertTrue(plan['fields'][-1]['callee_id'])
        self.assertEqual(len({f['field_id'] for f in plan['fields']}), 3)
        for options in ({'class_destruction':True},
                        {'class_destruction':True,'copy_class':'cp::UnionFind','copy_records':[],'copy_assignment':True},
                        {'class_destruction':True,'copy_class':'cp::UnionFind','copy_records':[],'move_kind':'construct'},
                        {'class_destruction':1,'copy_class':'cp::UnionFind','copy_records':[]}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                translation_unit(SOURCE, **options)

    def test_original_destructor_flags_body_and_field_order_rejected(self):
        mutations = [lambda r: destructor(r).update(isImplicit=False),
                     lambda r: destructor(r).update(isUsed=False),
                     lambda r: destructor(r).update(explicitlyDefaulted='deleted'),
                     lambda r: destructor(r).update(isDeleted=True),
                     lambda r: destructor(r).update(name='~Other'),
                     lambda r: destructor(r).update(type={'qualType':'void ()'}),
                     lambda r: destructor(r)['loc'].update(offset=0),
                     lambda r: destructor(r)['inner'][0].update(inner=[{'kind':'NullStmt'}]),
                     lambda r: destructor(r)['inner'].append({'kind':'ParmVarDecl'}),
                     lambda r: r['inner'].append(copy.deepcopy(destructor(r))),
                     lambda r: r.update(bases=[{'type':{'qualType':'Other'}}])]
        def reorder(record):
            indices = [i for i,n in enumerate(record['inner']) if n.get('kind')=='FieldDecl']
            record['inner'][indices[0]],record['inner'][indices[1]] = record['inner'][indices[1]],record['inner'][indices[0]]
        mutations.append(reorder)
        for mutate in mutations:
            record = copy.deepcopy(self.record)
            mutate(record)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                audit_destroy_record(SOURCE, 'cp::UnionFind', record, self.roots)

    def test_foreign_source_unit_and_vector_pattern_rejected(self):
        roots = copy.deepcopy(self.roots)
        roots[0]['_copy_translation_unit'] = 'foreign'
        with self.assertRaisesRegex(ValueError, 'same translation unit'):
            audit_destroy_record(SOURCE, 'cp::UnionFind', copy.deepcopy(self.record), roots)
        record = copy.deepcopy(self.record)
        record['_copy_source_sha256'] = 'foreign'
        with self.assertRaisesRegex(ValueError, 'source identity'):
            audit_destroy_record(SOURCE, 'cp::UnionFind', record, self.roots)
        for mode in ('used','pattern','throwing','deleted','allocator'):
            roots = copy.deepcopy(self.roots)
            _, instances = vector_declarations(roots)
            instance = next(i for i in instances if any(n.get('kind')=='CXXDestructorDecl' and n.get('isUsed') for n in i.get('inner',[])))
            selected = destructor(instance)
            if mode == 'used': selected['isUsed'] = False
            elif mode == 'pattern': selected['TemplateInstantiationPattern'] = 'foreign'
            elif mode == 'throwing': selected['type'] = {'qualType':'void () noexcept(false)'}
            elif mode == 'deleted': selected['isDeleted'] = True
            else:
                args = [n for n in instance['inner'] if n.get('kind')=='TemplateArgument']
                args[1]['type']['qualType'] = 'OtherAllocator'
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                audit_destroy_record(SOURCE, 'cp::UnionFind', copy.deepcopy(self.record), roots)

    def test_deleted_copy_const_vectors_and_interleaved_fields(self):
        with tempfile.TemporaryDirectory(prefix='destroy-profile-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text('''#include <vector>
namespace renamed {struct Packet {
  long stamp; const std::vector<long long> data; bool marked; std::vector<int> other;
  Packet(const Packet&)=delete; Packet(Packet&&)=delete;
};}
''')
            plan = audit_class_destroy(source, 'renamed::Packet')
            self.assertEqual([f['name'] for f in plan['fields']], ['other','marked','data','stamp'])
            self.assertEqual([f.get('type',f.get('element')) for f in plan['fields']], ['int','bool','long long','long'])
            record, roots = materialize_destroy(source, 'renamed::Packet')
            source.write_text(source.read_text()+'\n// changed\n')
            with self.assertRaisesRegex(ValueError, 'source identity'):
                audit_destroy_record(source, 'renamed::Packet', record, roots)
            source.write_text('namespace renamed {struct Packet {int a;const long b=7;};}\n')
            scalar_plan = audit_class_destroy(source, 'renamed::Packet')
            self.assertEqual([(f['name'],f['kind']) for f in scalar_plan['fields']],
                             [('b','scalar_lifetime_end'),('a','scalar_lifetime_end')])

    def test_unsupported_destructors_elements_and_specialization_rejected(self):
        declarations = [
            'struct Packet {std::vector<int> v; ~Packet(){}};',
            'struct Packet {std::vector<int> v; ~Packet()=default;};',
            'struct Packet {std::vector<int> v; ~Packet()=delete;};',
            'class Packet {std::vector<int> v; ~Packet()=default;};',
            'struct Packet {std::vector<bool> v;};',
            'struct Packet {std::vector<std::vector<int>> v;};',
            'struct Packet {std::vector<int> v; int& reference;};',
        ]
        with tempfile.TemporaryDirectory(prefix='destroy-reject-') as directory:
            source = Path(directory)/'source.hpp'
            for declaration in declarations:
                source.write_text('#include <vector>\nnamespace changed {'+declaration+'}\n')
                with self.subTest(declaration=declaration), self.assertRaises(ValueError):
                    audit_class_destroy(source, 'changed::Packet')
            source.write_text('''#include <vector>
namespace std {template<> vector<int>::~vector() noexcept {}}
namespace changed {struct Packet {std::vector<int> v;};}
''')
            with self.assertRaisesRegex(ValueError, 'specialization|pristine|standard library namespaces'):
                audit_class_destroy(source, 'changed::Packet')


if __name__ == '__main__':
    disable_network()
    unittest.main()
