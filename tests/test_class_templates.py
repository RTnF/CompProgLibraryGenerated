"""Controlled class-template materialization and source provenance."""
import hashlib
import copy
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools')]
from class_templates import TemplateInstance, instantiate_members, require_method_bodies
import vector_stl
from vector_stl import translation_unit
from offline import disable_network
from ast_stream import _display_name, _function_class_name
from class_lowering import ErasedClass, Eraser
from template_class_ir import lower_template_class


class ClassTemplateTests(unittest.TestCase):
    def materialize(self, directory, definition, driver, *, qualified='other::Box',
                    arguments=('long long', '3'), **options):
        directory = Path(directory)
        source = directory/'source.hpp'
        witness = directory/'instantiate.cpp'
        source.write_text(definition)
        witness.write_text(driver)
        records, callees = [], []
        translation_unit(source, copy_class=qualified, copy_records=records,
                         callees=callees, template_instance=TemplateInstance(arguments, witness),
                         **options)
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]['_copy_source_sha256'], hashlib.sha256(source.read_bytes()).hexdigest())
        self.assertEqual(records[0]['_template_instance_witness_sha256'], hashlib.sha256(witness.read_bytes()).hexdigest())
        return records[0], callees

    definition = '''namespace other {
template<class T, int N> struct Box {
 T x; Box():x(N){} Box(T value):x(value){}
 T get()const{return x;}
};
}
namespace cp { int original_helper(int x){return x+1;} }
'''
    driver = '''namespace cp { int injected_helper(int x){return x+99;} }
int instantiate(){other::Box<long long,3> a;other::Box<long long,3> b(7);
return static_cast<int>(a.get()+b.get());}
'''

    def test_implicit_instance_and_callee_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            record, callees = self.materialize(directory, self.definition, self.driver)
            origin = record['_template_witness_origin']
            self.assertEqual(origin['record_id'], record['id'])
            self.assertEqual(origin['requested'], 'other::Box<long long, 3>')
            self.assertNotEqual(origin['primary_id'], origin['record_id'])
            self.assertEqual([f['name'] for f in callees], ['original_helper'])
            methods = [n for n in record['inner'] if n.get('name') == 'get']
            self.assertTrue(any(c.get('kind') == 'CompoundStmt' for c in methods[0]['inner']))
            require_method_bodies(record)

    def test_missing_constructor_body_cannot_be_silently_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            record, _ = self.materialize(directory, self.definition,
                                        'int instantiate(){other::Box<long long,3> a(7);return a.get();}')
            with self.assertRaisesRegex(ValueError, 'body is not instantiated'):
                require_method_bodies(record)

    def test_common_lowering_checks_missing_bodies(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            source = directory/'source.hpp'
            witness = directory/'instantiate.cpp'
            source.write_text(self.definition)
            witness.write_text('int instantiate(){other::Box<long long,3> a(7);return a.get();}')
            with self.assertRaisesRegex(ValueError, 'body is not instantiated'):
                lower_template_class(source, 'other::Box', TemplateInstance(('long long','3'), witness))

    def test_cleanup_requires_exact_trivial_materialized_record(self):
        with tempfile.TemporaryDirectory() as directory:
            record, _ = self.materialize(directory, self.definition, self.driver)
            cls = ErasedClass(record, _function_class_name(record), _display_name(record))
            eraser = Eraser([cls])
            literal = dict(kind='IntegerLiteral', type={'qualType': 'long long'}, value='1')
            known = dict(kind='MaterializeTemporaryExpr', type={'qualType': 'other::Box<long long, 3>'}, inner=[literal])
            valid = dict(kind='ExprWithCleanups', type={'qualType': 'long long'}, inner=[known])
            self.assertEqual(eraser.transform(valid, None)['kind'], 'MaterializeTemporaryExpr')
            negatives = []
            bad = copy.deepcopy(valid)
            bad['cleanupsHaveSideEffects'] = True
            negatives.append(bad)
            bad = copy.deepcopy(valid)
            bad['inner'][0]['type']['qualType'] = 'other::OtherBox<long long, 3>'
            negatives.append(bad)
            bad = copy.deepcopy(valid)
            bad['inner'][0]['inner'] = [dict(kind='CXXBindTemporaryExpr', inner=[literal])]
            negatives.append(bad)
            negatives.append(dict(valid, inner=[literal]))
            negatives.append(dict(valid, inner=[known, literal]))
            for bad in negatives:
                with self.subTest(node=bad), self.assertRaises(ValueError):
                    eraser.transform(bad, None)

    def test_member_instances_keep_real_ids_and_reject_missing_coverage(self):
        definition = '''namespace other {
template<class T,int N> struct Box {
 T x; Box():x(N){}
 template<class U> U apply(U value)const{return x*value;}
}; }
'''
        driver = '''int instantiate(){other::Box<long long,3> a;
return a.apply<int>(2)+a.apply<long long>(4);}
'''
        with tempfile.TemporaryDirectory() as directory:
            record, _ = self.materialize(directory, definition, driver)
            with self.assertRaisesRegex(ValueError, 'explicit requested instances'):
                require_method_bodies(record)
            selected, ledger = instantiate_members(record, {'apply': [('int',), ('long long',)]})
            require_method_bodies(selected)
            self.assertEqual([r['type_arguments'] for r in ledger], [['int'], ['long long']])
            original = next(n for n in record['inner'] if n.get('kind') == 'FunctionTemplateDecl')
            ids = {n['id'] for n in original['inner'] if n.get('kind') == 'CXXMethodDecl'}
            for entry in ledger:
                self.assertIn(entry['declaration_id'], ids)
                method = next(n for n in selected['inner'] if n.get('id') == entry['declaration_id'])
                body = next(c for c in method['inner'] if c.get('kind') == 'CompoundStmt')
                old = next(n for n in original['inner'] if n.get('id') == method['id'])
                self.assertEqual(body, next(c for c in old['inner'] if c.get('kind') == 'CompoundStmt'))
            for schema in ({}, {'apply': []}, {'apply': [('unsigned int',)]},
                           {'apply': [('float',)]}, {'apply': [('int',), ('int',)]},
                           {'apply': [['int']]}, {'apply': [([],)]},
                           {'apply': [('int',)], 'absent': [('int',)]}):
                with self.subTest(schema=schema), self.assertRaises(ValueError):
                    instantiate_members(record, schema)
            collision = dict(record, inner=record['inner']+[
                {'kind': 'CXXMethodDecl', 'name': 'apply__template_int'}])
            with self.assertRaisesRegex(ValueError, 'name collision'):
                instantiate_members(collision, {'apply': [('int',)]})

    def test_copy_move_assignment_destruction_use_template_target(self):
        for options in ({'copy_assignment': True}, {'move_kind': 'construct'},
                        {'move_kind': 'assign'}, {'class_destruction': True}):
            with self.subTest(options=options), tempfile.TemporaryDirectory() as directory:
                self.materialize(directory, self.definition, self.driver, **options)

    def test_explicit_witness_instantiation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'original forced source|complete specialization'):
                self.materialize(directory, self.definition,
                                 'template struct other::Box<long long,3>;\n'+self.driver)

    def test_included_header_cannot_claim_source_ownership(self):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory)/'dependency.hpp').write_text(self.definition)
            with self.assertRaisesRegex(ValueError, 'original forced source'):
                self.materialize(directory, '#include "dependency.hpp"\n', self.driver)

    def test_alias_canonical_type_must_match_request(self):
        collector = vector_stl.collect_template_record
        def mismatched(stream, source, requested, namespace, witness):
            return collector(stream, source, requested.replace('long long', 'int'), namespace, witness)
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.object(vector_stl, 'collect_template_record', mismatched):
                with self.assertRaisesRegex(ValueError, 'canonical requested specialization mismatch'):
                    self.materialize(directory, self.definition, self.driver)

    def test_invalid_instance_schema(self):
        with tempfile.TemporaryDirectory() as directory:
            witness = Path(directory)/'instantiate.cpp'
            witness.write_text('')
            for args in ((), ['int'], ('int;void injected()',), ('float',),
                         ('01',), ('-1',), (True,), ('int\n',)):
                with self.subTest(arguments=args), self.assertRaises(ValueError):
                    TemplateInstance(args, witness)
            instance = TemplateInstance(('int',), witness)
            with self.assertRaises(ValueError):
                instance.target('other::Box<int>')
            with self.assertRaises(ValueError):
                translation_unit(witness, template_instance=instance)
            unsafe = Path(directory)/'bad"witness.cpp'
            unsafe.write_text('')
            with self.assertRaises(ValueError):
                TemplateInstance(('int',), unsafe)


if __name__ == '__main__':
    disable_network()
    unittest.main()
