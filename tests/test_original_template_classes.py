"""Regenerate original library3 scalar instances and independently check proofs.

This is finite-instance coverage; the C++ originals retain their generic API.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tests'), str(ROOT/'verifier'), str(ROOT/'tools')]
from class_templates import TemplateInstance
from template_class_ir import lower_template_class
from nested_ir import emit_lean
from offline import disable_network
import test_scalar_class_delegation as scalar_checks


class OriginalTemplateTests(unittest.TestCase):
    def check_case(self, case, name, header, count, expected):
        source = ROOT/'experiments/library3/cpp/AlgebraicStructure'/header
        witness = ROOT/'tests/imports'/('original_'+case+'.cpp')
        includes = [ROOT/'experiments/library3/cpp']
        digests = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source, witness)}
        ir, coverage = lower_template_class(source, name, TemplateInstance(('long long',), witness),
            includes, member_instances={'apply': [('long long',), ('int',)]} if case == 'mapping' else {},
            signed_conversion='gcc13.3-lp64-twos-complement' if case == 'mapping' else 'checked')
        self.assertEqual(len(ir['functions']), count)
        self.assertEqual(coverage['models'], [p['name'] for p in ir['functions']])
        self.assertEqual(coverage['source_sha256'], digests[source])
        self.assertEqual(coverage['witness_sha256'], digests[witness])
        self.assertFalse(coverage['generic_types_verified'])
        self.assertFalse(coverage['full_cpp_object_lifetime_verified'])
        roots = []
        proof = 'import Proofs.GroupCall\nimport Proofs.CppTargetCast\n'+emit_lean(ir, 'Original_'+case)
        namespace = 'OriginalEquivalence_'+case
        proof += '\nnamespace '+namespace+'\nopen Proofs.CppNestedProgram Proofs.CppNestedCall\n'
        if case == 'sum':
            pairs = [(op, 'Original_sum.GroupSum_long_long_'+op,
                      'Proofs.GroupInstance.GroupSum_long_long_'+op) for op in ('new0','new1','e','op')]
        else:
            ops = ('ide','inv','new0','new1','compose') if case == 'mapping' else ('e','inv','new0','new1','op')
            cls = 'Affine' if case == 'mapping' else 'GroupAffine'
            pairs = [(op+'_'+field, 'Original_'+case+'.'+cls+'_long_long_'+op+'_'+field,
                      'Proofs.GroupInstance.GroupAffine_long_long_'+
                      {'ide':'e','compose':'op_friend','op':'op_friend'}.get(op,op)+'__'+field)
                     for op in ops for field in ('a','b')]
        for theorem, original, modern in pairs:
            proof += '\ntheorem '+theorem+' : '+original+' = '+modern+' := by rfl\n'
            proof += 'theorem call_'+theorem+' (fuel : Nat) (caller : NState) (args : List NArgument) :\n'+\
                     original+'.callFuel fuel caller args = '+modern+'.callFuel fuel caller args :=\n'+\
                     'congrArg (fun p : NProgram => p.callFuel fuel caller args) '+theorem+'\n'
            roots.extend([namespace+'.'+theorem, namespace+'.call_'+theorem])
        proof += '\nend '+namespace+'\n'
        if case == 'sum':
            proof += (ROOT/'tests/lean/original_sum.lean').read_text()
            roots.extend(['OriginalSumAudit.inv_exec', 'OriginalSumAudit.inv_correct'])
        elif case == 'mapping':
            proof += (ROOT/'tests/lean/original_mapping.lean').read_text()
            proof += (ROOT/'tests/lean/original_mapping_int.lean').read_text()
            roots.extend(['OriginalMappingAudit.apply_value_correct', 'OriginalMappingIntAudit.apply_int_correct'])
            self.assertEqual(coverage['member_instances'], [
                dict(source_name='apply', type_arguments=['long long']),
                dict(source_name='apply', type_arguments=['int'])])
        with tempfile.TemporaryDirectory(prefix='original-template-') as directory:
            directory = Path(directory)
            scalar_checks.ScalarDelegationTests().kernel(directory, 'OriginalTemplateCheck', roots, proof)
            executable = directory/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(includes[0]),'-include',str(source),str(witness),'-o',str(executable)], check=True)
            result = subprocess.run([str(executable)], check=True, capture_output=True, text=True)
            self.assertEqual(result.stdout, expected+'\n')
        for path, digest in digests.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), digest)

    def test_original_sum(self):
        self.check_case('sum','GroupSum','Group.hpp',5,'0 -4 7 9')

    def test_original_affine_group(self):
        self.check_case('group_affine','GroupAffine','Group.hpp',10,'1 0 6 7 1 -4')

    def test_original_mapping_value_types(self):
        self.check_case('mapping','Affine','Mapping.hpp',12,'1 0 7 7 2 6 7 1 -4')


if __name__ == '__main__':
    disable_network()
    unittest.main()
