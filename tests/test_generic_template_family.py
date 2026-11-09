"""The converter's output for monoid_lazy is uniform in T.

For each integer T the public header is re-instantiated, lowered by the common
nested converter, and every generated program is compared with the `Ty`-indexed
family used by the generic proofs (Proofs/GenericLazy.lean) by `rfl`.
This ties the arbitrary-`Ty` theorems to the converter on several concrete T;
it does not, by itself, cover floating-point T or the full object lifetime.
"""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tests'), str(ROOT / 'verifier'), str(ROOT / 'tools')]
import class_copy_layout as layout
from class_templates import TemplateInstance
from nested_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

ORIGINAL = ROOT / 'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
HEADER = ROOT / 'library/algebraic_structure/monoid_lazy.hpp'
# (C++ type, name fragment used by the generator, Lean Ty literal)
TYPES = [('long long', 'long_long', '⟨64, true, false⟩'),
         ('int', 'int', '⟨32, true, false⟩'),
         ('unsigned int', 'unsigned_int', '⟨32, false, false⟩'),
         ('unsigned long long', 'unsigned_long_long', '⟨64, false, false⟩')]
# Each class-layout generation costs ~30 s, so extrema use one signed and one unsigned type of
# different widths (the type-dependent parts are signedness and width).
EXTREMA_TYPES = [t for t in TYPES if t[0] in ('int', 'unsigned long long')]
FAMILY = [('compose_RangeAdd_{s}', 'Proofs.GenericCall.composeAdd'),
          ('RangeSum_{s}_op_x', 'Proofs.GenericLazy.sumOpX'),
          ('RangeSet_{s}_compose_v', 'Proofs.GenericLazy.setComposeV'),
          ('RangeSet_{s}_compose_noop', 'Proofs.GenericLazy.setComposeNoop'),
          ('RangeSet_{s}_applyExtremum', 'Proofs.GenericLazy.setApplyExt'),
          ('RangeSet_{s}_applySumX', 'Proofs.GenericLazy.setApplySum'),
          ('RangeAdd_{s}_new0', 'Proofs.GenericLazy.addNew0'),
          ('RangeAdd_{s}_new1', 'Proofs.GenericLazy.addNew1'),
          ('RangeAdd_{s}_applyExtremum', 'Proofs.GenericLazy.addApplyExt'),
          ('RangeAdd_{s}_applySumX', 'Proofs.GenericLazy.addApplySum')]



class GenericTemplateFamilyTests(unittest.TestCase):
    def test_original_extrema_op_equals_the_ty_selection_family(self):
        """Original `RangeMax`/`RangeMin` friend `op` for both families and every T."""
        disable_network()
        parts, checks, imports = [], [], []
        with tempfile.TemporaryDirectory(prefix='generic-extrema-') as directory:
            count = 0
            for family, witness in [('RangeAddRangeMaxMin', 'original_mixed_add_extrema.cpp'),
                                    ('RangeSetRangeMaxMin', 'original_mixed_set_extrema.cpp')]:
                text = (ROOT / 'tests/imports' / witness).read_text()
                for cpp, _, ty in EXTREMA_TYPES:
                    path = Path(directory) / f'{count}_{witness}'
                    path.write_text(text.replace('long long', cpp))
                    for kind, indices in [('RangeMax', '0 1'), ('RangeMin', '1 0')]:
                        instance = TemplateInstance((cpp,), path, nested_members=(kind,))
                        generated = layout.emit_class_layout(ORIGINAL, family, 'OriginalExtremaObject',
                            [ROOT / 'experiments/library/cpp'], member_exports=True, factory_exports=True,
                            friend_exports=True, template_instance=instance)
                        namespace = f'Ext{count}'
                        count += 1
                        lines = generated.replace('OriginalExtremaObject', namespace).split('\n')
                        imports = imports or [line for line in lines if line.startswith('import')]
                        parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                        checks.append(f'example : {namespace}.«{kind}_factory_op».body = '
                                      f'Proofs.GenericExtrema.selectionBody {ty} {indices} := rfl')
                        # The generic call theorems live beside this instance's own generated
                        # MemberView/MemberFactory helpers and are tied to its exports by rfl.
                        fixture = (ROOT / 'tests/lean/generic_extrema_object_call.lean').read_text()
                        names = [line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
                        group = f'GenericExtremaCall{count}'
                        parts.append(fixture.replace('OriginalExtremaObject', namespace)
                                     .replace('GenericExtremaCall', group))
                        checks.append(f'example : {namespace}.«{kind}_factory_op_exportViewFuel» = '
                                      f'{group}.gView {ty} {indices.split()[0]} {indices.split()[1]} := rfl')
                        checks.append(f'example : {namespace}.«{kind}_factory_op_exportObjectsFuel» = '
                                      f'{group}.gCombine {ty} {indices.split()[0]} {indices.split()[1]} := rfl')
                        limit = ('Proofs.GenericExtrema.lowestV' if kind == 'RangeMax'
                                 else 'Proofs.GenericExtrema.highestV') + f' {ty}'
                        for program, body, slot in [('factory_e', 'identBody', 1), ('construct1', 'ctorBody', 2)]:
                            generic = f'{group}.gNullary {ty} (Proofs.GenericExtrema.{body} {ty} ({limit}))'
                            checks.append(f'example : {namespace}.«{kind}_{program}» = {generic} := rfl')
                            checks.append(f'example : {namespace}.«{kind}_{program}_exportViewFuel» = '
                                          f'{group}.gNullaryView {ty} (Proofs.GenericExtrema.{body} {ty} ({limit})) {slot} := rfl')
                        checks.extend(f'#print axioms {group}.{name}' for name in names)
            lean = Path(directory) / 'extrema.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.MonoidLazyCall\nimport Proofs.CppScalarContents\nimport Proofs.GenericExtrema\nopen Proofs.CppScalar\n' +
                            '\n'.join(parts) + '\n' + '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout[:3000] + result.stderr[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        self.assertNotIn('Lean.ofReduceBool', result.stdout)
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 100)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)

    def test_generated_programs_equal_the_ty_family(self):
        disable_network()
        source = HEADER.read_text()
        parts, checks = ['import Proofs.GenericLazy'], []
        with tempfile.TemporaryDirectory(prefix='generic-family-') as directory:
            for index, (cpp, fragment, ty) in enumerate(TYPES):
                path = Path(directory) / f'monoid_lazy_{index}.hpp'
                path.write_text(source.replace('long long', cpp))
                namespace = f'Proofs.GenFamily{index}'
                text = emit_lean(lower_source(path, [HEADER.parent]), namespace)
                parts.append('\n'.join(line for line in text.split('\n')
                                       if not line.startswith('import') and not line.startswith('--')))
                for name, family in FAMILY:
                    checks.append(f'example : {family} {ty} = {namespace}.«{name.format(s=fragment)}» := rfl')
            parts.append('open Proofs.CppScalar')
            parts.extend(checks)
            lean = Path(directory) / 'family.lean'
            lean.write_text('\n'.join(parts) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)



if __name__ == '__main__':
    unittest.main()
