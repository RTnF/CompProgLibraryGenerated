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
from class_templates import TemplateInstance, RecordArgument
import re
from nested_ir import lower_source, emit_lean
from template_class_ir import lower_template_class
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
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
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


    def test_original_extrema_add_apply_equals_the_ty_family(self):
        """`RangeAdd::apply` on `RangeMax`/`RangeMin` for every T (family and export views)."""
        disable_network()
        parts, checks, imports = [], [], []
        fixture = (ROOT / 'tests/lean/generic_extrema_add_apply.lean').read_text()
        prepare = (ROOT / 'tests/lean/original_extrema_member_prepare.lean').read_text()
        split_at = fixture.index('namespace GenericAddApplyCall')
        raw_names = [line.split()[1] for line in fixture[:split_at].splitlines() if line.startswith('theorem ')]
        names = [line.split()[1] for line in fixture[split_at:].splitlines() if line.startswith('theorem ')]
        prepare_names = [line.split()[1] for line in prepare.splitlines() if line.startswith('theorem ')]
        with tempfile.TemporaryDirectory(prefix='generic-add-apply-') as directory:
            count = 0
            text = (ROOT / 'tests/imports/original_mixed_add_extrema.cpp').read_text()
            for cpp, _, ty in EXTREMA_TYPES:
                path = Path(directory) / f'witness_{count}.cpp'
                path.write_text(text.replace('long long', cpp))
                for kind in ('RangeMax', 'RangeMin'):
                    instance = TemplateInstance((cpp,), path, nested_members=(kind,))
                    receiver = TemplateInstance((cpp,), path, nested_members=('RangeAdd',))
                    generated = layout.emit_class_layout(ORIGINAL, 'RangeAddRangeMaxMin', 'TemplateMemberResult',
                        [ROOT / 'experiments/library/cpp'], member_exports=True, factory_exports=True,
                        template_instance=instance, companion_instances=(('RangeAddRangeMaxMin', receiver),),
                        receiver_methods=((1, 'apply', (RecordArgument(0),)),))
                    namespace = f'Apply{count}'
                    lines = generated.replace('TemplateMemberResult', namespace).split('\n')
                    imports = imports or [line for line in lines if line.startswith('import')]
                    parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                    program = re.search(r'^def «(' + kind + r'_factory_receiver1_apply[^»]*)» : NProgram',
                                        '\n'.join(lines), re.M).group(1)
                    group = f'GenericAddApplyCall{count}'
                    raw = f'GenericAddApplyRaw{count}'
                    prep = f'ExtremaPrepareGeneral{count}'
                    parts.append(prepare.replace('ExtremaPrepareGeneral', prep))
                    parts.append(fixture.replace('TemplateMemberResult', namespace)
                                 .replace('GenericAddApplyRaw', raw).replace('GenericAddApplyCall', group)
                                 .replace('open ExtremaPrepareGeneral', f'open {prep}'))
                    checks.append(f'example : {namespace}.«{program}» = {group}.gApply {ty} := rfl')
                    checks.append(f'example : {namespace}.«{program}_exportViewFuel» = {group}.gApplyView {ty} := rfl')
                    checks.append(f'example : {namespace}.«{program}_exportObjectsFuel» = {group}.gApplyObjects {ty} := rfl')
                    checks.extend(f'#print axioms {group}.{name}' for name in names)
                    checks.extend(f'#print axioms {raw}.{name}' for name in raw_names)
                    checks.extend(f'#print axioms {prep}.{name}' for name in prepare_names)
                    count += 1
            lean = Path(directory) / 'apply.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.MonoidLazyCall\nimport Proofs.CppScalarValuePrepare\n'
                            'import Proofs.CppScalarContents\nopen Proofs.CppScalar\n' + '\n'.join(parts) + '\n' +
                            '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 40)
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)

    def test_original_extrema_set_apply_equals_the_ty_family(self):
        """`RangeSet::apply` on `RangeMax`/`RangeMin` for every T (family and export views)."""
        disable_network()
        parts, checks, imports = [], [], []
        fixture = (ROOT / 'tests/lean/generic_extrema_set_apply.lean').read_text()
        prepare = (ROOT / 'tests/lean/original_extrema_member_prepare.lean').read_text()
        split_at = fixture.index('namespace GenericSetApplyCall')
        raw_names = [line.split()[1] for line in fixture[:split_at].splitlines() if line.startswith('theorem ')]
        names = [line.split()[1] for line in fixture[split_at:].splitlines() if line.startswith('theorem ')]
        prepare_names = [line.split()[1] for line in prepare.splitlines() if line.startswith('theorem ')]
        with tempfile.TemporaryDirectory(prefix='generic-set-apply-') as directory:
            count = 0
            text = (ROOT / 'tests/imports/original_mixed_set_extrema.cpp').read_text()
            for cpp, _, ty in EXTREMA_TYPES:
                path = Path(directory) / f'witness_{count}.cpp'
                path.write_text(text.replace('long long', cpp))
                for kind in ('RangeMax', 'RangeMin'):
                    instance = TemplateInstance((cpp,), path, nested_members=(kind,))
                    receiver = TemplateInstance((cpp,), path, nested_members=('RangeSet',))
                    generated = layout.emit_class_layout(ORIGINAL, 'RangeSetRangeMaxMin', 'TemplateMemberResult',
                        [ROOT / 'experiments/library/cpp'], member_exports=True, factory_exports=True,
                        template_instance=instance, companion_instances=(('RangeSetRangeMaxMin', receiver),),
                        receiver_methods=((1, 'apply', (RecordArgument(0),)),))
                    namespace = f'Apply{count}'
                    lines = generated.replace('TemplateMemberResult', namespace).split('\n')
                    imports = imports or [line for line in lines if line.startswith('import')]
                    parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                    program = re.search(r'^def «(' + kind + r'_factory_receiver1_apply[^»]*)» : NProgram',
                                        '\n'.join(lines), re.M).group(1)
                    group = f'GenericSetApplyCall{count}'
                    raw = f'GenericSetApplyRaw{count}'
                    prep = f'ExtremaPrepareGeneral{count}'
                    parts.append(prepare.replace('ExtremaPrepareGeneral', prep))
                    parts.append(fixture.replace('TemplateMemberResult', namespace)
                                 .replace('GenericSetApplyRaw', raw).replace('GenericSetApplyCall', group)
                                 .replace('open ExtremaPrepareGeneral', f'open {prep}'))
                    checks.append(f'example : {namespace}.«{program}» = {group}.gApply {ty} := rfl')
                    checks.append(f'example : {namespace}.«{program}_exportViewFuel» = {group}.gApplyView {ty} := rfl')
                    checks.append(f'example : {namespace}.«{program}_exportObjectsFuel» = {group}.gApplyObjects {ty} := rfl')
                    checks.extend(f'#print axioms {group}.{name}' for name in names)
                    checks.extend(f'#print axioms {raw}.{name}' for name in raw_names)
                    checks.extend(f'#print axioms {prep}.{name}' for name in prepare_names)
                    count += 1
            lean = Path(directory) / 'apply.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.GenericLazy\nimport Proofs.MonoidLazyCall\nimport Proofs.CppScalarValuePrepare\n'
                            'import Proofs.CppScalarContents\nopen Proofs.CppScalar\n' + '\n'.join(parts) + '\n' +
                            '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 40)
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)


    def test_original_set_record_constructors_equal_the_ty_family(self):
        """`RangeSet` value/default constructors and `id()` for every T, in both families."""
        disable_network()
        parts, checks, imports = [], [], []
        fixture = (ROOT / 'tests/lean/generic_set_record_ctor.lean').read_text()
        names = [line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
        with tempfile.TemporaryDirectory(prefix='generic-set-ctor-') as directory:
            count = 0
            for family, kind in [('RangeSetRangeMaxMin', 'set_extrema'), ('RangeSetRangeSum', 'set_sum')]:
                text = (ROOT / 'tests/imports' / f'original_mixed_{kind}.cpp').read_text()
                for cpp, _, ty in EXTREMA_TYPES:
                    path = Path(directory) / f'witness_{count}.cpp'
                    path.write_text(text.replace('long long', cpp))
                    instance = TemplateInstance((cpp,), path, nested_members=('RangeSet',))
                    generated = layout.emit_class_layout(ORIGINAL, family, 'ValueObject',
                        [ROOT / 'experiments/library/cpp'], member_exports=True, factory_exports=True,
                        template_instance=instance)
                    namespace = f'Ctor{count}'
                    group = f'GenericSetCtor{count}'
                    lines = generated.replace('ValueObject', namespace).split('\n')
                    imports = imports or [line for line in lines if line.startswith('import')]
                    parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                    parts.append(fixture.replace('open ValueObject', f'open {namespace}')
                                 .replace('GenericSetCtor', group))
                    for generated_name, mode in [('RangeSet_construct0', 'Mode.value'),
                                                 ('RangeSet_construct1', 'Mode.defaulted'),
                                                 ('RangeSet_factory_id', 'Mode.identity')]:
                        checks.append(f'example : {namespace}.«{generated_name}» = {group}.program {ty} {group}.{mode} := rfl')
                        checks.append(f'example : {namespace}.«{generated_name}_exportViewFuel» = {group}.view {ty} {group}.{mode} := rfl')
                    checks.extend(f'#print axioms {group}.{name}' for name in names)
                    count += 1
            lean = Path(directory) / 'ctor.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.GenericLazy\nimport Proofs.MonoidLazyCall\n'
                            'import Proofs.CppScalarContents\nimport Proofs.CppScalarValuePrepare\n'
                            'import Proofs.CppFrameResolveExtension\nopen Proofs.CppScalar\n' +
                            '\n'.join(parts) + '\n' + '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 80)
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)


    def test_original_scalar_record_constructors_and_id_equal_the_ty_family(self):
        """One-field records (`RangeAdd`, `RangeMax`, `RangeMin`): value constructor and `RangeAdd::id()`."""
        disable_network()
        parts, checks, imports = [], [], []
        ctor = (ROOT / 'tests/lean/generic_scalar_record_ctor.lean').read_text()
        zero = (ROOT / 'tests/lean/generic_scalar_record_zero.lean').read_text()
        ctor_names = [line.split()[1] for line in ctor.splitlines() if line.startswith('theorem ')]
        zero_names = [line.split()[1] for line in zero.splitlines() if line.startswith('theorem ')]
        cases = [('RangeAddRangeMaxMin', 'add_extrema', 'RangeAdd'),
                 ('RangeSetRangeMaxMin', 'set_extrema', 'RangeMax'),
                 ('RangeAddRangeSum', 'add_sum', 'RangeAdd')]
        with tempfile.TemporaryDirectory(prefix='generic-scalar-ctor-') as directory:
            count = 0
            for family, kind, record in cases:
                text = (ROOT / 'tests/imports' / f'original_mixed_{kind}.cpp').read_text()
                for cpp, _, ty in EXTREMA_TYPES:
                    path = Path(directory) / f'witness_{count}.cpp'
                    path.write_text(text.replace('long long', cpp))
                    instance = TemplateInstance((cpp,), path, nested_members=(record,))
                    generated = layout.emit_class_layout(ORIGINAL, family, 'ValueObject',
                        [ROOT / 'experiments/library/cpp'], member_exports=True, factory_exports=True,
                        template_instance=instance)
                    namespace = f'Scalar{count}'
                    ctor_group, zero_group = f'GenericScalarCtor{count}', f'GenericScalarZero{count}'
                    lines = generated.replace('ValueObject', namespace).split('\n')
                    imports = imports or [line for line in lines if line.startswith('import')]
                    parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                    parts.append(ctor.replace('open ValueObject', f'open {namespace}').replace('GenericScalarCtor', ctor_group))
                    checks.append(f'example : {namespace}.«{record}_construct0» = {ctor_group}.program {ty} := rfl')
                    checks.append(f'example : {namespace}.«{record}_construct0_exportViewFuel» = {ctor_group}.view {ty} := rfl')
                    checks.extend(f'#print axioms {ctor_group}.{name}' for name in ctor_names)
                    if record == 'RangeAdd':
                        parts.append(zero.replace('open ValueObject', f'open {namespace}')
                                     .replace('GenericScalarZero', zero_group).replace('GenericScalarCtor', ctor_group))
                        checks.append(f'example : {namespace}.«RangeAdd_factory_id» = {zero_group}.program {ty} := rfl')
                        checks.append(f'example : {namespace}.«RangeAdd_factory_id_exportViewFuel» = {zero_group}.view {ty} := rfl')
                        checks.extend(f'#print axioms {zero_group}.{name}' for name in zero_names)
                    count += 1
            lean = Path(directory) / 'scalar.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.GenericLazy\nimport Proofs.MonoidLazyCall\n'
                            'import Proofs.CppScalarContents\nimport Proofs.CppScalarValuePrepare\n'
                            'import Proofs.CppFrameResolveExtension\nopen Proofs.CppScalar\n' +
                            '\n'.join(parts) + '\n' + '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 60)
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)


    def test_original_set_sum_transferred_programs_equal_the_ty_family(self):
        """The field-projection models of the original `RangeAddRangeSum`/`RangeSetRangeSum`."""
        disable_network()
        copy_fields = (ROOT / 'tests/lean/scalar_record_copy_fields.lean').read_text()
        # (fixture, group, [(namespace key, generated program, family expression)])
        fixtures = [
            ('generic_add_sum.lean', 'GenericAddSum', [
                ('add', 'RangeAdd_apply_x', 'gApply {ty} false'), ('add', 'RangeAdd_apply_size', 'gApply {ty} true'),
                ('add', 'RangeSum_e_x', 'gE {ty} false'), ('add', 'RangeSum_e_size', 'gE {ty} true'),
                ('add', 'RangeSum_new1_x', 'gNew1 {ty} false'), ('add', 'RangeSum_new1_size', 'gNew1 {ty} true'),
                ('add', 'RangeSum_new0_x', 'gNew0 {ty} false'), ('add', 'RangeSum_new0_size', 'gNew0 {ty} true'),
                ('add', 'RangeSum_op_x', 'gOp {ty} false'), ('add', 'RangeSum_op_size', 'gOp {ty} true'),
                ('add', 'RangeAdd_compose', 'gCompose {ty}')]),
            ('generic_set_value_ctor.lean', 'GenericSetValueCtor', [
                ('set', 'RangeSet_new0_v', 'gNew0 {ty} false'), ('set', 'RangeSet_new0_noop', 'gNew0 {ty} true')])]
        parts, checks, imports = [], [], []
        with tempfile.TemporaryDirectory(prefix='generic-set-sum-') as directory:
            count = 0
            for cpp, _, ty in EXTREMA_TYPES:
                namespaces = {}
                for key, family, witness, record, companion in [
                        ('add', 'RangeAddRangeSum', 'original_mixed_add_sum.cpp', 'RangeAdd', 'RangeSum'),
                        ('set', 'RangeSetRangeSum', 'original_mixed_set_sum.cpp', 'RangeSet', 'RangeSum')]:
                    path = Path(directory) / f'{key}_{count}.cpp'
                    path.write_text((ROOT / 'tests/imports' / witness).read_text().replace('long long', cpp))
                    ir, _ = lower_template_class(ORIGINAL, family,
                        TemplateInstance((cpp,), path, nested_members=(record,)), [ROOT / 'experiments/library/cpp'],
                        companion_instances=((family, TemplateInstance((cpp,), path, nested_members=(companion,))),))
                    prefix = 'OriginalMixedAddSum' if key == 'add' else 'OriginalSetSum'
                    namespaces[key] = f'{prefix}{count}'
                    lines = emit_lean(ir, prefix).replace(prefix, namespaces[key]).split('\n')
                    imports = imports or [line for line in lines if line.startswith('import')]
                    parts.append('\n'.join(line for line in lines if not line.startswith('import')))
                parts.append(copy_fields.replace('CopiedScalarFieldsAudit', f'CopiedScalarFieldsAudit{count}'))
                for name, group, programs in fixtures:
                    fixture = (ROOT / 'tests/lean' / name).read_text()
                    theorem_names = [line.split()[1] for line in fixture.splitlines() if line.startswith('theorem ')]
                    renamed = group + str(count)
                    parts.append(fixture.replace(group, renamed)
                                 .replace('CopiedScalarFieldsAudit', f'CopiedScalarFieldsAudit{count}'))
                    for key, generated, family in programs:
                        checks.append(f'example : {namespaces[key]}.«{generated}» = {renamed}.{family.format(ty=ty)} := rfl')
                    checks.extend(f'#print axioms {renamed}.{theorem}' for theorem in theorem_names)
                count += 1
            lean = Path(directory) / 'sum.lean'
            lean.write_text('\n'.join(imports) + '\nimport Proofs.GenericLazy\nimport Proofs.MonoidLazyCall\n'
                            'open Proofs.CppScalar\n' + '\n'.join(parts) + '\n' + '\n'.join(checks) + '\n')
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        errors = '\n'.join(line for line in (result.stdout + result.stderr).splitlines() if 'error' in line)
        self.assertEqual(result.returncode, 0, errors[:3000])
        self.assertNotIn('sorryAx', result.stdout)
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        reports = [line for line in result.stdout.splitlines() if 'axioms' in line]
        self.assertGreater(len(reports), 20)
        for line in reports:
            if line.endswith('does not depend on any axioms'):
                continue
            used = {name.strip() for name in line.split('depends on axioms: [', 1)[1].rstrip(']').split(',')}
            self.assertLessEqual(used, standard, line)



if __name__ == '__main__':
    unittest.main()
