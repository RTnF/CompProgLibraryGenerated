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
from nested_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

HEADER = ROOT / 'library/algebraic_structure/monoid_lazy.hpp'
# (C++ type, name fragment used by the generator, Lean Ty literal)
TYPES = [('long long', 'long_long', '⟨64, true, false⟩'),
         ('int', 'int', '⟨32, true, false⟩'),
         ('unsigned', 'unsigned_int', '⟨32, false, false⟩'),
         ('unsigned long long', 'unsigned_long_long', '⟨64, false, false⟩')]
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
