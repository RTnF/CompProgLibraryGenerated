"""Public common bridge must reject changes even after a hash update."""

import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from state_bridge import check_source
from state_ir import lower_source, emit_lean
from offline import disable_network


class BridgeTests(unittest.TestCase):
    def test_signed_conversion_policy_is_explicit_and_part_of_the_model(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.cpp"
            source.write_text('namespace cp {long f(unsigned long x){return x;}}')
            metadata = {"source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        "public_declarations": ["FunctionDecl:f"], "lean_namespace": "Proofs.Test",
                        "signed_conversion": "gcc13.3-lp64-twos-complement"}
            model = emit_lean(lower_source(source, signed_conversion=metadata['signed_conversion']),
                              metadata['lean_namespace'])
            check_source(source, metadata, model)
            metadata['signed_conversion'] = 'checked'
            with self.assertRaisesRegex(ValueError, 'generated Lean mismatch'):
                check_source(source, metadata, model)
            metadata['signed_conversion'] = 'unreviewed-target'
            with self.assertRaisesRegex(ValueError, 'unsupported signed conversion'):
                check_source(source, metadata, model)

    def test_regeneration_and_declaration_checks_do_not_use_hash_for_semantics(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.cpp"
            original = 'namespace cp {int f(int a,int b){a+=b;return a;}}'
            source.write_text(original)
            metadata = {"source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        "public_declarations": ["FunctionDecl:f"], "lean_namespace": "Proofs.Test"}
            model = emit_lean(lower_source(source), metadata["lean_namespace"])
            check_source(source, metadata, model)
            source.write_text(original.replace('a+=b','a-=b'))
            with self.assertRaisesRegex(RuntimeError, "source changed"):
                check_source(source, metadata, model)
            metadata["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "generated Lean mismatch"):
                check_source(source, metadata, model)
            regenerated = emit_lean(lower_source(source), metadata["lean_namespace"])
            self.assertNotEqual(regenerated, model)
            check_source(source, metadata, regenerated)
            source.write_text(original + '\nnamespace cp {int extra(){return 0;}}')
            metadata["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaisesRegex(RuntimeError, "public declarations changed"):
                check_source(source, metadata, model)

    def test_unsupported_declarations_and_partial_templates_are_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.cpp"
            source.write_text('namespace cp {int f(int a){return a<<1;}}')
            metadata = {"source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        "public_declarations": ["FunctionDecl:f"], "lean_namespace": "Proofs.Test"}
            with self.assertRaisesRegex(ValueError, "unsupported expression|bitwise operators are supported"):
                check_source(source, metadata, '')
            # A function template is a public declaration of its own kind: a registry that lists it as a plain
            # function is refused before lowering.
            source.write_text('namespace cp {template<class T>T f(T a){return a;}}')
            metadata["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaisesRegex(RuntimeError, "public declarations changed"):
                check_source(source, metadata, '')


if __name__ == "__main__":
    disable_network()
    unittest.main()
