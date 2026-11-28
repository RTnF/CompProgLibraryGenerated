"""Public Ratio source, canonical proof, and frontend regression fixtures."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_ratio_stream_model as reference
import test_lean_model_friend as friend_tests
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()

SOURCE = ROOT / 'library/number/ratio.hpp'


class RatioEuclidTests(unittest.TestCase):
    def test_only_numeric_helpers_and_calls_change(self):
        base = reference.CANDIDATE.read_text().replace(
            "// Standard-library reference fixture for frontend regression tests.\n", "")
        helpers = (ROOT / 'tests/fixtures/ratio_numeric.hpp').read_text()
        helpers = helpers.split('namespace cp {\n', 1)[1].split('} // namespace cp', 1)[0]
        helpers = helpers.replace('template <typename T> T ratio_', 'static T numeric_')
        helpers = helpers.replace('ratio_gcd', 'numeric_gcd')
        expected = base.replace('#include <numeric>\n', '')
        expected = expected.replace('  // n / d\n', helpers + '\n  // n / d\n')
        expected = expected.replace('std::gcd(', 'numeric_gcd(').replace('std::lcm(', 'numeric_lcm(')
        self.assertEqual(SOURCE.read_text(), expected)

    def test_fresh_helpers_and_stream_proofs(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++23')
        canonical = (ROOT / 'Proofs/Cpp/Ratio.lean').read_text()
        imports = [line for line in canonical.splitlines() if line.startswith('import ')
                   and line != 'import Proofs.Cpp.Gen.Ratio']
        contracts = '\n'.join(line for line in canonical.splitlines() if not line.startswith('import '))
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / 'Proof.lean'
            proof.write_text('\n'.join(imports) + '\n' + model + contracts)
            result = subprocess.run([LAKE, 'env', 'lean', str(proof)],
                                    cwd=ROOT, env=LAKE_ENV,
                                    capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_static_member_identity_with_same_named_free_function(self):
        friend_tests.FriendTranslationTests().compare(
            """#pragma once
namespace cp {
template <typename T> T helper(T x) { return x + 100; }
template <typename T> class Box {
  T value;
  static T helper(T x) { return x + 1; }
public:
  Box(T x) : value(x) {}
  T get() const { return helper(value); }
};
}
""", 'new Box.init 7\ndo Box.get_ 0\ncall helper 7\n',
            ['new', 'ok 8', 'ok 107'])
        # A different declaration with that spelling must never call Box.helper.
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'foreign.hpp'
            source.write_text("""#pragma once
namespace cp {
struct Other { static int helper(int x) { return x + 100; } };
template <typename T> class Box {
  T value;
  static T helper(T x) { return x + 1; }
public:
  Box(T x) : value(x) {}
  T get() const { return Other::helper(7); }
};
}
""")
            with self.assertRaisesRegex(lean_translate.Unsupported, 'static member declaration outside'):
                lean_translate.translate_file(source, [])

    def test_public_arithmetic_against_fraction(self):
        class CandidateArithmetic(friend_tests.FriendTranslationTests):
            def compare(self, header, cases, expected_values, standard="c++23"):
                super().compare(SOURCE.read_text(), cases, expected_values, standard=standard)
        CandidateArithmetic().test_original_ratio_arithmetic_translation()

    def test_public_stream_and_standalone(self):
        # Reuse the same independent native/Lean expectations for both candidates.
        case = reference.RatioStreamModelTests()
        with patch.object(reference, 'CANDIDATE', SOURCE):
            case.test_candidate_standalone_include_and_default_type()
            case.test_generic_harness_stream_arguments_and_object_writeback()


if __name__ == '__main__':
    unittest.main()
