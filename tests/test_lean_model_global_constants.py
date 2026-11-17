"""Namespace constants retain declaration identity and reject initialization effects."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends


class GlobalConstantTests(unittest.TestCase):
    def model(self, declarations):
        with tempfile.TemporaryDirectory() as directory:
            header = Path(directory) / 'constants.hpp'
            header.write_text('namespace cp {\n' + declarations + '\n}\n')
            return lean_translate.translate_file(header, [])

    def test_scalar_constants_and_shadowing(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
const int MAX_FAC = 20000003;
constexpr long long NEGATIVE = -17LL;
constexpr unsigned MOD = 4294967291u;
constexpr unsigned long long WIDE = 18446744073709551615ULL;
constexpr bool FLAG = true;
int capacity() { return MAX_FAC; }
int shadow(int MAX_FAC) { return MAX_FAC + cp::MAX_FAC; }
long long negative() { return NEGATIVE; }
unsigned modulus() { return MOD; }
unsigned long long wide() { return WIDE; }
bool flag() { return FLAG; }
}
''', 'call capacity\ncall shadow 9\ncall negative\ncall modulus\ncall wide\ncall flag\n',
            ['ok 20000003', 'ok 20000012', 'ok -17', 'ok 4294967291',
             'ok 18446744073709551615', 'ok 1'])

    def test_reject_mutable_volatile_and_nonliteral_initializers(self):
        for source in ('int value = 7;', 'volatile const int value = 7;',
                       'const int value = 3 + 4;', 'const unsigned value = -1;',
                       'extern const int value;', 'const int value = 7u;',
                       'int source() { return 7; } const int value = source();'):
            with self.subTest(source=source):
                with self.assertRaises(lean_translate.Unsupported):
                    self.model(source)


if __name__ == '__main__':
    unittest.main()
