"""Concrete formatted I/O keeps the C++ overload identity, not only its carrier."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()

HEADER = '''#pragma once
#include <iostream>
#include <cstdint>
namespace cp {
std::istream& read32(std::istream& input, int& x) { input >> x; return input; }
std::istream& readlong(std::istream& input, long& x) { input >> x; return input; }
std::istream& read64(std::istream& input, long long& x) { input >> x; return input; }
std::istream& readu32(std::istream& input, uint32_t& x) { input >> x; return input; }
std::ostream& write32(std::ostream& output, uint32_t x) { output << x; return output; }
struct Word {
  uint32_t x;
  Word(uint32_t value) : x(value % 7u) {}
  void set(long value) { x = (value % 7 + 7) % 7; }
  friend std::istream& operator>>(std::istream& input, Word& value) {
    int64_t temporary = 0;
    input >> temporary;
    value.set(temporary);
    return input;
  }
  friend std::ostream& operator<<(std::ostream& output, const Word& value) {
    output << value.x;
    return output;
  }
};
}
'''


class SourceStreamTests(unittest.TestCase):
    def model(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Source.hpp'
            source.write_text(HEADER)
            return lean_translate.translate_file(source, [])

    def test_overload_tags_distinguish_long_from_long_long(self):
        model = self.model()
        for source in ('int', 'long', 'long_long'):
            self.assertIn(f'Cpp.SourceStreamRead "{source}" Int', model)
        self.assertIn('Cpp.SourceStreamWrite "unsigned_int" UInt32', model)

    def test_arbitrary_stream_states_and_costs_contract(self):
        model = self.model()
        contract = (ROOT / 'tests/lean/source_stream_contract.lean').read_text()
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.source-contract-') as directory:
            lean = Path(directory) / 'Contract.lean'
            lean.write_text(model + contract)
            subprocess.run([LAKE, 'env', 'lean', str(lean)],
                           check=True, cwd=ROOT, timeout=60,
                           env=LAKE_ENV)

    def test_numeric_boundaries_and_class_streams(self):
        commands = ['call read32 1 1099511627776 0',
                    'call readlong 1 1099511627776 0',
                    'call read64 1 1099511627776 0',
                    'call readu32 1 -1 0',
                    'new Word.init 3',
                    'call op_shr_istream_Word 0 0',
                    'field Word.x 0',
                    'call op_shl_ostream_Word 0',
                    'call op_shr_istream_Word 1 -14 0',
                    'field Word.x 0',
                    'call write32 4294967295']
        def encoded(text):
            return ' ' + ' '.join([str(len(text)), *map(lambda c: str(ord(c)), text)])
        expected = ['ok 1 1 1 1 2147483647',
                    'ok 1 0 1 0 1099511627776',
                    'ok 1 0 1 0 1099511627776',
                    'ok 1 0 1 0 4294967295',
                    'new', 'ok 1 1 1 1 objref', 'ok 0',
                    'ok' + encoded('0') * 2,
                    'ok 1 0 1 0 objref', 'ok 0',
                    'ok' + encoded('4294967295') * 2]
        friends.FriendTranslationTests().compare(HEADER, '\n'.join(commands)+'\n', expected,
            instance={'T': 'long long', 'U': 'unsigned long long'})


if __name__ == '__main__':
    unittest.main()
