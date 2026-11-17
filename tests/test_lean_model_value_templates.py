"""Integral non-type parameters remain values in generated classes and calls."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends


class ValueTemplateTests(unittest.TestCase):
    def model(self, header):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'value.hpp'
            source.write_text(header)
            return lean_translate.translate_file(source, [])

    def test_unsigned_class_and_free_function(self):
        header = '''#pragma once
namespace cp {
template<unsigned N> struct Counter {
  unsigned x;
  Counter(unsigned value) : x(value + N) {}
  unsigned get() const { return x + N; }
};
template<unsigned M> unsigned offset(unsigned value) { return value + M; }
}
'''
        for n, m in ((0, 0), (7, 11), (2**32-1, 2**32-1)):
            with self.subTest(n=n, m=m):
                friends.FriendTranslationTests().compare(header,
                    'new Counter.init 3\nfield Counter.x 0\ndo Counter.get_ 0\ncall offset 5\n',
                    ['new', f'ok {(3+n) % 2**32}', f'ok {(3+2*n) % 2**32}',
                     f'ok {(5+m) % 2**32}'], instance={'N': str(n)+'u', 'M': str(m)+'u'})

    def test_signed_boolean_and_mixed_parameters(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<long long Delta> struct Shift {
  long long x;
  Shift(long long value) : x(value + Delta) {}
  long long get() const { return x - Delta; }
};
template<bool B> struct Flag {
  bool x;
  Flag() : x(B) {}
};
template<class T, unsigned N> struct Tagged {
  T x;
  Tagged(T value) : x(value) {}
  unsigned key() const { return N; }
};
}
''', 'new Shift.init 3\nfield Shift.x 0\ndo Shift.get_ 0\nnew Flag.init\n'
     'field Flag.x 0\nnew Tagged.init 12\nfield Tagged.x 0\ndo Tagged.key 0\n',
            ['new', 'ok -4', 'ok 3', 'new', 'ok 0', 'new', 'ok 12', 'ok 4294967295'],
            instance={'Delta': '-7', 'B': 'false', 'T': 'long long', 'N': '4294967295u'})

    def test_unsigned64_and_true_boolean(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned long long N> struct Wide {
  unsigned long long x;
  Wide(unsigned long long value) : x(value + N) {}
};
template<bool Invert> bool select(bool value) { return Invert ? !value : value; }
}
''', 'new Wide.init 1\nfield Wide.x 0\ncall select 0\ncall select 1\n',
            ['new', 'ok 0', 'ok 1', 'ok 0'],
            instance={'N': '18446744073709551615ull', 'Invert': 'true'})

    def test_explicit_value_calls_and_fixed_class_arguments(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned M> unsigned offset(unsigned value) { return value + M; }
template<unsigned N> unsigned twice(unsigned value) {
  return offset<N>(value) + offset<7>(value);
}
template<unsigned K> struct Counter {
  unsigned x;
  Counter(unsigned value) : x(value + K) {}
  unsigned get() const { return x + K; }
};
unsigned fixed(unsigned value) { Counter<7> c(value); return c.get(); }
}
''', 'call twice 5\ncall fixed 3\n', ['ok 26', 'ok 17'],
            instance={'M': '17', 'N': '9', 'K': '11'})

    def test_hidden_friend_deduces_value_parameter(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned N> struct Box {
  unsigned x;
  Box(unsigned value) : x(value) {}
  friend Box op(const Box& a, const Box& b) { return Box(a.x + b.x + N); }
};
unsigned read(const Box<7>& a, const Box<7>& b) { return op(a, b).x; }
}
''', 'new Box.init 3\nnew Box.init 5\ncall op 0 1\nfield Box.x 2\ncall read 0 1\n',
            ['new', 'new', 'ok obj', 'ok 15', 'ok 15'], instance={'N': '7'})

    def test_unsupported_parameter_kinds_are_not_erased(self):
        for parameters, includes in [('int* Pointer', ''), ('auto Value', ''),
                                     ('unsigned... Values', ''),
                                     ('unsigned N, std::enable_if_t<(N > 0 && N < 9)>* = nullptr', '#include <type_traits>\n')]:
            with self.subTest(parameters=parameters), self.assertRaises(lean_translate.Unsupported):
                self.model(includes + 'namespace cp { template<' + parameters +
                           '> struct Box { unsigned x; Box(unsigned value) : x(value) {} }; }')

    def test_unhandled_value_argument_expression_is_rejected(self):
        with self.assertRaisesRegex(lean_translate.Unsupported, 'non-type template argument'):
            self.model('''namespace cp {
template<unsigned N> unsigned constant() { return N; }
unsigned f() { return constant<1 + 2>(); }
}
''')

    def test_named_integer_width_conversion_is_rejected(self):
        with self.assertRaisesRegex(lean_translate.Unsupported, 'non-type template argument conversion'):
            self.model('''namespace cp {
template<long long N> long long constant() { return N; }
template<int M> long long f() { return constant<M>(); }
}
''')

    def test_explicit_mixed_arguments_cannot_drop_type_conversion(self):
        with self.assertRaisesRegex(lean_translate.Unsupported, 'explicit mixed type and non-type'):
            self.model('''namespace cp {
template<class T, unsigned N> T identity(T value) { return value; }
unsigned f(int value) { return identity<unsigned, 7>(value); }
}
''')


if __name__ == '__main__':
    unittest.main()
