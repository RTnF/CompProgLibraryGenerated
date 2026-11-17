"""Generic member definitions are translated once, including constructors."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'verifier'))
import test_lean_model_friend as friends
import lean_translate


class MemberTemplateTests(unittest.TestCase):
    def test_reference_template_constructor_cannot_be_erased_as_copy(self):
        header = '''namespace cp {
struct Box {
  int x;
  Box() : x(5) {}
  template<class T> Box(T& value) : x(99) {}
};
int run() { Box a; Box b(a); return b.x; }
}
'''
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'member.hpp'
            source.write_text(header)
            with self.assertRaisesRegex(lean_translate.Unsupported, 'copy competing with a reference template'):
                lean_translate.translate_file(source, [])

    def test_distinct_instantiations_keep_distinct_arithmetic(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
struct Twice {
  long long x;
  Twice(long long value) : x(value) {}
  template<class T> T apply(T value) const { return value + value; }
};
long long run(long long value) {
  Twice twice(0);
  return twice.apply(value) + (long long)twice.apply(4294967295u);
}
}
''', 'call run -21\ncall run 5\n', ['ok 4294967252', 'ok 4294967304'],
            instance={'T': 'long long'})

    def test_explicit_method_type_arguments_are_rejected(self):
        header = '''namespace cp {
struct Box {
  int x;
  Box(int value) : x(value) {}
  template<class T> T echo(T value) const { return value; }
};
unsigned f(int value) { Box box(0); return box.echo<unsigned>(value); }
}
'''
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'member.hpp'
            source.write_text(header)
            with self.assertRaisesRegex(lean_translate.Unsupported, 'explicit member template arguments'):
                lean_translate.translate_file(source, [])

    def test_calls_in_cpp_deduce_generic_members(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned N> class Box {
  long long x;
public:
  template<class T> Box(T value) : x(value) {}
  template<class U> void set(U value) { x = value; }
  template<class V> V echo(V value) const { return value; }
  long long get() const { return x; }
};
long long run(long long value) {
  Box<7> box(value);
  box.set(13);
  return box.get() + box.echo(value);
}
}
''', 'call run -21\ncall run 5\n', ['ok -8', 'ok 18'],
            instance={'N': '7', 'T': 'long long', 'U': 'long long', 'V': 'long long'})

    def test_generic_constructor_set_and_identity(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned N> class Box {
  long long x;
public:
  template<class T> Box(T value) : x(value) {}
  template<class U> void set(U value) { x = value; }
  template<class V> V echo(V value) const { return value; }
  long long get() const { return x; }
};
}
''', 'new Box.init -7\ndo Box.get_ 0\ndo Box.set_ 0 13\ndo Box.get_ 0\ndo Box.echo 0 -21\n',
            ['new', 'ok -7', 'ok', 'ok 13', 'ok -21'],
            instance={'N': '7', 'T': 'long long', 'U': 'long long', 'V': 'long long'})


if __name__ == '__main__':
    unittest.main()
