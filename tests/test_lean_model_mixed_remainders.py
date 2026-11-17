"""A uint32 destination does not narrow the operands before mixed-type %."""
import unittest
import test_lean_model_friend as friends

SOURCE = '''#pragma once
namespace cp {
template<class T> unsigned narrow(T value, unsigned modulus) { return value % modulus; }
}
'''


class MixedRemainderTests(unittest.TestCase):
    def test_signed_width_changes_unsigned_promotion(self):
        for cpp, promoted in (('int', True), ('long long', False)):
            commands, expected = [], []
            for value in (-2147483648, -17, -1, 0, 1, 2147483647):
                for modulus in (2, 7, 4294967291):
                    operand = value % 2**32 if promoted else value
                    remainder = operand % modulus if operand >= 0 else -((-operand) % modulus)
                    commands.append(f'call narrow {value} {modulus}')
                    expected.append(f'ok {remainder % 2**32}')
            with self.subTest(cpp=cpp):
                friends.FriendTranslationTests().compare(SOURCE, '\n'.join(commands)+'\n', expected,
                                                        instance={'T': cpp})

    def test_bool_and_unsigned_words(self):
        for cpp, values in (('bool', [0, 1]), ('unsigned int', [0, 1, 2**32-1]),
                            ('unsigned long long', [0, 1, 2**64-1])):
            commands, expected = [], []
            for value in values:
                for modulus in (2, 7, 4294967291):
                    commands.append(f'call narrow {value} {modulus}')
                    expected.append(f'ok {value % modulus}')
            with self.subTest(cpp=cpp):
                friends.FriendTranslationTests().compare(SOURCE, '\n'.join(commands)+'\n', expected,
                                                        instance={'T': cpp})


if __name__ == '__main__':
    unittest.main()
