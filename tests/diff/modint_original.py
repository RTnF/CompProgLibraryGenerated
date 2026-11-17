"""Boundary inputs and Python integer oracles for the original ModInt API."""
import argparse
import random


MODULI = (2, 7, 998244353, 2147483647, 4294967291)


def cases_for_modulus(modulus):
    rng = random.Random(20261116 + modulus)
    commands, expected = [], []
    signed = [-(2**63), -(2**63) + 1, -2*modulus, -modulus, -1, 0, 1,
              modulus - 1, modulus, 2*modulus, 2**63 - 1]
    for op in ('signed', 'set'):
        for value in signed:
            commands.append(f'{op} {value}')
            expected.append(value % modulus)
    for value in (0, 1, modulus - 1, modulus, modulus + 1, 2**32 - 1, 2**64 - 1):
        commands.append(f'unsigned {value}')
        expected.append(value % modulus)
    values = (0, 1, modulus - 1, modulus, 2**32 - 1, 2**64 - 1)
    pairs = [(a, b) for a in values for b in values]
    pairs += [(rng.randrange(2**64), rng.randrange(2**64)) for _ in range(120)]
    for op in ('add', 'sub', 'mul', 'alias_add', 'alias_sub'):
        for a, b in pairs:
            commands.append(f'{op} {a} {b}')
            value = {'add': a+b, 'sub': a-b, 'mul': a*b,
                     'alias_add': 2*a, 'alias_sub': 0}[op]
            expected.append(value % modulus)
    for base in (1, modulus - 1, 2 if modulus > 2 else 1):
        for exponent in (-(2**63), -(2**63)+1, -100, -1, 0, 1, 2, 63, 2**63-1):
            commands.append(f'pow {base} {exponent}')
            expected.append(pow(base, exponent, modulus))
    for op in ('signed128', 'set128'):
        commands.append(op)
        expected += [value % modulus for value in
                     (-(2**127), -(2**127)+1, -modulus, -1, 0, 1, 2**127-1)]
    commands.append('unsigned128')
    expected += [value % modulus for value in (0, 1, 2**127, 2**128-1)]
    commands.append('qualified128')
    expected += [(-1) % modulus] * 2
    return '\n'.join(commands) + '\n', expected


def constexpr_power_assertions():
    lines = []
    for modulus in MODULI:
        for base in (0, 1, 2, modulus-1):
            for exponent in (-(2**63), -17, -1, 0, 1, 17, 2**63-1):
                if exponent < 0 and base % modulus == 0:
                    continue
                expected = pow(base, exponent, modulus)
                argument = '(-9223372036854775807LL-1)' if exponent == -(2**63) else str(exponent)+'LL'
                lines.append(f'static_assert(ModInt<{modulus}u>({base}ull).pow({argument}) == ModInt<{modulus}u>({expected}ull));')
    return lines


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('modulus', type=int, choices=MODULI)
    args = parser.parse_args()
    print(cases_for_modulus(args.modulus)[0], end='')
