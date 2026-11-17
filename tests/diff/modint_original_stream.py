"""Native original ModInt I/O cases; expectations use mathematical integers."""
MODULI = (2, 7, 998244353, 2147483647, 4294967291)
LOW, HIGH = -(2**63), 2**63-1


def cases_for_modulus(modulus):
    commands, expected = [], []
    # mode, text, extracted value, fail, eof, bad, thrown
    reads = [('normal', '', 0, 1, 1, 0, 0),
             ('normal', ' \t\n', 0, 1, 1, 0, 0),
             ('normal', 'x', 0, 1, 0, 0, 0),
             ('normal', '-', 0, 1, 1, 0, 0),
             ('normal', '12x', 12, 0, 0, 0, 0),
             ('normal', '12', 12, 0, 1, 0, 0),
             ('normal', '-14', -14, 0, 1, 0, 0),
             ('normal', str(LOW), LOW, 0, 1, 0, 0),
             ('normal', str(HIGH), HIGH, 0, 1, 0, 0),
             ('normal', str(2**80), HIGH, 1, 1, 0, 0),
             ('normal', str(-2**80), LOW, 1, 1, 0, 0),
             ('fail', '12', 0, 1, 0, 0, 0),
             ('eof', '12', 0, 1, 1, 0, 0),
             ('bad', '12', 0, 1, 0, 1, 0),
             ('throw_fail', '', None, 1, 1, 0, 1),
             ('throw_fail', 'x', None, 1, 0, 0, 1),
             ('throw_eof', '12', None, 0, 1, 0, 1)]
    for initial in (0, modulus-1):
        for mode, text, value, fail, eof, bad, thrown in reads:
            tokens = [str(ord(c)) for c in text]
            commands.append(' '.join(['r', mode, str(initial), str(len(tokens)), *tokens]))
            result = initial if thrown else value % modulus
            expected.append(f'r {result} {fail} {eof} {bad} {thrown} {1-thrown}')
        for mode in ('decimal', 'showpos', 'hex', 'octal', 'padded'):
            if mode == 'hex':
                text = '0' if initial == 0 else '0X' + format(initial, 'X')
            elif mode == 'octal':
                text = '0' if initial == 0 else '0' + format(initial, 'o')
            else:
                text = str(initial)
                if mode == 'padded':
                    text = text.rjust(12, '_')
            commands.append(f'w {mode} {initial}')
            expected.append(' '.join(['w', '1', str(len(text)), *[str(ord(c)) for c in text]]))
    return '\n'.join(commands)+'\n', expected


if __name__ == '__main__':
    print(cases_for_modulus(7)[0], end='')
