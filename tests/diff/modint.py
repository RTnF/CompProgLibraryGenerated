"""Commands for the complete public ModInt; globals retain their original size.

The fixed factorial API returns mint (998244353). Other moduli and full-width
constructor inputs are covered by the original API's native/model regressions.
Startup and the complete factorial table have separate proofs and native tests.
"""


def commands():
    for value in (-(2**63), -998244353, -1, 0, 1, 998244353, 2**63-1):
        yield f'new ModInt.init_T {value}'
    # Keep indices 0..6 stable; commands below may append returned objects.
    yield 'new ModInt.init_U 18446744073709551615'
    yield 'new ModInt.init_0'
    for index in range(9):
        yield f'do ModInt.get_ {index}'
    yield 'do ModInt.set__T 8 -1'
    yield 'do ModInt.get_ 8'
    yield 'do ModInt.set__U 8 18446744073709551615'
    yield 'do ModInt.get_ 8'
    for op in ('add', 'sub', 'mul', 'div', 'eq', 'ne'):
        yield f'call op_{op}_ModInt_ModInt 0 4'
        yield 'do ModInt.get_ 0'
    for op in ('inc_0', 'inc_int', 'dec_0', 'dec_int', 'add', 'sub'):
        yield f'do ModInt.op_{op} 0' + (' 0' if op.endswith('_int') else '')
        yield 'do ModInt.get_ 0'
    for op in ('add', 'sub', 'mul', 'div'):
        yield f'do ModInt.op_{op}_assign 0 4'
        yield 'do ModInt.get_ 0'
    for exponent in (-(2**63), -17, -1, 0, 1, 17, 2**63-1):
        yield f'do ModInt.pow 0 {exponent}'
    yield 'do ModInt.inv 0'
    # Source-tagged signed extraction and unsigned insertion.
    yield 'call op_shr_istream_ModInt 1 -998244354 8'
    yield 'do ModInt.get_ 8'
    yield 'call op_shl_ostream_ModInt 8'


if __name__ == '__main__':
    print('\n'.join(commands()))
