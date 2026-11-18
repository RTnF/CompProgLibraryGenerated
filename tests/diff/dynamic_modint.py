"""Exercise the runtime-modulus interface and the shared-cache calls."""


def commands():
    objects = 9

    def observe(command):
        nonlocal objects
        yield command
        yield f'field DynamicModInt.x {objects}'
        objects += 1

    for value in (-(2**63), -998244353, -1, 0, 1, 998244353, 2**63-1):
        yield f'new DynamicModInt.init_T {value}'
    # Keep indices 0..6 stable; commands below may append returned objects.
    yield 'new DynamicModInt.init_U 18446744073709551615'
    yield 'new DynamicModInt.init_0'
    for index in range(9):
        yield f'do DynamicModInt.get_ {index}'
    yield 'do DynamicModInt.set__T 8 -1'
    yield 'do DynamicModInt.get_ 8'
    yield 'do DynamicModInt.set__U 8 18446744073709551615'
    yield 'do DynamicModInt.get_ 8'
    for op in ('add', 'sub', 'mul', 'div'):
        yield from observe(f'call op_{op}_DynamicModInt_DynamicModInt 0 4')
    for op in ('eq', 'ne'):
        yield f'call op_{op}_DynamicModInt_DynamicModInt 0 4'
    for op in ('inc_0', 'inc_int', 'dec_0', 'dec_int', 'add', 'sub'):
        command = f'do DynamicModInt.op_{op} 0'
        yield from observe(command + (' 0' if op.endswith('_int') else ''))
        yield 'do DynamicModInt.get_ 0'
    for op in ('add', 'sub', 'mul', 'div'):
        yield from observe(f'do DynamicModInt.op_{op}_assign 0 4')
        yield 'do DynamicModInt.get_ 0'
    for exponent in (-(2**63), -17, -1, 0, 1, 17, 2**63-1):
        yield from observe(f'do DynamicModInt.pow 0 {exponent}')
    yield from observe('do DynamicModInt.inv 0')
    yield 'call dynamic_modint_pow_word 4294967290 18446744073709551615 4294967291'
    for command in ('factorial 0', 'factorial_inv 0', 'dynamic_modint.C 0 0'):
        yield from observe(f'call {command}')
    # Source-tagged signed extraction and unsigned insertion.
    yield 'call op_shr_istream_DynamicModInt 1 -998244354 8'
    yield 'do DynamicModInt.get_ 8'
    yield 'call op_shl_ostream_DynamicModInt 8'


if __name__ == '__main__':
    print('\n'.join(commands()))
