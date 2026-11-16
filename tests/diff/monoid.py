"""Common representable cases for every registered integral Monoid binding."""
for cls in ('MonoidMul', 'MonoidMax', 'MonoidMin'):
    print(f'new {cls}.init_0')
    for value in (0, 1, 3, 7, 11):
        print(f'new {cls}.init_T {value}')
    for index in range(6):
        print(f'field {cls}.x {index}')
    next_index = 6
    for left in range(6):
        for right in range(6):
            # Multiplication by integer extrema is not used: its identity is 1,
            # and 11 * 11 fits even the smallest signed binding.
            for kind in ('hidden', 'qualified'):
                print(f'call op_{cls}_{cls}_{kind} {left} {right}')
                print(f'field {cls}.x {next_index}')
                next_index += 1
