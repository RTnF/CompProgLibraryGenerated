"""Shared nonoverflow cases for every registered integer Group instance."""


def main():
    counts = {}

    def new(cls, ctor, *args):
        index = counts.get(cls, 0)
        counts[cls] = index + 1
        print('new', cls + '.' + ctor, *args)
        return index

    def result(cls, command, label, *args):
        index = counts[cls]
        counts[cls] += 1
        print(command, label, *args)
        return index

    for cls in ['GroupSum', 'GroupMul']:
        default = new(cls, 'init_0')
        print('do', cls + '.x', default)
        objects = [new(cls, 'init_T', value) for value in ([0, 1, 2, 3] if cls == 'GroupSum' else [1, 2, 3])]
        # Nonzero unsigned negation is outside the common no-wrap domain.
        inverse = result(cls, 'do', cls + '.inv', objects[0])
        print('do', cls + '.x', inverse)
        for a in objects:
            for b in objects:
                for form in ['hidden', 'qualified']:
                    r = result(cls, 'call', f'op_{cls}_{cls}_{form}', a, b)
                    print('do', cls + '.x', r)
    cls = 'GroupAffine'
    default = new(cls, 'init_0')
    objects = [default] + [new(cls, 'init_T_T', a, b) for a, b in [(0, 0), (1, 0), (2, 3), (3, 1)]]
    for a in objects:
        print('do', cls + '.a', a)
        print('do', cls + '.b', a)
        print('do', cls + '.apply', a, 2)
        for b in objects:
            for form in ['hidden', 'qualified']:
                r = result(cls, 'call', f'op_{cls}_{cls}_{form}', a, b)
                print('do', cls + '.a', r)
                print('do', cls + '.b', r)
                print('do', cls + '.apply', r, 2)
    inverse = result(cls, 'do', cls + '.inv', default)
    print('do', cls + '.a', inverse)
    print('do', cls + '.b', inverse)


if __name__ == '__main__':
    main()
