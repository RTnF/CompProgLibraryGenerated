"""Growing append: native target correspondence and max_size boundaries."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network
from check_public import check_compiler, FLAGS
from test_scalar_ir import lean_environment


def buffer(values, capacity, epoch=0, limit=10000, owner=7):
    items = "[" + ",".join(f"({x}:Int)" for x in values) + "]"
    return f"(⟨{owner},{items},{capacity},{limit},{epoch}⟩ : Buffer Int)"


class GrowthTests(unittest.TestCase):
    def lean(self, scratch, checks):
        source = scratch / "checks.lean"
        source.write_text("import Proofs.CppVectorStoreGrowth\n"
                          "open Proofs Proofs.CppVector\n"
                          "def accept : Int → Bool := (⟨32,true,false⟩ : Proofs.CppScalar.Ty).valid\n"
                          + "\n".join(checks))
        lake, env = lean_environment()
        result = subprocess.run([lake, "env", "lean", str(source)], cwd=ROOT,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_native_growth_and_alias_value(self):
        # Include empty, arbitrary reserve, repeated growth, and a value read
        # from the very buffer that is reallocated. Never dereference stale C++ pointers.
        starts = [(0, 0), (0, 7), (1, 1), (3, 3), (3, 8), (8, 8), (15, 15)]
        native = ['#include "experiments/library/cpp/template/small_template.hpp"',
                  '#include <vector>', '#include <iostream>', 'int main() {']
        checks = []
        expected = []
        for size, reserved in starts:
            values = [i - 4 for i in range(size)]
            capacity, epoch = reserved, 0
            native += ['{ std::vector<int> v{' + ','.join(map(str, values)) + '};',
                       f'v.reserve({reserved});']
            for step in range(20):
                value = values[0] if values else -11
                old = buffer(values, capacity, epoch)
                full = len(values) == capacity
                new_capacity = max(1, 2 * len(values)) if full else capacity
                work = len(values) + 3 if full else 2
                peak = capacity + new_capacity + 2 if full else capacity + 2
                new_epoch = epoch + int(full)
                after = buffer(values + [value], new_capacity, new_epoch)
                checks.append(f'#guard CppVectorGrowth.append {old} accept true ({value}:Int) == '
                              f'some ⟨{after},(),{work},{peak}⟩')
                if values:
                    checks.append(f'#guard readRef {after} accept ⟨7,{epoch},0⟩ == ' +
                                  ('none' if full else f'some ⟨{after},({values[0]}:Int),1,{new_capacity+2}⟩'))
                # Native call deliberately passes an alias of the existing element.
                native += ['if (v.empty()) v.emplace_back(-11); else v.emplace_back(v[0]);',
                           'std::cout << v.size() << " " << v.capacity();',
                           'for (int x : v) std::cout << " " << x;',
                           'std::cout << "\\n";']
                values.append(value)
                capacity, epoch = new_capacity, new_epoch
                expected.append([len(values), capacity, *values])
            native.append('}')
        native.append('}')
        with tempfile.TemporaryDirectory(prefix="vector-growth-") as name:
            scratch = Path(name)
            self.lean(scratch, checks)
            source = scratch / "native.cpp"
            source.write_text("\n".join(native))
            check_compiler()
            exe = scratch / "native"
            subprocess.run(['g++', *FLAGS, '-fsanitize=undefined', '-fno-sanitize-recover=all',
                            '-I', str(ROOT), str(source), '-o', str(exe)], check=True, cwd=ROOT)
            result = subprocess.run([str(exe)], check=True, capture_output=True, text=True)
            self.assertEqual([list(map(int, line.split())) for line in result.stdout.splitlines()], expected)

    def test_clamped_growth_and_refusals(self):
        checks = []
        for size, limit in [(0, 1), (1, 2), (3, 4), (3, 5), (3, 6), (8, 9), (8, 15)]:
            values = list(range(size))
            cap = min(limit, max(1, 2 * size))
            old = buffer(values, size, limit=limit)
            after = buffer(values + [17], cap, 1, limit)
            checks += [f'#guard CppVectorGrowth.append {old} accept true 17 == '
                       f'some ⟨{after},(),{size+3},{size+cap+2}⟩',
                       f'#guard CppVectorGrowth.potential {after} == '
                       f'{0 if cap == limit else max(0, 2*(size+1)-cap)}']
        for old in [buffer([1], 1, limit=1), buffer([], 0, limit=0),
                    buffer([1, 2], 1), buffer([1], 3, limit=2), buffer([2147483648], 2)]:
            checks.append(f'#guard CppVectorGrowth.append {old} accept true 0 == none')
        old = buffer([1], 1)
        checks += [f'#guard CppVectorGrowth.append {old} accept false 0 == none',
                   f'#guard CppVectorGrowth.append {old} accept true 2147483648 == none',
                   f'#guard CppVectorGrowth.append {old} accept true (-2147483649) == none']
        with tempfile.TemporaryDirectory(prefix="vector-growth-faults-") as name:
            self.lean(Path(name), checks)

    def test_store_work_live_space_and_peak(self):
        checks = []
        for base in [0, 5]:
            values, capacities, epochs = [[], [4, 5]], [0, 3], [0, 0]
            work, peak = 0, 0

            def state():
                objects = ','.join('some ' + buffer(values[i], capacities[i], epochs[i], owner=i)
                                   for i in range(2))
                return f'(⟨[{objects}],{work},{peak},{base}⟩ : CppVectorStore.Store Int)'

            for step in range(30):
                owner = step % 2
                old = state()
                live = sum(capacities) + 2
                size, cap = len(values[owner]), capacities[owner]
                full = size == cap
                newcap = max(1, 2 * size) if full else cap
                opwork = size + 3 if full else 2
                oppeak = cap + newcap + 2 if full else cap + 2
                work += opwork
                peak = max(peak, live + oppeak - (cap + 1) - base, 0)
                values[owner].append(step)
                capacities[owner] = newcap
                epochs[owner] += int(full)
                after = state()
                checks += [f'#guard CppVectorStoreGrowth.append {old} accept true {owner} {step} == '
                           f'some ({after},())',
                           f'#guard {after}.liveSpace == {sum(capacities)+2}',
                           f'#guard {after}.peak >= {sum(capacities)+2-base}']
            checks += [f'#guard CppVectorStoreGrowth.append {state()} accept true 2 0 == none',
                       f'#guard CppVectorStoreGrowth.append {state()} accept false 0 0 == none']
        with tempfile.TemporaryDirectory(prefix="vector-store-growth-") as name:
            self.lean(Path(name), checks)


if __name__ == '__main__':
    disable_network()
    unittest.main()
