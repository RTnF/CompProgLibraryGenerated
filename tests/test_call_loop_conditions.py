"""Call-bearing loop tests must preserve final effects and control order."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from state_ir import (contains_kind, emit_lean, lean_expression,
                      lean_reference_statement, lower_source)
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE = '''namespace cp {
bool advance(long long &x, long long limit){++x;return x<limit;}
long long bump(long long &x){++x;return x;}
bool positive(long long x){return x>0ll;}
long long counted(long long &x,long long limit){
  long long count=0ll;while(advance(x,limit)){++count;}return count;
}
long long counted_for(long long &x,long long limit){
  long long count=0ll;for(long long i=0ll;advance(x,limit);++i){++count;}return count;
}
long long skipped_update(long long &x,long long limit){
  long long updates=0ll;for(;advance(x,limit);bump(updates)){if(x==2ll)break;}return updates;
}
long long returned(long long &x,long long limit){
  while(advance(x,limit)){return x;}return -x;
}
long long nested(long long &x,long long limit){
  long long count=0ll;while(advance(x,limit)){
    long long inner=0ll;while(advance(inner,3ll)){++count;}++count;
  }return count;
}
long long value_condition(long long n){long long count=0ll;while(positive(n)){++count;--n;}return count;}
long long value_for(long long n){long long count=0ll;for(long long i=0ll;positive(n);--n){count+=i;++i;}return count;}
}'''


class CallLoopConditionTests(unittest.TestCase):
    def check_lean(self, scratch, source, checks, succeeds=True):
        cpp = scratch / "source.cpp"
        cpp.write_text(source)
        ir = lower_source(cpp)
        generated = emit_lean(ir, "Conditions")
        # Check that the generated reference-loop iteration is exactly the
        # structural form used by the three general control lemmas.
        def iterations(value):
            if isinstance(value, dict):
                if value.get("kind") == "while":
                    iteration = value["body"]
                    if contains_kind(iteration, "reference_invoke") and value["condition"]["kind"] == "literal":
                        inner = iteration.get("body", {})
                        if iteration["kind"] == "scope" and inner.get("kind") == "sequence" and inner["rest"]["kind"] == "branch":
                            branch = inner["rest"]
                            yield ("\nexample : " + lean_reference_statement(iteration) +
                                " = Proofs.CppReferenceCommands.conditionIteration " +
                                lean_reference_statement(inner["first"]) + " " +
                                lean_expression(branch["condition"]) + " " +
                                lean_reference_statement(branch["yes"]) + " := rfl\n")
                for child in value.values():
                    yield from iterations(child)
            elif isinstance(value, list):
                for child in value:
                    yield from iterations(child)
        checks += "".join(iterations(ir))
        proof = scratch / "test.lean"
        proof.write_text(generated + "\n" + checks)
        lake, env = lean_environment()
        result = subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT,
                                env=env, capture_output=True, text=True)
        if succeeds:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)
        return generated

    def test_each_condition_evaluation_native_results_and_frames(self):
        checks = []
        native = ["#include <cassert>", SOURCE, "int main(){"]
        for start in [-3, 0, 1, 2, 5]:
            for limit in [-2, 0, 2, 4, 7, 20]:
                iterations = max(0, limit - start - 1)
                end = max(start + 1, limit)
                # Independent simulation: a body break skips both the update
                # and the next condition evaluation.
                stopped, updates = start, 0
                while True:
                    stopped += 1
                    if stopped >= limit or stopped == 2:
                        break
                    updates += 1
                cases = {"counted": (iterations, end), "counted_for": (iterations, end),
                         "nested": (3 * iterations, end), "skipped_update": (updates, stopped),
                         "returned": (start + 1 if start + 1 < limit else -(start + 1), start + 1)}
                for name, (value, changed) in cases.items():
                    call = (f"Conditions.{name}.callFuel 2000 "
                            f"[⟨⟨64,true,false⟩,({start})⟩,⟨⟨32,false,false⟩,99⟩] "
                            f"[.reference 0,.value ({limit})]")
                    checks.append(f"#guard (match {call} with | .finished r => "
                                  f"r.value == ({value}) && r.memory.map (·.value) == [({changed}),99] "
                                  f"&& r.peak ≤ 80 && r.work ≤ {256*(iterations+1)} | _ => false)")
                    native.append(f"{{long long x={start}LL;assert(cp::{name}(x,{limit}LL)=={value}LL);assert(x=={changed}LL);}}")
        for n in [-2, 0, 1, 4, 20]:
            for name, value in [("value_condition", max(n, 0)), ("value_for", sum(range(max(n, 0))))]:
                checks.append(f"#guard (match Conditions.{name}.callFuel 2000 [] [.value ({n})] "
                              f"with | .finished r => r.value == {value} && r.memory.isEmpty && r.peak ≤ 80 | _ => false)")
                native.append(f"assert(cp::{name}({n}LL)=={value}LL);")
        checks.extend(['''example (extra : Nat) :
  Conditions.counted.callFuel (2000+extra) [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 20] =
  Conditions.counted.callFuel 2000 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 20] := by
  exact Proofs.CppReferenceCommands.Program.callFuel_success_mono _ 2000 extra _ _ _ rfl''',
            '#guard Conditions.counted.callFuel 1 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 20] == .exhausted',
            '#guard Conditions.counted.callFuel 2000 [⟨⟨64,true,false⟩,9223372036854775807⟩] [.reference 0,.value 0] == .fault',
            '#guard Conditions.counted.callFuel 2000 [] [.reference 0,.value 0] == .fault'])
        checks.append('''#guard (match
  Conditions.counted.callFuel 2000 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 2],
  Conditions.counted.callFuel 2000 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 200] with
  | .finished small, .finished large => small.peak == large.peak && large.value == 199
  | _, _ => false)''')
        native.append("}")
        with tempfile.TemporaryDirectory(prefix="call-loop-conditions-") as directory:
            scratch = Path(directory)
            generated = self.check_lean(scratch, SOURCE, "\n".join(checks))
            self.assertIn("Proofs.CppReferenceCommands.Program", generated)
            self.assertIn("LoopProgram", generated)
            cpp, binary = scratch / "native.cpp", scratch / "native"
            cpp.write_text("\n".join(native))
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=undefined",
                            "-fno-sanitize-recover=all", str(cpp), "-o", str(binary)], check=True)
            subprocess.run([str(binary)], check=True)

    def test_boundary_effect_mutations_and_unsupported_conditions(self):
        guard = ('#guard (match Conditions.counted.callFuel 200 [⟨⟨64,true,false⟩,0⟩] '
                 '[.reference 0,.value 4] with | .finished r => r.value == 3 && '
                 'r.memory.map (·.value) == [4] | _ => false)\n')
        with tempfile.TemporaryDirectory(prefix="call-loop-mutations-") as directory:
            scratch = Path(directory)
            self.check_lean(scratch, SOURCE, guard)
            for changed in [SOURCE.replace("x<limit", "x<=limit"), SOURCE.replace("++x;return x<limit", "x+=2ll;return x<limit")]:
                self.check_lean(scratch, changed, guard, False)
            original = scratch / "source.cpp"
            original.write_text(SOURCE)
            before = lower_source(original)
            original.write_text(SOURCE.replace("advance", "next_test"))
            after = lower_source(original)
            for function in after["functions"]:
                if function["name"] == "next_test":
                    function["name"] = "advance"
            self.assertEqual(before, after)
            for loop in ["while(advance(x,4ll)&&x<3ll){}", "for(;advance(x,4ll)||x<3ll;){}",
                         "while(bool b=advance(x,4ll)){}"]:
                original.write_text('namespace cp {bool advance(long long &x,long long n){++x;return x<n;}long long f(long long &x){' + loop + 'return x;}}')
                with self.subTest(loop=loop), self.assertRaises(ValueError):
                    lower_source(original)


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.CppReferenceCommands"], cwd=ROOT, env=env, check=True)
    unittest.main()
