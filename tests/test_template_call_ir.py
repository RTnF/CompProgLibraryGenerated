"""Resolve concrete template calls by Clang identity, including nested calls."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from state_ir import emit_lean, lower_source
from test_scalar_ir import lean_environment
from offline import disable_network

HEADER = ROOT / "experiments/verification/template/update_extrema.hpp"
SOURCE = f'#include "{HEADER}"\n' + '''namespace cp {
template<class T>T step(T x){return x+T(1);}
template<class T>T relay(T x){return step<T>(x);}
long long ordinary_step(long long x){return x+3ll;}
template<class T>T via_ordinary(T x){return T(ordinary_step(x));}
template<class T>bool advance(T &x,const T &limit){++x;return x<limit;}
template<class T>T scan(T &x,const T &limit){T count=T(0);while(advance<T>(x,limit)){++count;}return count;}
long long value64(long long x){return relay(x);}
long long through_ordinary(long long x){return via_ordinary(x);}
unsigned int value32(unsigned int x){return relay<unsigned int>(x);}
long long loop64(long long &x,const long long &limit){return scan(x,limit);}
unsigned int loop32(unsigned int &x,const unsigned int &limit){return scan<unsigned int>(x,limit);}
bool low(int &x,const int &y){return chmin(x,y);}
bool high(unsigned int &x,const unsigned int &y){return chmax(x,y);}
}'''


class TemplateCallIRTests(unittest.TestCase):
    def lower(self, scratch, source):
        cpp = scratch / "source.cpp"
        cpp.write_text(source)
        return lower_source(cpp)

    def lean(self, scratch, ir, checks, succeeds=True):
        proof = scratch / "test.lean"
        proof.write_text(emit_lean(ir, "TemplateCalls") + "\n" + checks)
        lake, env = lean_environment()
        result = subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT,
                                env=env, capture_output=True, text=True)
        if succeeds:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)

    def test_generated_template_callees_and_original_helpers(self):
        checks, native = [], ["#include <cassert>", SOURCE, "int main(){"]
        for name, ty, cpp_type, values in [
            ("value64", "⟨64,true,false⟩", "long long", [-7, -1, 0, 4, 100]),
            ("through_ordinary", "⟨64,true,false⟩", "long long", [-7, -1, 0, 4, 100]),
            ("value32", "⟨32,false,false⟩", "unsigned int", [0, 1, 4, 100, 4294967295])]:
            for value in values:
                expected = value + 3 if name == "through_ordinary" else value + 1 if name == "value64" else (value + 1) % (2**32)
                checks.append(f"#guard (TemplateCalls.{name}.call [] [.value ({value})]).map (·.value) == some ({expected})")
                suffix = "U" if name == "value32" else "LL"
                native.append(f"assert(cp::{name}({value}{suffix})=={expected}{suffix});")
        for name, ty, cpp_type, starts in [
            ("loop64", "⟨64,true,false⟩", "long long", [-3, 0, 2, 5]),
            ("loop32", "⟨32,false,false⟩", "unsigned int", [0, 1, 2, 5])]:
            for start in starts:
                for limit in [0, 2, 4, 7]:
                    end, count = max(start + 1, limit), max(0, limit - start - 1)
                    memory = f"[⟨{ty},({start})⟩,⟨{ty},{limit}⟩]"
                    checks.append(f"#guard (match TemplateCalls.{name}.callFuel 800 {memory} [.reference 0,.reference 1] "
                                  f"with | .finished r => r.value == {count} && r.memory.map (·.value) == [({end}),{limit}] | _ => false)")
                    native.append(f"{{{cpp_type} x={start},limit={limit};assert(cp::{name}(x,limit)=={count});assert(x=={end});assert(limit=={limit});}}")
                checks.append(f"#guard (match TemplateCalls.{name}.callFuel 800 [⟨{ty},({start})⟩] [.reference 0,.reference 0] "
                              f"with | .finished r => r.value == 0 && r.memory.map (·.value) == [({start+1})] | _ => false)")
                native.append(f"{{{cpp_type} x={start};assert(cp::{name}(x,x)==0);assert(x=={start+1});}}")
        for name, ty, cpp_type in [("low", "⟨32,true,false⟩", "int"), ("high", "⟨32,false,false⟩", "unsigned int")]:
            for x in [0, 1, 9]:
                for y in [0, 1, 9]:
                    changed = y < x if name == "low" else x < y
                    value = min(x, y) if name == "low" else max(x, y)
                    checks.append(f"#guard (TemplateCalls.{name}.call [⟨{ty},{x}⟩,⟨{ty},{y}⟩] [.reference 0,.reference 1]).map "
                                  f"(fun r => (r.value,r.memory.map (·.value))) == some ({int(changed)},[{value},{y}])")
                    native.append(f"{{{cpp_type} x={x},y={y};assert(cp::{name}(x,y)=={str(changed).lower()});assert(x=={value});assert(y=={y});}}")
        checks.append('#guard TemplateCalls.value64.call [] [.value 9223372036854775807] == none')
        native.append("}")
        with tempfile.TemporaryDirectory(prefix="template-call-ir-") as directory:
            scratch = Path(directory)
            ir = self.lower(scratch, SOURCE)
            self.assertTrue(all(t["coverage"] == "concrete_instances_only" for t in ir["templates"]))
            self.assertEqual(len(ir["templates"]), 7)
            self.lean(scratch, ir, "\n".join(checks))
            cpp, binary = scratch / "native.cpp", scratch / "native"
            cpp.write_text("\n".join(native))
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=undefined",
                            "-fno-sanitize-recover=all", str(cpp), "-o", str(binary)], check=True)
            subprocess.run([str(binary)], check=True)

    def test_declaration_identity_renaming_mutations_and_refusal(self):
        with tempfile.TemporaryDirectory(prefix="template-call-changes-") as directory:
            scratch = Path(directory)
            original = self.lower(scratch, SOURCE)
            renamed = self.lower(scratch, SOURCE.replace("step", "successor"))
            for function in renamed["functions"]:
                function["name"] = function["name"].replace("successor", "step")
                if "cpp_name" in function:
                    function["cpp_name"] = function["cpp_name"].replace("successor", "step")
            for template in renamed["templates"]:
                template["name"] = template["name"].replace("successor", "step")
                template["instances"] = [s.replace("successor", "step") for s in template["instances"]]
            self.assertEqual(original, renamed)
            guard = '#guard (TemplateCalls.value64.call [] [.value 5]).map (·.value) == some 6\n'
            self.lean(scratch, original, guard)
            self.lean(scratch, self.lower(scratch, SOURCE.replace("x+T(1)", "x+T(2)")), guard, False)
            # Ordinary and template overloads share a name; the selected
            # FunctionDecl ID, rather than spelling, determines the body.
            overload = '''namespace cp {template<class T>T pick(T x){return x+T(1);}
int pick(int x){return x+9;}int ordinary(int x){return pick(x);}
long chosen(long x){return pick<long>(x);}}'''
            self.lean(scratch, self.lower(scratch, overload),
                      '#guard (TemplateCalls.ordinary.call [] [.value 2]).map (·.value) == some 11\n'
                      '#guard (TemplateCalls.chosen.call [] [.value 2]).map (·.value) == some 3\n')
            for text in [
                'template<class T>T f(T x){return f(x);}int g(int x){return f(x);}',
                'template<class T>T f(T x);int g(int x){return f(x);}',
                'template<class T>T f(T x){return x;}template<>int f<int>(int x){return 9;}int g(int x){return f(x);}',
                'template<int N>int f(int x){return x+N;}int g(int x){return f<2>(x);}',
                'template<class T>bool f(T &x){++x;return true;}bool g(int &x){return f(x)&&x>0;}',
            ]:
                with self.subTest(source=text), self.assertRaises(ValueError):
                    self.lower(scratch, "namespace cp {" + text + "}")


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.CppReferenceCommands"], cwd=ROOT, env=env, check=True)
    unittest.main()
