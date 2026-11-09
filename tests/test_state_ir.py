"""C++/Lean differential tests for scalar updates, aliases and scopes."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
import state_ir
from test_scalar_ir import lean_environment
from offline import disable_network


class StateTests(unittest.TestCase):
    def lower(self, text):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.cpp"
            source.write_text("namespace cp { " + text + " }")
            return state_ir.lower_source(source)

    def check_lean(self, scratch, text, success=True):
        proof = scratch / "test.lean"
        proof.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)

    def test_scopes_updates_early_return_and_aliases(self):
        text = '''int alias(int &a, const int &b) { a = a + 1; return b; }
int scope(int a) { if (a) int b = 9; int c = 2; return c; }
int shadow(int a) { { int a = 3; a = 4; } return a; }
int early(int &a) { if (a < 0) { return 3; } a = 7; return 4; }
int mixed(int a, int &b) { b = 3; return b; }
'''
        ir = self.lower(text)
        lean = state_ir.emit_lean(ir, "StateTest") + "\nopen StateTest Proofs.CppState\n"
        for a in range(-3, 4):
            for b in range(-3, 4):
                lean += f"#guard (alias.call [⟨⟨32,true,false⟩,{a}⟩,⟨⟨32,true,false⟩,{b}⟩] [.reference 0,.reference 1]).map (fun r => (r.value, r.memory.map (·.value))) == some ({b}, [{a+1},{b}])\n"
            lean += f"#guard (alias.call [⟨⟨32,true,false⟩,{a}⟩] [.reference 0,.reference 0]).map (fun r => (r.value, r.memory.map (·.value))) == some ({a+1}, [{a+1}])\n"
            lean += f"#guard (scope.call [] [.value ({a})]).map (fun r => (r.value, r.memory.length)) == some (2, 0)\n"
            lean += f"#guard (shadow.call [] [.value ({a})]).map (·.value) == some ({a})\n"
            value, updated = (3, a) if a < 0 else (4, 7)
            lean += f"#guard (early.call [⟨⟨32,true,false⟩,{a}⟩] [.reference 0]).map (fun r => (r.value,r.memory.map (·.value))) == some ({value},[{updated}])\n"
        lean += """#guard alias.call [⟨⟨32,true,false⟩,2147483647⟩] [.reference 0,.reference 0] == none
#guard alias.call [] [.reference 0,.reference 0] == none
#guard alias.call [⟨⟨32,false,false⟩,0⟩] [.reference 0,.reference 0] == none
#guard scope.call [] [.reference 0] == none
#guard scope.call [] [.value 0,.value 1] == none
#guard mixed.call [] [.value 2,.reference 0] == none
"""
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            self.check_lean(scratch, lean)
            source = scratch / "test.cpp"
            source.write_text("#include <cassert>\nnamespace cp {" + text + '''}
int main() {
  for (int a=-3; a<=3; ++a) {
    for (int b=-3; b<=3; ++b) { int x=a; assert(cp::alias(x,b)==b); assert(x==a+1); }
    int x=a; assert(cp::alias(x,x)==a+1); assert(x==a+1);
    assert(cp::scope(a)==2); assert(cp::shadow(a)==a);
    x=a; assert(cp::early(x)==(a<0?3:4)); assert(x==(a<0?a:7));
  }
}''')
            binary = scratch / "test"
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=undefined",
                            "-fno-sanitize-recover=all", str(source), "-o", str(binary)], check=True)
            subprocess.run([str(binary)], check=True)
            changed = self.lower("int early(int &a) { if (a <= 0) { return 3; } a = 7; return 4; }")
            self.check_lean(scratch, state_ir.emit_lean(changed, "BoundaryState") +
                            "\n#guard (BoundaryState.early.call [⟨⟨32,true,false⟩,0⟩] [.reference 0]).map (·.value) == some 4\n",
                            success=False)

    def test_template_instances_and_original_source_correspondence(self):
        instances = ROOT / "tests/imports/update_extrema_instantiations.cpp"
        ir = state_ir.lower_source(instances)
        self.assertEqual(len(ir["functions"]), 4)
        self.assertTrue(all(t["coverage"] == "concrete_instances_only" for t in ir["templates"]))
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            # Lower actual imported definitions as well: namespace differences
            # and unrelated template helpers must not select another model.
            for original in ["experiments/library/cpp/template/template.cpp",
                             "experiments/library3/cpp/Template/Template.cpp"]:
                for name in ("chmin", "chmax"):
                    source = scratch / "original.cpp"
                    source.write_text(f'#include "{ROOT / original}"\n' +
                        f'template bool {name}<int,int>(int &,const int &);\n' +
                        f'template bool {name}<unsigned int,unsigned int>(unsigned int &,const unsigned int &);\n')
                    imported = state_ir.lower_source(source, name)
                    expected = [f for f in ir["functions"] if f["cpp_name"] == name]
                    self.assertEqual(imported["functions"], expected)
            lean = state_ir.emit_lean(ir, "ExtremaTest") + "\nopen ExtremaTest Proofs.CppState\n"
            for function in ir["functions"]:
                signed = function["template_arguments"][0] == "int"
                ty = "⟨32,true,false⟩" if signed else "⟨32,false,false⟩"
                values = [-2147483648, -3, -1, 0, 1, 3, 2147483647] if signed else [0,1,3,4294967295]
                for a in values:
                    for b in values:
                        changed = a < b if function["cpp_name"] == "chmax" else b < a
                        updated = b if changed else a
                        lean += f"#guard ({function['name']}.call [⟨{ty},{a}⟩,⟨{ty},{b}⟩] [.reference 0,.reference 1]).map (fun r => (r.value,r.memory.map (·.value),r.work,r.peak)) == some ({int(changed)},[{updated},{b}],{9 if changed else 7},5)\n"
                    lean += f"#guard ({function['name']}.call [⟨{ty},{a}⟩] [.reference 0,.reference 0]).map (fun r => (r.value,r.memory.map (·.value),r.work,r.peak)) == some (0,[{a}],7,5)\n"
            self.check_lean(scratch, lean)
            source = scratch / "candidate.cpp"
            source.write_text(f'#include "{ROOT / "experiments/library/cpp/template/small_template.hpp"}"\n' +
                              f'#include "{ROOT / "experiments/verification/template/update_extrema.hpp"}"\n' + '''
template<class T> void check(const vector<T>& values) {
  for (T a:values) { for (T b:values) {
    T x=a; assert(cp::chmax(x,b)==(a<b)); assert(x==(a<b?b:a));
    x=a; assert(cp::chmin(x,b)==(b<a)); assert(x==(b<a?b:a));
  } T x=a; assert(!cp::chmax(x,x)); assert(x==a); assert(!cp::chmin(x,x)); assert(x==a); }
}
int main() { check<int>({INT_MIN,-3,-1,0,1,3,INT_MAX}); check<unsigned int>({0,1,3,UINT_MAX}); }
''')
            binary = scratch / "candidate"
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=undefined",
                            "-fno-sanitize-recover=all", str(source), "-o", str(binary)], check=True)
            subprocess.run([str(binary)], check=True)

    def test_unsupported_state_constructs_and_templates_are_refused(self):
        for text in ["int f(int &&a){return a;}", "int f(int&a){while(a){continue;}return a;}",
                     "int f(int&a){int &b=a;return b;}", "int& f(int&a){return a;}",
                     "int f(int a){return ++a;}", "int f(int a){if(int b=a) return b;return 0;}",
                     "int f(int a){return a+=1;}", "int f(int a){a<<=1;return a;}",
                     "int f(int a){a+=++a;return a;}",
                     "template<class T> int f(T a){return a;}",
                     "template<class... T> int f(T... args){return 0;} template int f<int>(int);",
                     "template<int n> int f(){return n;} template int f<1>();"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.lower(text)

    def test_compound_assignments_promotions_aliases_and_imported_safe_mod(self):
        declarations = '\n'.join(f'int op{i}(int &a,const int &b){{a{op}=b;return a;}}'
            for i, op in enumerate(['+', '-', '*', '/', '%']))
        declarations += '''
unsigned int wide(unsigned int a, unsigned long b){a *= b; return a;}
bool promoted(bool a, int b){a += b; return a;}
int narrowing(int a, unsigned long b){a += b; return a;}
'''
        ir = self.lower(declarations)
        with tempfile.TemporaryDirectory(prefix='compound-') as directory:
            scratch = Path(directory)
            original = ROOT / 'experiments/library/cpp/number_theory/floor_sum.hpp'
            candidate = ROOT / 'library/number_theory/safe_mod.hpp'
            imported = state_ir.lower_source(original, 'safe_mod', [ROOT/'experiments/library/cpp'])
            lowered_candidate = state_ir.lower_source(candidate)
            self.assertEqual(imported, lowered_candidate)
            lean = state_ir.emit_lean(ir, 'CompoundTest') + state_ir.emit_lean(imported, 'SafeModTest')
            # Separate import directives belong before declarations in Lean.
            lean = lean.replace('import Proofs.CppState\n', '')
            lean = 'import Proofs.CppState\n' + lean + '\nopen CompoundTest Proofs.CppState\n'
            calls, expected = [], []
            for a in range(-3, 4):
                for b in range(-3, 4):
                    q = (abs(a)//abs(b)) * (-1 if (a<0)!=(b<0) else 1) if b else 0
                    for i, value in enumerate([a+b,a-b,a*b,q,a-q*b]):
                        if i >= 3 and b == 0:
                            continue
                        calls.append((i,a,b)); expected.append(value)
                        lean += f'#guard (op{i}.call [⟨⟨32,true,false⟩,{a}⟩,⟨⟨32,true,false⟩,{b}⟩] [.reference 0,.reference 1]).map (fun r => (r.value,r.memory.map (·.value))) == some ({value},[{value},{b}])\n'
                for i, value in enumerate([a+a,0,a*a,1,0]):
                    if i>=3 and a==0:
                        continue
                    lean += f'#guard (op{i}.call [⟨⟨32,true,false⟩,{a}⟩] [.reference 0,.reference 0]).map (·.value) == some ({value})\n'
            cases = [(x,m) for x in [-9223372036854775808,-17,-1,0,1,17,9223372036854775807]
                     for m in [1,2,3,17,9223372036854775807]]
            for x,m in cases:
                lean += f'#guard (SafeModTest.safe_mod.call [] [.value ({x}),.value {m}]).map (·.value) == some ({x%m})\n'
            lean += '''#guard (wide.call [] [.value 4294967295,.value 4294967297]).map (·.value) == some 4294967295
#guard (promoted.call [] [.value 1,.value (-1)]).map (·.value) == some 0
#guard (promoted.call [] [.value 0,.value 2]).map (·.value) == some 1
#guard narrowing.call [] [.value (-2),.value 1] == none
#guard op0.call [⟨⟨32,true,false⟩,2147483647⟩,⟨⟨32,true,false⟩,1⟩] [.reference 0,.reference 1] == none
#guard op3.call [⟨⟨32,true,false⟩,-2147483648⟩,⟨⟨32,true,false⟩,-1⟩] [.reference 0,.reference 1] == none
#guard op4.call [⟨⟨32,true,false⟩,-2147483648⟩,⟨⟨32,true,false⟩,-1⟩] [.reference 0,.reference 1] == none
#guard SafeModTest.safe_mod.call [] [.value 7,.value 0] == none
'''
            self.check_lean(scratch, lean)
            source = scratch/'test.cpp'
            # Both actual imported and candidate headers, template first.
            source.write_text(f'#include "{ROOT/"experiments/library/cpp/template/small_template.hpp"}"\n'
                f'#include "{original}"\n#include "{candidate}"\nnamespace cp {{\n' + declarations +
                '\n}\nint main(){\n' + '\n'.join(
                    f'{{int a={a},b={b}; assert(cp::op{i}(a,b)==({v}));assert(a==({v}));assert(b==({b}));}}'
                    for (i,a,b),v in zip(calls,expected)) + '\n' + '\n'.join(
                    f'{{ll x={"(-9223372036854775807LL-1LL)" if x==-(1<<63) else str(x)+"LL"}, m={m}LL; assert(safe_mod(x,m)=={x%m}LL);assert(cp::safe_mod(x,m)=={x%m}LL);}}'
                    for x,m in cases) + '''
assert(cp::wide(4294967295U,4294967297UL)==4294967295U);
assert(!cp::promoted(true,-1)); assert(cp::promoted(false,2));
for(int a=-3;a<=3;++a){int x=a;assert(cp::op0(x,x)==2*a);x=a;assert(cp::op1(x,x)==0);x=a;assert(cp::op2(x,x)==a*a);if(a){x=a;assert(cp::op3(x,x)==1);x=a;assert(cp::op4(x,x)==0);}}
}''')
            binary = scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                '-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),
                str(source),'-o',str(binary)], check=True)
            subprocess.run([str(binary)],check=True)
            changed = self.lower('long safe_mod(long x,long m){x/=m;if(x<0){x+=m;}return x;}')
            self.check_lean(scratch, state_ir.emit_lean(changed, 'ChangedSafeMod') +
                '\n#guard (ChangedSafeMod.safe_mod.call [] [.value (-17),.value 3]).map (·.value) == some 1\n',
                success=False)

    def test_state_rules_do_not_depend_on_names(self):
        a = self.lower("int first(int &a,int b){if(a<b) a=b;return a;}")
        b = self.lower("int different(int &x,int y){if(x<y) x=y;return x;}")
        a["functions"][0]["name"] = b["functions"][0]["name"]
        self.assertEqual(a, b)


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.CppState"], cwd=ROOT, env=env, check=True)
    unittest.main()
