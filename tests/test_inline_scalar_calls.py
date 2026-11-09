"""`[[gnu::always_inline]]` scalar helpers are inlined into their callers by the common generator."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
import nested_ir
from offline import disable_network

PRELUDE = '#include <vector>\nnamespace cp {\n'
HELPER = ('{attr} inline unsigned long long twice_mod(unsigned long long a, unsigned long long m) {{\n'
          '  unsigned long long r = a + a;\n  if (a >= m - a) {{\n    r = a - (m - a);\n  }}\n  return r;\n}}\n')
USER = ('inline unsigned long long f(unsigned long long x, unsigned long long m) {\n'
        '  unsigned long long y = twice_mod(x, m);\n  return y;\n}\n')

CONDITIONALS = '''[[gnu::always_inline]] inline long long mark(long long &trace,long long value){
 trace=trace*10+value; return value;
}
[[gnu::always_inline]] inline bool guard(long long &count,bool value){
 count=count+1; return value;
}
[[gnu::always_inline]] inline long long divide(long long n){return 7/n;}
inline long long nested(bool a,bool b){
 long long count=0,trace=0;
 long long value=guard(count,a)?mark(trace,2):(guard(count,b)?mark(trace,3):mark(trace,4));
 return value+10*trace+100*count;
}
inline long long condition_only(bool a){
 long long count=0;long long value=guard(count,a)?7:8;return value+100*count;
}
inline long long selected_division(bool take,long long n){return take?divide(n):17;}
inline long long discarded_division(long long n){divide(n);return 17;}
[[gnu::always_inline]] inline long long increment(long long n){return n+1;}
inline long long discarded_overflow(long long n){increment(n);return 19;}
'''


class InlineScalarCallTests(unittest.TestCase):
    def lower(self, text, scratch):
        path = scratch / 'case.hpp'
        path.write_text(text)
        return nested_ir.lower_source(path, [scratch])

    def test_always_inline_removes_the_call(self):
        with tempfile.TemporaryDirectory(prefix='inline-scalar-') as directory:
            scratch = Path(directory)
            ir = self.lower(PRELUDE + HELPER.format(attr='[[gnu::always_inline]]') + USER + '}\n', scratch)
            text = nested_ir.emit_lean(ir, 'Proofs.CaseInstance')
            self.assertNotIn('invokeScalar', text)
            self.assertEqual(ir['callees'], [])
            plain = nested_ir.emit_lean(self.lower(PRELUDE + HELPER.format(attr='') + USER + '}\n', scratch),
                                        'Proofs.CaseInstance')
            self.assertIn('invokeScalar', plain)

    def test_early_return_is_rejected(self):
        helper = ('[[gnu::always_inline]] inline unsigned long long g(unsigned long long a) {\n'
                  '  if (a == 0) {\n    return 1;\n  }\n  return a;\n}\n')
        user = ('inline unsigned long long f(unsigned long long x) {\n'
                '  unsigned long long y = g(x);\n  return y;\n}\n')
        with tempfile.TemporaryDirectory(prefix='inline-scalar-') as directory:
            with self.assertRaises(Exception):
                self.lower(PRELUDE + helper + user + '}\n', Path(directory))

    def test_conditional_calls_preserve_selected_branch_and_condition_count(self):
        import test_scalar_class_delegation as scalar_checks
        with tempfile.TemporaryDirectory(prefix='inline-conditional-') as directory:
            scratch=Path(directory)
            ir=self.lower(PRELUDE+CONDITIONALS+'}\n',scratch)
            proof='import Proofs.MonoidLazyCall\n'+nested_ir.emit_lean(ir,'InlineConditionals')
            fixture=(ROOT/'tests/lean/inline_scalar_conditionals.lean').read_text()
            roots=['ConditionalCallAudit.'+line.split()[1] for line in fixture.splitlines()
                   if line.startswith('theorem ')]
            self.assertEqual(len(roots),13)
            scalar_checks.ScalarDelegationTests().kernel(scratch,'InlineConditionalCheck',roots,proof+fixture)
            main=scratch/'main.cpp'
            main.write_text('#include "case.hpp"\nint main(int argc,char**){\n'
                'if(argc==2)return cp::discarded_division(0)==17?0:1;'
                'if(argc==3)return cp::discarded_overflow(9223372036854775807LL)==19?0:1;'
                'return cp::nested(true,true)==122 && cp::nested(true,false)==122 && '
                'cp::nested(false,true)==233 && cp::nested(false,false)==244 && '
                'cp::condition_only(true)==107 && cp::condition_only(false)==108 && '
                'cp::selected_division(false,0)==17 && cp::selected_division(true,2)==3 && '
                'cp::discarded_division(2)==17 && cp::discarded_overflow(0)==19 ? 0:1;\n}\n')
            exe=scratch/'native'
            subprocess.run(['g++','-std=c++17','-O0','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(main),'-o',str(exe)],check=True,timeout=60)
            subprocess.run([str(exe)],check=True,timeout=10)
            for args,diagnostic in [(['division'],'division by zero'),(['overflow','unused'],'signed integer overflow')]:
                failed=subprocess.run([str(exe),*args],capture_output=True,text=True,timeout=10)
                self.assertNotEqual(failed.returncode,0)
                self.assertIn(diagnostic,failed.stderr)

    def test_conditional_calls_keep_reference_object_and_short_circuit_boundaries(self):
        cases=[('[[gnu::always_inline]] inline int& get(int &x){return x;}\n'
                'inline int f(bool b,int &x,int &y){return b?get(x):get(y);}\n',
                'inlined conditional calls require a scalar prvalue result'),
               ('[[gnu::always_inline]] inline std::vector<int> make(int x){return std::vector<int>(1,x);}\n'
                'inline std::vector<int> f(bool b){return b?make(1):make(2);}\n',
                'unsupported scalar type:'),
               ('[[gnu::always_inline]] inline bool yes(){return true;}\n'
                'inline bool f(bool b){return b&&yes();}\n',
                'calls in conditionally evaluated operands cannot be inlined')]
        with tempfile.TemporaryDirectory(prefix='inline-conditional-boundaries-') as directory:
            for source,error in cases:
                with self.subTest(error=error),self.assertRaisesRegex(ValueError,error):
                    self.lower(PRELUDE+source+'}\n',Path(directory))


if __name__ == '__main__':
    disable_network()
    unittest.main()
