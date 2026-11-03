"""Explicit compiler conversion contract, checked arithmetic, signed source."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from scalar_ir import lower_source as scalar_source,emit_lean as scalar_lean,SIGNED_CONVERSIONS
from state_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

POLICY=SIGNED_CONVERSIONS[1]
I64_MIN=-(1<<63);I64_MAX=(1<<63)-1;U64_MAX=(1<<64)-1

def decode(x,width=64):
    r=x%(1<<width)
    return r if r<(1<<(width-1)) else r-(1<<width)

def literal(x):
    return '(-9223372036854775807LL-1)' if x==I64_MIN else f'({x}LL)' if x<0 else f'{x}ULL'


class TargetCastTests(unittest.TestCase):
    def lean(self,scratch,text):
        lake,env=lean_environment();p=scratch/'test.lean';p.write_text(text)
        result=subprocess.run([lake,'env','lean',str(p)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def native(self,scratch,source,checks,includes=()):
        p=scratch/'native.cpp';binary=scratch/'native'
        p.write_text('#include <cassert>\n'+source+'\nint main(){'+''.join(checks)+'}\n')
        subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                        *[x for d in includes for x in ('-I',str(d))],str(p),'-o',str(binary)],check=True)
        subprocess.run([str(binary)],check=True)

    def test_explicit_and_implicit_conversions_match_fixed_cpp(self):
        sources=[('unsigned long long',[0,1,(1<<31)-1,1<<31,(1<<32)-1,1<<32,(1<<63)-1,1<<63,U64_MAX]),
                 ('long long',[I64_MIN,-(1<<32),-(1<<31)-1,-(1<<31),-1,0,1,(1<<31)-1,1<<31,I64_MAX]),
                 ('unsigned int',[0,1,(1<<31)-1,1<<31,(1<<32)-1])]
        targets=[('int',32),('long long',64)]
        functions=[];cases=[]
        for si,(src,values) in enumerate(sources):
            for ti,(target,width) in enumerate(targets):
                for form in range(3):
                    name=f'cast_{si}_{ti}_{form}'
                    expression=(f'({target})x',f'static_cast<{target}>(x)',f'target_{ti}(x)')[form]
                    functions.append(f'{target} {name}({src} x){{return {expression};}}')
                    cases.extend((name,src,x,decode(x,width)) for x in values)
        code='using target_0=int;using target_1=long long;namespace cp {'+''.join(functions)+'}'
        with tempfile.TemporaryDirectory() as directory:
            scratch=Path(directory);p=scratch/'source.cpp';p.write_text(code)
            checked=scalar_source(p);selected=scalar_source(p,POLICY)
            self.assertNotIn('signed_conversion',checked);self.assertEqual(selected['signed_conversion'],POLICY)
            guards='';native=[]
            for name,src,x,expected in cases:
                guards+=f'#guard (Target.{name}.call [{x}]).map (·.value) == some ({expected})\n'
                native.append(f'assert(cp::{name}(static_cast<{src}>({literal(x)}))=={literal(expected)});')
            self.lean(scratch,scalar_lean(selected,'Target')+guards)
            self.native(scratch,code,native)
            self.lean(scratch,scalar_lean(checked,'Checked')+'\n#guard Checked.cast_0_0_0.call [2147483648] == none\n')
            # Source-range preserving casts retain the existing constructor.
            self.assertEqual(selected['functions'][-1],checked['functions'][-1])
            with self.assertRaisesRegex(ValueError,'unsupported signed conversion contract'):scalar_source(p,'wrap-arithmetic')
            actual=subprocess.check_output
            def other_target(command, **kwargs):
                return 'aarch64-linux-gnu\n' if command==['g++','-dumpmachine'] else actual(command,**kwargs)
            with patch('scalar_ir.subprocess.check_output',side_effect=other_target):
                with self.assertRaisesRegex(ValueError,'unsupported target'):scalar_source(p,POLICY)

    def test_assignments_argument_return_and_arithmetic_safety(self):
        code='''namespace cp {
int helper(int x){return x;}
int argument(unsigned long long x){return helper(x);}
int local(unsigned long long x){int y=x;y=x;return y;}
int compound(unsigned long long x){int y=1;y+=x;return y;}
long long result(unsigned long long x){return x;}
int add(int x){return x+1;}
int neg(int x){return -x;}
int mul(int x){return x*2;}
int div(int x){return x/(-1);}
int rem(int x){return x%(-1);}
}'''
        with tempfile.TemporaryDirectory() as directory:
            scratch=Path(directory);p=scratch/'source.cpp';p.write_text(code)
            ir=lower_source(p,signed_conversion=POLICY);guards='';native=[]
            for x in (0,1,1<<31,(1<<32)-1,1<<32,1<<63,U64_MAX):
                for name,width,value in [('argument',32,x),('local',32,x),('compound',32,x+1),('result',64,x)]:
                    expected=decode(value,width)
                    guards+=f'#guard (StateTarget.{name}.call [] [.value {x}]).map (·.value) == some ({expected})\n'
                    native.append(f'assert(cp::{name}({x}ULL)=={literal(expected)});')
            guards+='''#guard StateTarget.add.call [] [.value 2147483647] == none
#guard StateTarget.neg.call [] [.value (-2147483648)] == none
#guard StateTarget.mul.call [] [.value 2147483647] == none
#guard StateTarget.div.call [] [.value (-2147483648)] == none
#guard StateTarget.rem.call [] [.value (-2147483648)] == none
'''
            self.lean(scratch,emit_lean(ir,'StateTarget')+guards)
            self.native(scratch,code,native)

    def test_original_signed_source_negative_and_extreme_results(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        includes=[ROOT/'experiments/library/cpp']
        ir=lower_source(source,None,includes,POLICY)
        checked=lower_source(source,'safe_mod',includes)
        self.assertEqual(ir['functions'][0],checked['functions'][0])
        generated=emit_lean(ir,'SignedTarget')
        self.assertEqual(generated,(ROOT/'experiments/verification/number/floor_sum_signed_gcc_model.lean').read_text())
        cases=[]
        for n in range(5):
            for m in range(1,6):
                for a in range(-2,3):
                    for b in range(-2,3):cases.append((n,m,a,b,sum((a*i+b)//m for i in range(n))))
        for n in (0,1,2,9):
            for m in (1,2,(1<<31)-1):
                for a,b in ((I64_MIN,I64_MIN),(I64_MAX,I64_MAX),(I64_MIN,I64_MAX),(I64_MAX,I64_MIN),(0,-1)):
                    cases.append((n,m,a,b,sum((a*i+b)//m for i in range(n))))
        for a,b in ((I64_MIN,I64_MIN),(I64_MAX,I64_MAX),(I64_MIN,I64_MAX),(0,-1)):
            n=(1<<32)-1;cases.append((n,1,a,b,a*n*(n-1)//2+b*n))
        guards='';native=[]
        for n,m,a,b,total in cases:
            expected=decode(total)
            guards+=f'#guard (match SignedTarget.floor_sum.callFuel 4000 [] [.value {n},.value {m},.value ({a}),.value ({b})] with | .finished r => r.value == ({expected}) && r.memory == [] | _ => false)\n'
            native.append(f'assert(floor_sum({n}LL,{m}LL,{literal(a)},{literal(b)})=={literal(expected)});')
        guards+='''#guard SignedTarget.floor_sum.callFuel 4000 [] [.value (-1),.value 1,.value 0,.value 0] == .fault
#guard SignedTarget.floor_sum.callFuel 4000 [] [.value 1,.value 0,.value 0,.value 0] == .fault
'''
        with tempfile.TemporaryDirectory() as directory:
            scratch=Path(directory);self.lean(scratch,generated+guards)
            self.native(scratch,'#include "template/small_template.hpp"\n#include "number_theory/floor_sum.hpp"',native,includes)


if __name__=='__main__':
    disable_network();unittest.main()
