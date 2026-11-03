"""Integral template execution proofs, mixed conversions and source mutations."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
import template_ir
from test_scalar_ir import lean_environment
from offline import disable_network

HEADER=ROOT/'experiments/verification/template/update_extrema.hpp'
# Independent LP64 reference: spelling, width, signedness, rank, Lean constructor.
TYPES=[('bool',1,False,0,'boolean'),('int',32,True,1,'i32'),
       ('unsigned int',32,False,1,'u32'),('long',64,True,2,'signedLong'),
       ('unsigned long',64,False,2,'unsignedLong'),('long long',64,True,3,'signedLongLong'),
       ('unsigned long long',64,False,3,'unsignedLongLong')]

def convert(value,ty,checked=False):
    _,bits,signed,rank,_=ty
    if rank==0:return int(value!=0)
    if not signed:return value%(1<<bits)
    if -(1<<(bits-1))<=value<(1<<(bits-1)):return value
    if checked:return None
    rem=value%(1<<bits)
    return rem if rem<(1<<(bits-1)) else rem-(1<<bits)

def common(left,right):
    left=TYPES[1] if left[3]==0 else left
    right=TYPES[1] if right[3]==0 else right
    high,low=(left,right) if left[3]>=right[3] else (right,left)
    if high[2]==low[2] or not high[2] or high[1]>low[1]:return high
    return next(t for t in TYPES if t[3]==high[3] and not t[2])

def extremes(ty):
    if ty[3]==0:return [0,1]
    return [-(1<<(ty[1]-1)),0,1,(1<<(ty[1]-1))-1] if ty[2] else [0,1,(1<<ty[1])-1]

def literal(value):
    if value==-(1<<63):return '(-9223372036854775807LL-1)'
    return str(value)+('ULL' if value>(1<<63)-1 else 'LL')

class IntegralExecutionTests(unittest.TestCase):
    def test_mixed_boundary_values_cpp_and_generated_call_theorem(self):
        template_ir.apply_conversion_policy([],template_ir.SIGNED_CONVERSIONS[1])
        lake,env=lean_environment()
        proof='import Proofs.IntegralExtremaExecution\nopen Proofs.CppScalar Proofs.CppState Proofs.CppTemplate Proofs.IntegralExtremaExecution\n'
        native=f'#include "{HEADER}"\n#include <cassert>\nint main(){{\n'
        case=0
        for left in TYPES:
            for right in TYPES:
                la,rb=extremes(left),extremes(right)
                pairs=list(dict.fromkeys([(0,0),(la[0],rb[-1]),(la[-1],rb[0]),(la[-1],rb[-1])]))
                for a,b in pairs:
                    ac,bc=convert(a,common(left,right)),convert(b,common(left,right))
                    for minimum in [False,True]:
                        update=bc<ac if minimum else ac<bc
                        c=convert(b,left)
                        name='chmin' if minimum else 'chmax'
                        native+=f'{{{left[0]} a=static_cast<{left[0]}>({literal(a)});const {right[0]} b=static_cast<{right[0]}>({literal(b)});assert(cp::{name}(a,b)=={str(update).lower()});assert(a==static_cast<{left[0]}>({literal(c if update else a)}));assert(b==static_cast<{right[0]}>({literal(b)}));}}\n'
                        for policy in [False,True]:
                            converted=convert(b,left,checked=not policy)
                            cells=['⟨⟨1,false,true⟩,9⟩',f'⟨Integral.{right[4]}.type,({b})⟩','⟨⟨1,false,true⟩,9⟩',f'⟨Integral.{left[4]}.type,({a})⟩']
                            memory='['+','.join(cells)+']'
                            invocation=f'((program {str(minimum).lower()}).instantiate [.{left[4]},.{right[4]}] {str(policy).lower()}).bind (fun model => model.call {memory} [.reference 3,.reference 1])'
                            if update and converted is None:
                                proof+=f'example : {invocation} = none := by decide\n'
                            else:
                                dest=converted if update else a
                                expected=cells.copy();expected[3]=f'⟨Integral.{left[4]}.type,({dest})⟩'
                                extraA=int(left!=common(left,right));extraB=int(right!=common(left,right))
                                condition_nodes=3+extraA+extraB
                                assign_nodes=1+int(left!=right)
                                work=condition_nodes+(assign_nodes+5 if update else 4)
                                final='['+','.join(expected)+']'
                                cv=converted if converted is not None else 0
                                proof+=f'example : {invocation} = some ⟨{int(update)},{final},{work},{2+condition_nodes}⟩ := by\n'
                                proof+=f'  simpa [condition,assignment,conversion_nodes,conversionWork,Expr.nodes,commonIntegral,Integral.promote,Integral.rank,Integral.type,Integral.unsigned,List.set] using call_correct .{left[4]} .{right[4]} {str(policy).lower()} {str(minimum).lower()} {memory} 3 1 ({a}) ({b}) ({ac}) ({bc}) ({cv}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n'
                            case+=1
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='integral-execution-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';cpp=scratch/'test.cpp';binary=scratch/'test'
            lean.write_text(proof)
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
        self.assertGreater(case,600)

    def test_same_cell_for_every_builtin_type(self):
        lake,env=lean_environment()
        proof='import Proofs.IntegralExtremaExecution\nopen Proofs.CppScalar Proofs.CppState Proofs.CppTemplate Proofs.IntegralExtremaExecution\n'
        native=f'#include "{HEADER}"\n#include <cassert>\nint main(){{\n'
        for ty in TYPES:
            nodes=5 if ty[3]==0 else 3
            for value in extremes(ty):
                memory=f'[⟨⟨1,false,true⟩,9⟩,⟨Integral.{ty[4]}.type,({value})⟩]'
                for minimum in [False,True]:
                    name='chmin' if minimum else 'chmax'
                    native+=f'{{{ty[0]} a=static_cast<{ty[0]}>({literal(value)});assert(!cp::{name}(a,a));assert(a==static_cast<{ty[0]}>({literal(value)}));}}\n'
                    for policy in [False,True]:
                        proof+=f'example : ((program {str(minimum).lower()}).instantiate [.{ty[4]},.{ty[4]}] {str(policy).lower()}).bind (fun model => model.call {memory} [.reference 1,.reference 1]) = some ⟨0,{memory},{nodes+4},{nodes+2}⟩ := by\n'
                        proof+=f'  simpa [condition,conversion_nodes,conversionWork,Expr.nodes,commonIntegral,Integral.promote,Integral.rank,Integral.type,Integral.unsigned] using same_type_alias .{ty[4]} {str(policy).lower()} {str(minimum).lower()} {memory} 1 ({value}) (by decide) (by decide)\n'
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='integral-alias-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';cpp=scratch/'test.cpp';binary=scratch/'test'
            lean.write_text(proof)
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_primary_source_mutations_fail_execution_proofs(self):
        lake,env=lean_environment()
        execution=(ROOT/'Proofs/IntegralExtremaExecution.lean').read_text().replace('import Proofs.IntegralExtrema\n','')
        with tempfile.TemporaryDirectory(prefix='integral-execution-mutations-') as directory:
            scratch=Path(directory);header=scratch/'helper.hpp';lean=scratch/'test.lean'
            for change in [None,('a < b','a <= b'),('b < a','b <= a'),('a = b','a = a'),('return 1','return 0')]:
                with self.subTest(change=change):
                    header.write_text(HEADER.read_text() if change is None else HEADER.read_text().replace(*change))
                    model=template_ir.emit_lean(template_ir.lower_source(header))
                    # Lean imports must precede all declarations.
                    imports='\n'.join(re.findall(r'^import .*$',model+'\n'+execution,flags=re.M))+'\n'
                    lean.write_text(imports+re.sub(r'^import .*\n','',model+'\n'+execution,flags=re.M))
                    checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                    if change is None:self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
                    else:self.assertNotEqual(checked.returncode,0)

if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.IntegralExtremaExecution'],cwd=ROOT,env=env,check=True)
    unittest.main()
