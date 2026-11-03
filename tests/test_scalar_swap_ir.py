"""Scalar std::swap contracts and an actual imported floor_sum loop."""

from pathlib import Path
import math
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from state_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network


class SwapTests(unittest.TestCase):
    def test_included_swap_is_checked_in_the_callers_translation_unit(self):
        with tempfile.TemporaryDirectory(prefix='included-swap-') as directory:
            scratch=Path(directory)
            (scratch/'helpers').mkdir();(scratch/'entry').mkdir()
            helper=scratch/'helpers/swap.hpp';source=scratch/'entry/main.cpp'
            helper.write_text('#pragma once\n#include <utility>\nnamespace cp {int first(int a,int b){std::swap(a,b);return a;}}\n')
            text='#include "../helpers/swap.hpp"\nnamespace cp {int f(int a,int b){return first(a,b);}}\n'
            source.write_text(text)
            ir=lower_source(source)
            self.assertEqual([f['name'] for f in ir['functions']],['first','f'])
            proof=scratch/'test.lean'
            proof.write_text(emit_lean(ir,'IncludedSwap')+'\nopen Proofs.CppState\n'
                '#guard (IncludedSwap.f.call [] [.value 3,.value (-8)]).map (fun r => (r.value,r.memory.isEmpty)) == some (-8,true)\n')
            lake,env=lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            # The header's standalone compilation would miss this specialization.
            source.write_text('#include <utility>\nnamespace std {template<>void swap<int>(int&a,int&b)noexcept{a=0;b=0;}}\n'+text)
            with self.assertRaises(ValueError):lower_source(source)
            source.write_text(text)
            helper.write_text('#pragma once\n#include <utility>\nnamespace cp {void swap(int&a,int&b){a=0;b=0;} int first(int a,int b){swap(a,b);return a;}}\n')
            with self.assertRaisesRegex(ValueError,'identity probe'):lower_source(source)

    def test_reference_updates_aliases_bounds_and_namesakes(self):
        with tempfile.TemporaryDirectory(prefix='scalar-swap-') as directory:
            scratch=Path(directory);source=scratch/'test.cpp';proof=scratch/'test.lean';binary=scratch/'test'
            text='''#include <utility>
using std::swap;
namespace cp {
int f(int &a,int &b){std::swap(a,b);return a;}
unsigned long wide(unsigned long &a,unsigned long &b){swap(a,b);return a;}
bool truth(bool &a,bool &b){std::swap<bool>(a,b);return a;}
}'''
            source.write_text(text);ir=lower_source(source)
            lean=emit_lean(ir,'SwapTest')+'\nopen SwapTest Proofs.CppState\n'
            for a in [-2147483648,-1,0,1,2147483647]:
                for b in [-2147483648,-1,0,1,2147483647]:
                    lean+=f'#guard (f.call [⟨⟨32,true,false⟩,{a}⟩,⟨⟨32,true,false⟩,{b}⟩] [.reference 0,.reference 1]).map (fun r => (r.value,r.memory.map (·.value),r.work,r.peak)) == some ({b},[{b},{a}],8,5)\n'
                lean+=f'#guard (f.call [⟨⟨32,true,false⟩,{a}⟩] [.reference 0,.reference 0]).map (fun r => (r.value,r.memory.map (·.value),r.work,r.peak)) == some ({a},[{a}],8,5)\n'
            lean+='''#guard (wide.call [⟨⟨64,false,false⟩,0⟩,⟨⟨64,false,false⟩,18446744073709551615⟩] [.reference 0,.reference 1]).map (·.value) == some 18446744073709551615
#guard (truth.call [⟨⟨1,false,true⟩,0⟩,⟨⟨1,false,true⟩,1⟩] [.reference 0,.reference 1]).map (·.value) == some 1
#guard (Stmt.swap 0 1).run ⟨[⟨⟨32,true,false⟩,1⟩],[⟨0,false⟩,⟨0,true⟩],0,1,0⟩ == none
#guard (Stmt.swap 0 1).run ⟨[⟨⟨32,true,false⟩,1⟩],[⟨0,true⟩,⟨1,true⟩],0,1,0⟩ == none
'''
            proof.write_text(lean);lake,env=lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            source.write_text('#include <cassert>\n#include <climits>\n'+text+'''
int main(){for(int a:{INT_MIN,-1,0,1,INT_MAX}){for(int b:{INT_MIN,-1,0,1,INT_MAX}){int x=a,y=b;assert(cp::f(x,y)==b);assert(x==b&&y==a);}int x=a;assert(cp::f(x,x)==a);assert(x==a);}
unsigned long a=0,b=ULONG_MAX;assert(cp::wide(a,b)==ULONG_MAX);assert(a==ULONG_MAX&&b==0);bool x=false,y=true;assert(cp::truth(x,y));assert(x&&!y);}
''')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            for fake in [
                'void swap(int&a,int&b){a=0;b=0;} namespace cp {int f(int&a,int&b){swap(a,b);return a;}}',
                'namespace user {template<class T>void swap(T&a,T&b){a=0;b=0;}} namespace cp {int f(int&a,int&b){user::swap(a,b);return a;}}',
                'namespace std {template<>void swap<int>(int&a,int&b)noexcept{a=0;b=0;}} namespace cp {int f(int&a,int&b){std::swap(a,b);return a;}}']:
                source.write_text('#include <utility>\n'+fake)
                with self.subTest(fake=fake),self.assertRaises(ValueError):lower_source(source)

    def test_original_floor_sum_unsigned_generates_and_matches_finite_inputs(self):
        original=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        ir=lower_source(original,'floor_sum_unsigned',[ROOT/'experiments/library/cpp'])
        cases=[(n,m,a,b) for n in range(6) for m in range(1,6) for a in range(6) for b in range(6)]
        cases += [(3,4294967295,18446744073709551615,18446744073709551615),
                  (7,1,18446744073709551615,18446744073709551615)]
        expected=[sum((a*i+b)//m for i in range(n))%(1<<64) for n,m,a,b in cases]
        with tempfile.TemporaryDirectory(prefix='floor-sum-ir-') as directory:
            scratch=Path(directory);proof=scratch/'test.lean';source=scratch/'test.cpp';binary=scratch/'test'
            guards=[f'#guard (match FloorSumTest.floor_sum_unsigned.callFuel 200 [] [.value {n},.value {m},.value {a},.value {b}] with | .finished r => r.value == {value} && r.memory.isEmpty | _ => false)'
                    for (n,m,a,b),value in zip(cases,expected)]
            guards += [f'#guard Proofs.FloorSumArithmetic.directSum {m} {a} {b} {n} % Proofs.FloorSumArithmetic.wordLimit == {value}'
                       for (n,m,a,b),value in zip(cases,expected)]
            guards += [f'#guard Proofs.FloorSumReciprocity.mathRun {n} {m} {a} {b} 0 == {value}'
                       for (n,m,a,b),value in zip(cases,expected)]
            guards+=['#guard FloorSumTest.floor_sum_unsigned.callFuel 200 [] [.value 1,.value 0,.value 1,.value 0] == .fault']
            proof.write_text('import Proofs.FloorSumReciprocity\n'+emit_lean(ir,'FloorSumTest')+'\nopen Proofs.CppState Proofs.CppLoop\n'+'\n'.join(guards))
            lake,env=lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            source.write_text(f'#include "{ROOT/"experiments/library/cpp/template/small_template.hpp"}"\n#include "{original}"\nint main(){{\n'+'\n'.join(
                f'assert(floor_sum_unsigned({n}ULL,{m}ULL,{a}ULL,{b}ULL)=={value}ULL);' for (n,m,a,b),value in zip(cases,expected))+'\n}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_floor_sum_domain_boundaries_and_unrestricted_counterexample(self):
        limit=1<<32;word=1<<64
        triangle=lambda n:n*(n-1)//2
        # Closed forms keep the reference independent of the Euclidean loop and
        # allow billions of summands to be checked without enumerating them.
        cases=[(n,1,word-1,word-1,((word-1)*(triangle(n)+n))%word)
               for n in [0,1,limit-1]]
        n=limit-1
        cases += [(n,n,n,0,triangle(n)),
                  (n,n,n-1,n-1,triangle(n)),
                  (n,n,word-1,word-1,((limit+1)*(triangle(n)+n))%word),
                  (1,n,word-1,word-1,(word-1)//n)]
        fibonacci=[(1836311903,1134903170),(2971215073,1836311903)]
        for m,a in fibonacci:
            self.assertEqual(math.gcd(m,a),1)
            # Pairing i with m-i gives a-1 for every nonzero i when gcd=1.
            cases.append((m,m,a,0,(m-1)*(a-1)//2))
        outside=limit+1
        actual=(outside*(outside-1)%word)//2
        mathematical=triangle(outside)%word
        self.assertNotEqual(actual,mathematical)
        original=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        with tempfile.TemporaryDirectory(prefix='floor-sum-domain-') as directory:
            scratch=Path(directory);proof=scratch/'test.lean';source=scratch/'test.cpp';binary=scratch/'test'
            guards=[f'#guard (match floor_sum_unsigned.callFuel 200 [] [.value {n},.value {m},.value {a},.value {b}] with | .finished r => r.value == {value} && r.memory.isEmpty | _ => false)'
                    for n,m,a,b,value in cases+[(outside,1,1,0,actual)]]
            guards += [f'#guard Proofs.FloorSumReciprocity.mathRun {n} {m} {a} {b} 0 == {value}'
                       for n,m,a,b,value in cases]
            guards.append(f'#guard Proofs.FloorSumReciprocity.mathRun {outside} 1 1 0 0 == {mathematical}')
            for m,a in fibonacci:
                modulus,coefficient=m,a;count=0
                while modulus:
                    modulus,coefficient=coefficient%modulus,modulus
                    count+=1
                guards.append(f'#guard Proofs.FloorSumArithmetic.rounds {m} {m} {a} 0 == {count}')
                guards.append(f'#guard (match floor_sum_unsigned.callFuel 200 [] [.value {m},.value {m},.value {a},.value 0] with | .finished r => r.work ≤ 64*160 && r.peak ≤ 25 | _ => false)')
            proof.write_text('import Proofs.FloorSumReciprocity\nopen Proofs.FloorSumUnsignedInstance Proofs.CppState Proofs.CppLoop\n'+'\n'.join(guards))
            lake,env=lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            source.write_text(f'#include "{ROOT/"experiments/library/cpp/template/small_template.hpp"}"\n#include "{original}"\nint main(){{\n'+'\n'.join(
                f'assert(floor_sum_unsigned({n}ULL,{m}ULL,{a}ULL,{b}ULL)=={value}ULL);' for n,m,a,b,value in cases+[(outside,1,1,0,actual)])+
                f'\nassert(floor_sum_unsigned({outside}ULL,1ULL,1ULL,0ULL)!={mathematical}ULL);\n}}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp'),str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)


if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.FloorSumReciprocity'],cwd=ROOT,env=env,check=True)
    unittest.main()
