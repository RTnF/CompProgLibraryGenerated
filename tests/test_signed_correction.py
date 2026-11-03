"""Check the mixed signed/unsigned correction quotient against C++ and Lean."""
from pathlib import Path
import re
import resource
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from state_ir import lower_source,emit_lean
from scalar_ir import SIGNED_CONVERSIONS
from test_scalar_ir import lean_environment
from offline import disable_network

class CorrectionTests(unittest.TestCase):


    def test_original_asserts_and_initial_preparation(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        original=source.read_text();includes=[ROOT/'experiments/library/cpp']
        generated=emit_lean(lower_source(source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
        self.assertEqual(generated,(ROOT/'experiments/verification/number/floor_sum_signed_gcc_model.lean').read_text())
        assertions=re.findall(r'assert\((.*?)\);',original)
        self.assertEqual(assertions,['0 <= n && n < (1ll << 32)','1 <= m && m < (1ll << 32)'])
        branches=[re.search(r'if \('+label+r' < 0\) \{.*?\n  \}',original,re.S).group() for label in ['a','b']]
        proof='import Proofs.FloorSumSignedPrefix\n'+generated+'''
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumSignedPrefix Proofs.FloorSumSignedBranch Proofs.FloorSumSignedCorrection Proofs.FloorSumArithmetic
-- Keep the source's sequence structure; remove only the later return suffix.
def selectedPrefix : Stmt := match SignedTarget.floor_sum.body with
  | .scope (.sequence first (.sequence second (.sequence initial _))) =>
      .sequence first (.sequence second initial)
  | _ => .skip
def selectedPreparation : Stmt := match SignedTarget.floor_sum.body with
  | .scope (.sequence first (.sequence second (.sequence initial (.sequence a (.sequence b _))))) =>
      .sequence first (.sequence second (.sequence initial (.sequence a (.sequence b .skip))))
  | _ => .skip
example : selectedPrefix = inputPrefix := rfl
example : selectedPreparation = preparation := rfl
def callerCells : List Cell := [⟨signed64,-8⟩,⟨⟨64,false,false⟩,9223372036854775808⟩]
'''
        native='#include <cassert>\n#include <cstdlib>\n#include "number_theory/floor_sum.hpp"\nstruct NativeResult{ull ans;ll a;ll b;};\n'
        native+='NativeResult prepare(ll n,ll m,ll a,ll b){'+''.join('assert('+a+');' for a in assertions)+'ull ans=0;'+''.join(branches)+'return {ans,a,b};}\n'
        invalid=[(-1,1),(1,0),(1,-1),(1<<32,1),(1,1<<32)]
        native+='int main(int argc,char**argv){if(argc>1){ll cases[][2]={' + ','.join('{'+str(n)+'LL,'+str(m)+'LL}' for n,m in invalid)+'};int i=std::atoi(argv[1]);prepare(cases[i][0],cases[i][1],0,0);return 0;}\n'
        cases=[(n,m,a,b) for n in [0,1,4294967295] for m in [1,4294967295]
               for a,b in [(-(1<<63),(1<<63)-1),((1<<63)-1,-(1<<63)),(-1,-1),(0,0),(1,1)]]
        for n,m,a,b in cases:
            na=a%m if a<0 else a;nb=b%m if b<0 else b
            ans=(-n*(n-1)//2*(-(a//m))*(a<0)-n*(-(b//m))*(b<0))%(1<<64)
            wa=(11 if a%m==0 else 15)+39 if a<0 else 5
            wb=(11 if b%m==0 else 15)+30 if b<0 else 5
            work=17+31+wa+wb
            start=f'(Proofs.FloorSumSignedPrefix.parameterState {n} {m} ({a}) ({b}) callerCells 17 1 10)'
            final=f'(mainState {n} {m} {na} {nb} {ans} callerCells {work} 1 finalPeak)'
            proof+=f'example : runFuel 6 inputPrefix {start} = .finished ⟨mainState {n} {m} ({a}) ({b}) 0 callerCells 48 1 15,none,false⟩ := by\n'
            proof+=f'  have result := prefix_runs {n} {m} ({a}) ({b}) callerCells 17 1 10 (by decide) (by decide) (by decide) (by decide) (by decide)\n'
            proof+='  simpa [callerCells] using result\n'
            proof+=f'example : ∃ finalPeak, runFuel 20 preparation {start} = .finished ⟨{final},none,false⟩ ∧ finalPeak ≤ 36 := by\n'
            proof+=f'  obtain ⟨p,done,bound,_,_,_⟩ := preparation_runs {n} {m} ({a}) ({b}) callerCells 17 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n'
            proof+='  exact ⟨p,by simpa [normalizedCoefficient,correctedAns,normalizationWork,Proofs.SafeModFrame.bodyWork,triangle,Proofs.FloorSumArithmetic.wordLimit] using done,by simpa [callerCells] using bound⟩\n'
            proof+=f'#guard (match runFuel 20 selectedPreparation {start} with | .finished step => step.state.memory == callerCells ++ [⟨signed64,{n}⟩,⟨signed64,{m}⟩,⟨signed64,{na}⟩,⟨signed64,{nb}⟩,⟨⟨64,false,false⟩,{ans}⟩] && step.state.bindings.length == 5 && step.state.work == {work} && step.state.baseMemory == 1 && step.state.peak ≤ 36 | _ => false)\n'
            def cppint(x):return '(-9223372036854775807LL-1)' if x==-(1<<63) else f'({x}LL)'
            native+=f'{{auto r=prepare({n}LL,{m}LL,{cppint(a)},{cppint(b)});assert(r.ans=={ans}ULL);assert(r.a=={na}LL);assert(r.b=={nb}LL);}}\n'
        for n,m in invalid:
            proof+=f'#guard runFuel 20 selectedPreparation (Proofs.FloorSumSignedPrefix.parameterState ({n}) ({m}) 0 0 callerCells 17 1 10) == .fault\n'
        proof+='#guard runFuel 3 selectedPrefix (Proofs.FloorSumSignedPrefix.parameterState 0 1 0 0 callerCells 17 1 10) == .exhausted\n'
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='signed-prefix-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';lean.write_text(proof)
            lake,env=lean_environment()
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            changed_source=scratch/'changed.hpp'
            for changed in [original.replace('assert(0 <= n','assert(1 <= n'),original.replace('ull ans = 0','ull ans = 1')]:
                changed_source.write_text(changed)
                mutated=emit_lean(lower_source(changed_source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
                lean.write_text(proof.replace(generated,mutated,1))
                rejected=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
            cpp=scratch/'native.cpp';binary=scratch/'native';cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(includes[0]),str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            for index in range(len(invalid)):
                rejected=subprocess.run([str(binary),str(index)],capture_output=True,text=True,
                    preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_CORE,(0,0)))
                self.assertNotEqual(rejected.returncode,0)
                self.assertIn('Assertion',rejected.stderr)

    def test_original_normalization_branches_and_scope_restoration(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        original=source.read_text();includes=[ROOT/'experiments/library/cpp']
        generated=emit_lean(lower_source(source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
        self.assertEqual(generated,(ROOT/'experiments/verification/number/floor_sum_signed_gcc_model.lean').read_text())
        branches=[re.search(r'if \('+label+r' < 0\) \{.*?\n  \}',original,re.S).group() for label in ['a','b']]
        proof='import Proofs.FloorSumSignedBranch\n'+generated+'''
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumSignedBranch Proofs.FloorSumSignedCorrection Proofs.FloorSumArithmetic Proofs.FloorSumState
-- Ignore invoked bodies: their variable slots belong to the callee.
def normalizationBranches : Stmt → List Stmt
  | .branch (.binary ty .lt (.variable vx slot) right) yes .skip =>
      [.branch (.binary ty .lt (.variable vx slot) right) yes .skip]
  | .scope s => normalizationBranches s
  | .sequence a b => normalizationBranches a ++ normalizationBranches b
  | .branch _ a b => normalizationBranches a ++ normalizationBranches b
  | _ => []
example : normalizationBranches SignedTarget.floor_sum.body =
  [normalizationBranch aCorrectionExpression 2,normalizationBranch bCorrectionExpression 3] := rfl
-- Reassemble the selected prefix in the order from the original body.
def selectedSequence : Stmt := match normalizationBranches SignedTarget.floor_sum.body with
  | [a,b] => .sequence a (.sequence b .skip)
  | _ => .skip
example : selectedSequence = normalizationSequence := rfl
def callerCells : List Cell := [⟨signed64,-8⟩,⟨unsigned64,9223372036854775808⟩]
'''
        native='#include <cassert>\n#include "number_theory/floor_sum.hpp"\nstruct NativeResult{ull ans;ll a;ll b;};\n'
        native+='NativeResult normalize(ll n,ll m,ll a,ll b,ull ans){'+''.join(branches)+'return {ans,a,b};}\nint main(){\n'
        cases=[(n,m,a,b,ans) for n in [0,4294967295] for m in [1,4294967295]
               for a,b in [(-1,-1),(-(1<<63),-1),(0,0),(1,-1),(-1,1),((1<<63)-1,(1<<63)-1)]
               for ans in [0,(1<<64)-1]]
        for n,m,a,b,ans in cases:
            na=a%m if a<0 else a;nb=b%m if b<0 else b
            total=(ans-(n*(n-1)//2)*(-(a//m))*(a<0)-n*(-(b//m))*(b<0))%(1<<64)
            wa=(11 if a%m==0 else 15)+39 if a<0 else 5
            wb=(11 if b%m==0 else 15)+30 if b<0 else 5
            work=17+wa+wb
            start=f'(mainState {n} {m} ({a}) ({b}) {ans} callerCells 17 1 10)'
            final=f'(mainState {n} {m} {na} {nb} {total} callerCells {work} 1 finalPeak)'
            proof+=f'example : ∃ finalPeak, runFuel 17 normalizationSequence {start} = .finished ⟨{final},none,false⟩ ∧ finalPeak ≤ 36 := by\n'
            proof+=f'  obtain ⟨p,done,bound,_,_,_⟩ := both_normalizations {n} {m} ({a}) ({b}) {ans} callerCells 17 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n'
            proof+='  exact ⟨p,by simpa [normalizedCoefficient,correctedAns,normalizationWork,Proofs.SafeModFrame.bodyWork,triangle,wordLimit] using done,by simpa [callerCells] using bound⟩\n'
            # Compare the actual selected source, including temporary cleanup.
            proof+=f'#guard (match runFuel 17 selectedSequence {start} with | .finished step => step.state.memory == callerCells ++ [⟨signed64,{n}⟩,⟨signed64,{m}⟩,⟨signed64,{na}⟩,⟨signed64,{nb}⟩,⟨unsigned64,{total}⟩] && step.state.bindings.length == 5 && step.state.work == {work} && step.state.baseMemory == 1 && step.state.peak ≤ 36 && step.returned == none && step.breaking == false | _ => false)\n'
            def cppint(x):return '(-9223372036854775807LL-1)' if x==-(1<<63) else f'({x}LL)'
            native+=f'{{auto result=normalize({n}LL,{m}LL,{cppint(a)},{cppint(b)},{ans}ULL);assert(result.ans=={total}ULL);assert(result.a=={na}LL);assert(result.b=={nb}LL);}}\n'
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='signed-normalization-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';lean.write_text(proof)
            lake,env=lean_environment()
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            changed_source=scratch/'changed.hpp'
            for changed in [original.replace('safe_mod(a, m)','safe_mod(m, a)'),original.replace('if (a < 0)','if (a <= 0)')]:
                changed_source.write_text(changed)
                mutated=emit_lean(lower_source(changed_source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
                lean.write_text(proof.replace(generated,mutated,1))
                rejected=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
            cpp=scratch/'native.cpp';binary=scratch/'native';cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(includes[0]),str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_original_body_slots_and_ans_updates(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        original=source.read_text();includes=[ROOT/'experiments/library/cpp']
        generated=emit_lean(lower_source(source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
        self.assertEqual(generated,(ROOT/'experiments/verification/number/floor_sum_signed_gcc_model.lean').read_text())
        expressions=re.findall(r'ans -= (.*);',original)
        self.assertEqual(len(expressions),2)
        proof='import Proofs.FloorSumSignedState\n'+generated+'''
open Proofs.CppScalar Proofs.CppState Proofs.FloorSumSignedCorrection Proofs.FloorSumArithmetic Proofs.FloorSumState
-- Only inspect this function's assignments; invoked bodies have their own slots.
def ansUpdates : Stmt → List Expr
  | .scope s => ansUpdates s
  | .sequence a b => ansUpdates a ++ ansUpdates b
  | .branch _ a b => ansUpdates a ++ ansUpdates b
  | .assign 4 e => [e]
  | _ => []
example : ansUpdates SignedTarget.floor_sum.body =
  [ansUpdateExpression aCorrectionExpression,ansUpdateExpression bCorrectionExpression] := rfl
open Proofs.FloorSumSignedState Proofs.CppLoop Proofs.SafeModProofs
-- Select the two consecutive writes in their original order.
def correctionTails : Stmt → List Stmt
  | .sequence (.assign 4 e) (.sequence (.assign slot value) .skip) =>
      [.sequence (.assign 4 e) (.sequence (.assign slot value) .skip)]
  | .scope s => correctionTails s
  | .sequence a b => correctionTails a ++ correctionTails b
  | .branch _ a b => correctionTails a ++ correctionTails b
  | _ => []
example : correctionTails SignedTarget.floor_sum.body =
  [correctionTail aCorrectionExpression 2,correctionTail bCorrectionExpression 3] := rfl
def callerCells : List Cell := [⟨signed64,-8⟩,⟨unsigned64,9223372036854775808⟩]
def stateExample : State := correctionState 0 1 (-1) (-1) 0 0 0 callerCells 17 1 10
example : (Stmt.assign 5 (.literal signed64 1)).run stateExample = none := by
  exact Proofs.CppAssignment.assign_readonly stateExample 5 (.literal signed64 1)
    ⟨callerCells.length+5,false⟩ rfl rfl
#guard runFuel 1 (.assign 5 (.literal signed64 1)) stateExample == .fault
#guard runFuel 2 (correctionTail aCorrectionExpression 2) stateExample == .exhausted
'''
        self.assertEqual(re.findall(r'\n\s*([ab]) = ([ab]2);',original),[('a','a2'),('b','b2')])
        native='#include <cassert>\nusing ll=long long;using ull=unsigned long long;\nstruct NativeResult{ull ans;ll a;ll b;};\n'
        for label,expr in zip(['a','b'],expressions):
            native+=f'NativeResult update_{label}(ll n,ll m,ll a,ll b,ull ans,ull a2,ull b2){{ans-={expr};{label}={label}2;return {{ans,a,b}};}}\n'
        native+='int main(){\n'
        for n in [0,1,4294967295]:
            for x in [-1,-9223372036854775808]:
                for m in [1,4294967295]:
                    for ans in [0,18446744073709551615]:
                        remainder=x%m;q=-(x//m)
                        for label,work in [('a',21),('b',12)]:
                            value=(ans-(n*(n-1)//2 if label=='a' else n)*q)%(1<<64)
                            env=f'[{n},{m},({x}),({x}),{ans},{remainder},{remainder},999]'
                            proof+=f'example : (ansUpdateExpression {label}CorrectionExpression).eval {env} = some ⟨{value},{work}⟩ := by\n'
                            proof+=f'  have result := {label}AnsUpdate_eval {n} {m} ({x}) ({x}) {ans} {remainder} [999] (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n'
                            proof+='  simpa [triangle,wordLimit] using result\n'
                            proof+=f'#guard (((ansUpdates SignedTarget.floor_sum.body)[{0 if label=="a" else 1}]?).bind (fun e => e.eval {env})) == some ⟨{value},{work}⟩\n'
                            start=f'(correctionState {n} {m} ({x}) ({x}) {ans} {remainder} {remainder} callerCells 17 1 10)'
                            finala=str(remainder) if label=='a' else f'({x})'
                            finalb=str(remainder) if label=='b' else f'({x})'
                            final=f'(correctionState {n} {m} {finala} {finalb} {value} {remainder} {remainder} callerCells {42 if label=="a" else 33} 1 {36 if label=="a" else 27})'
                            proof+=f'example : runFuel 3 (correctionTail {label}CorrectionExpression {2 if label=="a" else 3}) {start} = .finished ⟨{final},none,false⟩ := by\n'
                            proof+=f'  have result := {label}_correction_tail {n} {m} ({x}) ({x}) {ans} {remainder} callerCells 17 1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n'
                            proof+='  simpa [triangle,wordLimit,callerCells] using result\n'
                            proof+=f'#guard (((correctionTails SignedTarget.floor_sum.body)[{0 if label=="a" else 1}]?).map (fun stmt => runFuel 3 stmt {start})) == some (.finished ⟨{final},none,false⟩)\n'
                            cppx='(-9223372036854775807LL-1)' if x==-(1<<63) else f'({x}LL)'
                            native+=f'{{auto result=update_{label}({n}LL,{m}LL,{cppx},{cppx},{ans}ULL,{remainder}ULL,{remainder}ULL);assert(result.ans=={value}ULL);assert(result.a=={str(remainder)+"LL" if label=="a" else cppx});assert(result.b=={str(remainder)+"LL" if label=="b" else cppx});}}\n'
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='signed-body-corrections-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';lean.write_text(proof)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            # Mutate the original body, including its actual declaration layout.
            changed_source=scratch/'changed.hpp'
            for changed in [original.replace('(n - 1)','(n + 1)'),original.replace('(a2 - a) / m','(a2 - a) / n')]:
                changed_source.write_text(changed)
                mutated=emit_lean(lower_source(changed_source,None,includes,SIGNED_CONVERSIONS[1]),'SignedTarget')
                lean.write_text(proof.replace(generated,mutated,1))
                rejected=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
            cpp=scratch/'native.cpp';binary=scratch/'native';cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_signed_triangle_and_wrapped_product(self):
        original=(ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp').read_text()
        triangle=re.search(r'\(ull\)n \* \(n - 1\) / 2',original)
        self.assertIsNotNone(triangle)
        ns=[0,1,2,2147483648,4294967295]
        coefficients=[0,1,2,9223372036854775808,18446744073709551615]
        with tempfile.TemporaryDirectory(prefix='signed-triangle-') as directory:
            scratch=Path(directory);source=scratch/'triangle.cpp'
            source.write_text('using ll=long long;using ull=unsigned long long;\n'+
                f'unsigned long long triangle_value(ll n){{return {triangle.group()};}}\n'+
                f'ull triangle_product(ll n,ull coefficient){{return {triangle.group()}*coefficient;}}\n')
            generated=emit_lean(lower_source(source,'triangle_'),'TriangleSource')
            proof='import Proofs.FloorSumSignedCorrection\n'+generated+'''
open Proofs.CppScalar Proofs.CppState Proofs.FloorSumSignedCorrection Proofs.FloorSumArithmetic
def returnedExpr (s : Stmt) : Expr := match s with
  | .scope (.sequence (.ret e) .skip) => e
  | _ => .literal ⟨1,false,true⟩ 0
example : returnedExpr TriangleSource.triangle_value.body = signedTriangleExpression := rfl
example : returnedExpr TriangleSource.triangle_product.body = triangleProductExpression := rfl
'''
            native='#include <cassert>\n'+source.read_text()+'\nint main(){\n'
            for n in ns:
                tri=n*(n-1)//2
                proof+=f'example : signedTriangleExpression.eval [{n}] = some ⟨{tri},11⟩ := by\n'
                proof+=f'  have result := signedTriangle_eval {n} (by decide)\n  simpa [triangle] using result\n'
                proof+=f'#guard (TriangleSource.triangle_value.call [] [.value {n}]).map (·.value) == some {tri}\n'
                native+=f'assert(triangle_value({n}LL)=={tri}ULL);\n'
                for coefficient in coefficients:
                    product=tri*coefficient%(1<<64)
                    proof+=f'example : triangleProductExpression.eval [{n},{coefficient}] = some ⟨{product},13⟩ := by\n'
                    proof+=f'  have result := triangleProduct_eval {n} {coefficient} (by decide) (by decide)\n'
                    proof+='  simpa [triangle,wordLimit] using result\n'
                    proof+=f'#guard (TriangleSource.triangle_product.call [] [.value {n},.value {coefficient}]).map (·.value) == some {product}\n'
                    native+=f'assert(triangle_product({n}LL,{coefficient}ULL)=={product}ULL);\n'
            native+='}\n'
            lake,env=lean_environment();lean=scratch/'test.lean';lean.write_text(proof)
            result=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            fixture=source.read_text()
            for changed in [fixture.replace('n - 1','n + 1'),fixture.replace('/ 2','/ 3')]:
                source.write_text(changed)
                mutated=emit_lean(lower_source(source,'triangle_'),'TriangleSource')
                lean.write_text(proof.replace(generated,mutated,1))
                rejected=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
            source.write_text(native);binary=scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_source_quotients_match_model_and_mathematical_correction(self):
        original=(ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp').read_text()
        quotients=re.findall(r'\(\((\w+2) - (\w+)\) / m\)',original)
        self.assertEqual(quotients,[('a2','a'),('b2','b')])
        cases=[(x,m) for x in [-1,-7,-2147483648,-9223372036854775807,-9223372036854775808]
               for m in [1,2,3,2147483647,4294967295]]
        with tempfile.TemporaryDirectory(prefix='signed-correction-') as directory:
            scratch=Path(directory);source=scratch/'correction.cpp'
            source.write_text('using ll=long long;using ull=unsigned long long;\n'+
                ''.join(f'ull correction_{x}(ull {r},ll {x},ll m){{return ({r}-{x})/m;}}\n'
                        for r,x in quotients))
            generated=emit_lean(lower_source(source,'correction_'),'CorrectionSource')
            proof='import Proofs.FloorSumSignedCorrection\n'+generated+'''
open Proofs.CppScalar Proofs.CppState Proofs.FloorSumSignedCorrection Proofs.SafeModProofs
def returnedExpr (s : Stmt) : Expr := match s with
  | .scope (.sequence (.ret e) .skip) => e
  | _ => .literal ⟨1,false,true⟩ 0
example : returnedExpr CorrectionSource.correction_a.body = quotientExpression := rfl
example : returnedExpr CorrectionSource.correction_b.body = quotientExpression := rfl
'''
            native='#include <cassert>\n'+source.read_text()+'\nint main(){\n'
            for x,m in cases:
                remainder=x%m;expected=-(x//m)
                proof+=f'example : quotientExpression.eval [{remainder},({x}),{m}] = some ⟨{expected},7⟩ := by\n'
                proof+=f'  have result := quotient_eval ({x}) {m} (by decide) (by decide) (by decide) (by decide)\n'
                proof+='  simpa using result\n'
                proof+=f'#guard (CorrectionSource.correction_a.call [] [.value {remainder},.value ({x}),.value {m}]).map (·.value) == some {expected}\n'
                cppx='(-9223372036854775807LL-1)' if x==-(1<<63) else f'({x}LL)'
                for name in ['a','b']:
                    native+=f'assert(correction_{name}({remainder}ULL,{cppx},{m}LL)=={expected}ULL);\n'
            native+='}\n'
            lake,env=lean_environment();lean=scratch/'test.lean';lean.write_text(proof)
            result=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            original_fixture=source.read_text()
            for changed in [original_fixture.replace('a2-a','a2+a'),original_fixture.replace('/m','%m')]:
                source.write_text(changed)
                mutated=emit_lean(lower_source(source,'correction_'),'CorrectionSource')
                lean.write_text(proof.replace(generated,mutated,1))
                rejected=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
            source.write_text(native);binary=scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

if __name__=='__main__':
    disable_network()
    lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.FloorSumSignedPrefix'],cwd=ROOT,env=env,check=True)
    unittest.main()
