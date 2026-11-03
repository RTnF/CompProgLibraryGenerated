"""Source-derived size call and unary expressions over flat-vector reads."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_fields_call import FIXTURE
from test_union_find_original_api import HEADER, SOURCE
from nested_ir import lower_source, emit_lean
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent

PROOF = '''
open Proofs.UfFieldsSize Proofs.UfInlineRoot
 theorem parentWeights : Weights parents := by
   intro i w found negative
   have inside : i<4 := (List.getElem?_eq_some_iff.mp found).1
   have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
   rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst w <;> simp [parents] at *
 def ne : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def ae : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 example := size_call (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest parentWeights (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   ne ae 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example := Proofs.UfFieldsSize.body_correct [] (⟨0,true⟩ : Proofs.CppState.Binding) parents ranks
   parentForest (by decide +kernel) parentWeights 3 (by decide +kernel) 4 (by decide +kernel)
 def sizeCall := Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel 128 rootCaller
   [.vectorReference 0,.scalarReference 1,.value ne,.value ae]
 #guard observe sizeCall == some (4,1,[-4,0,0,0])
 -- Forest permits INT_MIN. Its invalid negation must be rejected, not treated as a size.
 example : ¬ Weights [-2147483648] := by
   intro weights
   have invalid := weights 0 (-2147483648) rfl (by decide)
   norm_num at invalid
 def invalidSize := Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel 128 (caller [-2147483648] 1)
   [.vectorReference 0,.scalarReference 1,.value (.literal intTy 1),.value (.literal intTy 0)]
 #guard invalidSize == .fault
 def unaryRead (op : Unary) : NExpr := .unary intTy op (.read intTy (.local 0) (.literal ⟨64,false,false⟩ 0))
 #guard vwp (unaryRead .neg) == (5,5)
 def unsignedNeg : NExpr := .unary ⟨64,false,false⟩ .neg (.read intTy (.local 0) (.literal ⟨64,false,false⟩ 0))
 #guard vdenL intTy [1] (fun _ _ => none) unsignedNeg == some 18446744073709551615
 def nestedRead : NExpr := .unary intTy .neg (.binary intTy .add (unaryRead .neg) (.literal intTy 2))
 #guard vdenL intTy [-4] (fun _ _ => none) nestedRead == some (-6)
 #guard vdenL intTy [-2147483648] (fun _ _ => none) (unaryRead .neg) == none
 #guard vdenL intTy [] (fun _ _ => none) (unaryRead .plus) == none
 #guard vdenL intTy [2147483648] (fun _ _ => none) (unaryRead .plus) == none
 #guard vdenL intTy [1] (fun _ _ => none) (.unary intTy .neg (.read intTy (.local 1) (.literal intTy 0))) == none
 -- Existing scalar-only unary costs are unchanged.
 #guard vwp (.unary intTy .neg (.literal intTy 1)) == (2,2)
'''

class UnionFindSizeCallTests(unittest.TestCase):
    def test_size_source_call_and_unary_semantics(self):
        self.assertEqual((ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text(),
            emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'))
        checks=[]
        for x in [-2147483648,-2147483647,-4,-1,0,1,2147483647]:
            for op in ['plus','neg','not']:
                checks.append(f'''#guard ((unaryRead .{op}).eval (caller [({x})] 1)).map (fun (s,v) => (v,s.scalars.work)) ==
                  (vdenL intTy [({x})] (fun _ _ => none) (unaryRead .{op})).map (fun v => (v,4))''')
        with tempfile.TemporaryDirectory(prefix='union-find-size-call-') as directory:
            proof=Path(directory)/'checks.lean'
            header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
            proof.write_text('import Proofs.UfFieldsSize\n'+header+FIXTURE+PROOF+'\n'+'\n'.join(checks))
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        print('size full source call and compression; unary plus/neg/not values, work, overflow, unsigned wrap and invalid reads')

if __name__=='__main__':disable_network();unittest.main()
