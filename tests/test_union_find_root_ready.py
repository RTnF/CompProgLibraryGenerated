"""Root restores method preconditions; the next call consumes its compressed state."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER
from test_union_find_fields_call import FIXTURE
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.UfRootReady
 def nExpr : NExpr := .binary intTy .add (.literal intTy 2) (.literal intTy 2)
 def aExpr : NExpr := .binary intTy .add (.literal intTy 1) (.literal intTy 2)
 def bExpr : NExpr := .literal intTy 1
 example := root_call_ready (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   nExpr aExpr 3 rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example := two_roots (cslot := 1) rootCaller ownerOK ⟨0,true⟩ 1 (by decide +kernel) rfl
   parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
   nExpr aExpr bExpr 3 1 rfl rfl rfl rfl rfl rfl
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 def first := Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 rootCaller
   [.vectorReference 0,.scalarReference 1,.value nExpr,.value aExpr]
 #guard observe first == some (0,1,[-4,0,0,0])
 def middle : NState := match first with | .finished (s,_) => s | _ => rootCaller
 def second := Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel 64 middle
   [.vectorReference 0,.scalarReference 1,.value nExpr,.value bExpr]
 #guard observe second == some (0,1,[-4,0,0,0])
 #guard (match second with
   | .finished (s,_) => s.scalars.bindings == rootCaller.scalars.bindings &&
       s.scalarCell 2 intTy == some (⟨0,false⟩,⟨intTy,1⟩) &&
       s.scalarCell 3 intTy == some (⟨1,true⟩,⟨intTy,9876⟩) &&
       (s.frame.state.storage.lookup 0).map (·.limit) == some (Proofs.CppVectorBindings.sizeLimit intTy) &&
       (s.frame.state.storage.lookup 0).map (·.capacity) == some 5 &&
       (s.frame.state.storage.lookup 0).map (·.epoch) == some 0
   | _ => false)
 example (c : NState) (vslot vb V vsc cslot : Nat) (buf : Proofs.CppVector.Buffer Value)
   (ok : VOKWF c vslot vb V vsc buf) (cb : Proofs.CppState.Binding) (count : Int)
   (cell : c.scalarCell cslot intTy = some (cb,⟨intTy,count⟩)) (writable : cb.writable = true)
   (ps : List Int) (rank : Nat → Nat) (forest : Proofs.UfRootCall.Forest ps rank)
   (items : buf.items = ps.map Value.integer) (small : ps.length < 2147483648)
   (valid : buf.Valid (accepts (.integer intTy))) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit intTy)
   (owner : buf.owner = V) (en ea eb : NExpr) (a b : Nat)
   (ns : en.scalarOnly = true) (as_ : ea.scalarOnly = true) (bs_ : eb.scalarOnly = true)
   (nt : en.resultType = intTy) (at_ : ea.resultType = intTy) (bt_ : eb.resultType = intTy)
   (nv : en.denote (Proofs.CppNestedEval.envOf c) = some (ps.length : Int))
   (av : ea.denote (Proofs.CppNestedEval.envOf c) = some (a : Int))
   (bv : eb.denote (Proofs.CppNestedEval.envOf c) = some (b : Int))
   (ha : a < ps.length) (hb : b < ps.length) :=
   two_roots c ok cb count cell writable ps rank forest items small valid limit owner
     en ea eb a b ns as_ bs_ nt at_ bt_ nv av bv ha hb
'''
class UnionFindRootReadyTests(unittest.TestCase):
    def test_general_repeated_root_and_alias_metadata(self):
        header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
        with tempfile.TemporaryDirectory(prefix='uf-root-ready-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfRootReady\n'+header+FIXTURE+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
