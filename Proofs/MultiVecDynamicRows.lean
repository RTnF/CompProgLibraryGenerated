import Proofs.MultiVecN
import Proofs.CppRowsFrame

namespace Proofs.MultiVecDynamicRows
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.CppRowsFrame Proofs.MultiVecN

-- A legacy function frame supplies the initial dynamic view. Subsequent row
-- operations use FWR, whose resource and row-count indices may change.
def legacyResources (mv : MV) (wk : Nat) (fr : Frame) : Resources :=
  ⟨mv.L0,mv.T0+wk,fr.state.storage.peak,mv.N,fr.state.storage.baseSpace⟩

theorem dynamic_rows (mv : MV) (vv : Nat → List Int) (bb : Nat → Buffer Value)
    (wk : Nat) (fr : Frame) (fw : FWM mv vv bb wk fr) (k : Nat)
    (hk : k < mv.nv) (nested : mv.flat k = false) :
    FWR fr k (mv.R k) (mv.ty k) (mv.vsc k)
      (rowIds (mv.R k) (mv.wrows k)) 0
      ((List.range (mv.wrows k)).map fun i => vv (rowKey k i))
      (mv.wN k) (mv.flag k) (legacyResources mv wk fr) := by
  obtain ⟨_,_,g,flag,contents⟩ := fw.nested k hk nested
  refine ⟨⟨CppRowsGraph.of_legacy fr.state (mv.R k) (mv.ty k) (mv.wrows k) (mv.vsc k) g,?_,?_⟩,
    ?_,fw.lengths,flag,mv.permN k,⟨fw.live,fw.work,rfl,fw.count,rfl⟩⟩
  · simp [rowIds]
  · intro j owner lookup
    have inside : j < mv.wrows k := by
      have bound := (List.getElem?_eq_some_iff.mp lookup).1
      simpa [rowIds] using bound
    have equal : owner = mv.R k+1+j := by
      rw [CppNestedRows.rowIds_get _ _ _ inside] at lookup
      exact (Option.some.inj lookup).symm
    subst owner
    obtain ⟨b,hb,hi⟩ := contents j inside
    refine ⟨b,hb,?_⟩
    simpa [List.getElem?_map,List.getElem?_range,inside] using hi
  · simp [fw.bindings,List.getElem?_map,List.getElem?_range,hk,bindOf,nested]

end Proofs.MultiVecDynamicRows
