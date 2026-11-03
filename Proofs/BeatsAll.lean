import Proofs.BeatsAdd
namespace Proofs.BeatsModel

/-- `update_all`: every element becomes `x`; `len` is the number of elements. -/
def setNd (len x : Int) : Nd := { mx := x, smx := -INF, mc := len, mn := x, smn := INF, mnc := len }

theorem setNd_desc (n : Nat) (x : Int) (hx : -INF < x) (hx2 : x < INF) (hn : 0 < n) :
    Desc (setNd n x) (List.replicate n x) := by
  have hmem : x ∈ List.replicate n x := List.mem_replicate.mpr ⟨by omega, rfl⟩
  have hall : ∀ w ∈ List.replicate n x, w = x := fun w hw => (List.mem_replicate.mp hw).2
  have hM : mxL (List.replicate n x) = x := by
    apply Int.le_antisymm
    · exact mxL_le _ _ (by omega) (fun w hw => Int.le_of_eq (hall w hw))
    · exact mxL_ge _ _ hmem
  have hm : mnL (List.replicate n x) = x := by
    apply Int.le_antisymm
    · exact mnL_le _ _ hmem
    · exact mnL_ge _ _ (by omega) (fun w hw => Int.le_of_eq (hall w hw).symm)
  refine ⟨hM.symm, ?_, ?_, hm.symm, ?_, ?_⟩
  · unfold smxL
    rw [hM, filter_none _ _ (fun w hw => by simp [hall w hw])]; rfl
  · unfold cmxL
    rw [hM, List.countP_eq_length.mpr (fun w hw => by simp [hall w hw])]; simp [setNd]
  · unfold smnL
    rw [hm, filter_none _ _ (fun w hw => by simp [hall w hw])]; rfl
  · unfold cmnL
    rw [hm, List.countP_eq_length.mpr (fun w hw => by simp [hall w hw])]; simp [setNd]

end Proofs.BeatsModel
