import Proofs.TreeOrderMath

namespace Proofs.TreeOrderMath
open Proofs.TreeDpSpec Proofs.TreeDpMath

-- TO permits extra arcs; DP additionally needs the parent/child classification
-- and the arc from each non-root vertex back to its parent.
theorem TO.toTS (H : TO head target parent n root) (ord : List Nat)
    (cls : ∀ v, v < n → ∀ p ∈ arcs head v,
      (tgt target p ≠ root ∧ parent.getD (tgt target p) 0 = (v : Int)) ∨
        (v ≠ root ∧ tgt target p = par parent v))
    (back : ∀ v, v < n → v ≠ root → par parent v ∈ nbs head target v)
    (length : ord.length = n) (nd : ord.Nodup) (upper : ∀ x ∈ ord, x < n)
    (first : ord.getD 0 0 = root)
    (before : ∀ j, 1 ≤ j → j < n → ∃ j', j' < j ∧ ord.getD j' 0 = par parent (ord.getD j 0)) :
    TS head target parent ord n root := by
  have covered : ∀ x, x < n → x ∈ ord := by
    intro x hx
    by_cases missing : x ∈ ord
    · exact missing
    have larger : (x::ord).Nodup := List.nodup_cons.mpr ⟨missing,nd⟩
    have bound := len_le_n (x::ord) larger (by
      intro y member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      · exact upper y member)
    simp only [List.length_cons,length] at bound
    omega
  refine ⟨H.rootlt,length,nd,upper,covered,H.rootpar,?_,H.tgtlt,cls,H.nodup,back,H.chArc⟩
  intro w hw nonroot
  have inside : ord.idxOf w < ord.length := List.idxOf_lt_length_of_mem (covered w hw)
  have value : ord.getD (pos ord w) 0 = w := by
    simp [pos,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,List.getElem_idxOf]
  have positive : 1 ≤ pos ord w := by
    by_cases zero : 1 ≤ pos ord w
    · exact zero
    have equal : pos ord w = 0 := by omega
    rw [equal] at value
    exact False.elim (nonroot (value.symm.trans first))
  obtain ⟨j,earlier,found⟩ := before (pos ord w) positive (by simpa [pos,length] using inside)
  rw [value] at found
  have index : pos ord (par parent w) = j := by
    have ji : j < ord.length := by simp only [pos] at earlier; omega
    change ord.idxOf (par parent w) = j
    rw [←found]
    have get : ord.getD j 0 = ord[j]'ji := by simp [List.getD_eq_getElem?_getD,ji]
    rw [get]
    exact List.Nodup.idxOf_getElem nd j ji
  have bounds := H.parv w hw
  refine ⟨bounds.1,?_,?_⟩
  · unfold par
    omega
  · rw [index]
    exact earlier

end Proofs.TreeOrderMath
