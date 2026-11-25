import Proofs.Cpp.SortUtil

namespace Proofs.Cpp.LowlinkResults

def EndpointOrder (a b : Int × Int) : Prop := a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2

theorem endpoint_order_iff (a b : Int × Int) :
    EndpointOrder a b ↔ ¬ Prod.lexLt b a := by
  simp only [EndpointOrder, Prod.lexLt]
  omega

/-- The two sorts at the end of ListGraph::lowlink preserve both result lists.
The bridge list uses the C++ lexicographic comparison on endpoint pairs. -/
theorem sorted_results (points : Array Int) (bridges : Array (Int × Int)) :
    (Cpp.sort points).toList.Pairwise (· ≤ ·) ∧ (Cpp.sort points).toList.Perm points.toList ∧
      (Cpp.sortLex bridges).toList.Pairwise EndpointOrder ∧
      (Cpp.sortLex bridges).toList.Perm bridges.toList := by
  refine ⟨SortUtil.sort_sorted points, SortUtil.sort_perm points, ?_, ?_⟩
  · unfold Cpp.sortLex
    have isLe (a b : Int × Int) : (!decide (Prod.lexLt b a)) = true ↔ EndpointOrder a b := by
      simp [endpoint_order_iff]
    have h := List.pairwise_mergeSort (le := fun a b => !decide (Prod.lexLt b a))
      (fun a b c hab hbc => (isLe a c).mpr (by
        have h₁ := (isLe a b).mp hab
        have h₂ := (isLe b c).mp hbc
        unfold EndpointOrder at *
        omega))
      (fun a b => Bool.or_eq_true_iff.mpr (by
        rw [isLe, isLe]
        unfold EndpointOrder
        omega)) bridges.toList
    exact h.imp (fun h => (isLe _ _).mp h)
  · simpa only [Cpp.sortLex, List.toList_toArray] using
      (List.mergeSort_perm bridges.toList (fun a b => !decide (Prod.lexLt b a)))

end Proofs.Cpp.LowlinkResults
