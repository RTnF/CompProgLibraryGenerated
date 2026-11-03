import Proofs.BeatsCalcMin
namespace Proofs.BeatsModel

def leafNd (v : Int) : Nd := { mx := v, smx := -INF, mc := 1, mn := v, smn := INF, mnc := 1 }

theorem leafNd_desc (v : Int) (hv : -INF < v ∧ v < INF) : Desc (leafNd v) [v] := by
  have e : mnL [v] = mxL [v] := by rw [mnL_single v hv.2, mxL_single v hv.1]
  refine ⟨(mxL_single v hv.1).symm, (allEq_smx [v] e).symm, ?_, (mnL_single v hv.2).symm, (allEq_smn [v] e).symm, ?_⟩
  · show (1 : Int) = _
    unfold cmxL; rw [mxL_single v hv.1]; simp
  · show (1 : Int) = _
    unfold cmnL; rw [mnL_single v hv.2]; simp

def buildBT (a : List Int) (lo hi : Nat) : BT :=
  if lo + 1 < hi then
    .node (mergeNd (buildBT a lo ((lo + hi) / 2)).nd (buildBT a ((lo + hi) / 2) hi).nd) noTag
      (buildBT a lo ((lo + hi) / 2)) (buildBT a ((lo + hi) / 2) hi)
  else .leaf (leafNd (a.getD lo 0))
termination_by hi - lo
decreasing_by all_goals omega

theorem buildBT_spec (a : List Int) (ha : InRange a) :
    ∀ (n lo hi : Nat), hi - lo = n → lo < hi → hi ≤ a.length →
      Inv (buildBT a lo hi) ((a.drop lo).take (hi - lo)) ∧ Shape lo hi (buildBT a lo hi).skel := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn hlo hhi
    unfold buildBT
    by_cases hc : lo + 1 < hi
    · rw [if_pos hc]
      have h1 := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) (by omega)
      have h2 := ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl (by omega) hhi
      have := Inv.update h1.1 h2.1 (mergeNd (buildBT a lo ((lo + hi) / 2)).nd (buildBT a ((lo + hi) / 2) hi).nd) noTag
      have e : (a.drop lo).take (hi - lo) = (a.drop lo).take ((lo + hi) / 2 - lo) ++ (a.drop ((lo + hi) / 2)).take (hi - (lo + hi) / 2) := by
        have : hi - lo = ((lo + hi) / 2 - lo) + (hi - (lo + hi) / 2) := by omega
        rw [this, List.take_add, List.drop_drop]
        congr 3
        omega
      refine ⟨?_, ?_⟩
      · rw [e]; exact this
      · exact ⟨hc, h1.2, h2.2⟩
    · rw [if_neg hc]
      have hhi' : hi = lo + 1 := by omega
      have hlen : lo < a.length := by omega
      have hmem : a.getD lo 0 ∈ a := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]; exact List.getElem_mem _
      have e : (a.drop lo).take (hi - lo) = [a.getD lo 0] := by
        rw [hhi', Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
        rfl
      have hr := ha _ hmem
      refine ⟨?_, ?_⟩
      · rw [e]; exact Inv.leaf _ _ (leafNd_desc _ hr) (fun w hw => by rw [List.mem_singleton.mp hw]; exact hr)
      · exact hhi'

end Proofs.BeatsModel
