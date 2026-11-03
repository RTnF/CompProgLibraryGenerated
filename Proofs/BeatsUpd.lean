import Proofs.BeatsPushT
namespace Proofs.BeatsModel

/-- `update(k)`: recompute a node's summary from its children (the node has no pending tag). -/
def updateBT : BT → BT
  | .leaf nd => .leaf nd
  | .node _ _ l r => .node (mergeNd l.nd r.nd) noTag l r

theorem Inv.update {l r : BT} {xl xr : List Int} (hl : Inv l xl) (hr : Inv r xr) (nd : Nd) (tg : Tag) :
    Inv (updateBT (.node nd tg l r)) (xl ++ xr) := by
  obtain ⟨vl, hvl⟩ := List.exists_mem_of_ne_nil _ hl.ne
  obtain ⟨vr, hvr⟩ := List.exists_mem_of_ne_nil _ hr.ne
  have hd : Desc (mergeNd l.nd r.nd) (xl ++ xr) := mergeNd_desc _ _ _ _ hl.desc hr.desc
  have hrg : InRange (xl ++ xr) := fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact hl.range w h
    · exact hr.range w h
  have hsubL : ∀ w ∈ xl, w ∈ xl ++ xr := fun w hw => List.mem_append.mpr (Or.inl hw)
  have hsubR : ∀ w ∈ xr, w ∈ xl ++ xr := fun w hw => List.mem_append.mpr (Or.inr hw)
  simp only [updateBT]
  refine Inv.node _ noTag l r xl xr _ ?_ hl hr
  refine ⟨hd, (pend_noTag _ _ hd).symm, hl.desc, hr.desc, hl.ne, hr.ne, hl.range, hr.range, hrg, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp [noTag] at hv
  · intro _ w hw; simpa [noTag] using hrg w hw
  · intro _
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · exfalso
      have h1 : l.nd.mx = mxL xl := hl.desc.1
      have h2 : mxL xl ≤ mxL (xl ++ xr) := mxL_mono _ _ hsubL
      have h3 : (mergeNd l.nd r.nd).mx = mxL (xl ++ xr) := hd.1
      simp only [noTag] at hp
      omega
    · exfalso
      have h1 : l.nd.mn = mnL xl := hl.desc.2.2.2.1
      have h2 : mnL (xl ++ xr) ≤ mnL xl := by
        rcases mnL_cases xl with h | h
        · rw [h]; exact mnL_le_INF _
        · exact mnL_le _ _ (hsubL _ h)
      have h3 : (mergeNd l.nd r.nd).mn = mnL (xl ++ xr) := hd.2.2.2.1
      simp only [noTag] at hp
      omega
  · intro _
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · exfalso
      have h1 : r.nd.mx = mxL xr := hr.desc.1
      have h2 : mxL xr ≤ mxL (xl ++ xr) := mxL_mono _ _ hsubR
      have h3 : (mergeNd l.nd r.nd).mx = mxL (xl ++ xr) := hd.1
      simp only [noTag] at hp
      omega
    · exfalso
      have h1 : r.nd.mn = mnL xr := hr.desc.2.2.2.1
      have h2 : mnL (xl ++ xr) ≤ mnL xr := by
        rcases mnL_cases xr with h | h
        · rw [h]; exact mnL_le_INF _
        · exact mnL_le _ _ (hsubR _ h)
      have h3 : (mergeNd l.nd r.nd).mn = mnL (xl ++ xr) := hd.2.2.2.1
      simp only [noTag] at hp
      omega

end Proofs.BeatsModel
