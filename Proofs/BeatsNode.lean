import Proofs.BeatsTag
namespace Proofs.BeatsModel

theorem pend_length (tg : Tag) (nd : Nd) (zs : List Int) : (pend tg nd zs).length = zs.length := by
  unfold pend
  cases tg.lval <;> simp

def noTag : Tag := ⟨none, 0⟩

/-- With no pending operation, the caps by the node's own summary change nothing. -/
theorem pend_noTag (nd : Nd) (ys : List Int) (hd : Desc nd ys) : pend noTag nd ys = ys := by
  unfold pend noTag
  simp only []
  have h1 : ys.map (fun w => w + 0) = ys := by simp
  rw [h1, map_min_id, map_max_id]
  · intro v hv; have := mnL_le ys v hv; have h4 := hd.2.2.2.1; omega
  · intro v hv; have := mxL_ge ys v hv; have h1 := hd.1; omega

/-- The state of an internal node and its two children, with the arrays they describe. `xl`, `xr` are what the children's
summaries describe (before the node's pending operation); `ys` is the node's own (true) array. -/
structure NodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) : Prop where
  desc : Desc nd ys
  eq : ys = pend tg nd (xl ++ xr)
  dl : Desc cl xl
  dr : Desc cr xr
  nel : xl ≠ []
  ner : xr ≠ []
  rl : InRange xl
  rr : InRange xr
  okl : PushOk tg nd cl xl
  okr : PushOk tg nd cr xr

/-- After `push`: the pending operation is cleared, the children describe their true arrays, the node is unchanged. -/
theorem push_nodeInv (nd : Nd) (tg : Tag) (cl cr : Nd) (xl xr ys : List Int) (h : NodeInv nd tg cl cr xl xr ys)
    (okl' : PushOk noTag nd (pushChild tg nd cl xl.length) (pend tg nd xl))
    (okr' : PushOk noTag nd (pushChild tg nd cr xr.length) (pend tg nd xr))
    (rl' : InRange (pend tg nd xl)) (rr' : InRange (pend tg nd xr)) :
    NodeInv nd noTag (pushChild tg nd cl xl.length) (pushChild tg nd cr xr.length) (pend tg nd xl) (pend tg nd xr) ys := by
  obtain ⟨vl, hvl⟩ := List.exists_mem_of_ne_nil _ h.nel
  obtain ⟨vr, hvr⟩ := List.exists_mem_of_ne_nil _ h.ner
  have hys : ys = pend tg nd xl ++ pend tg nd xr := by rw [h.eq, pend_append]
  refine ⟨h.desc, ?_, pushChild_desc tg nd cl xl vl hvl h.rl h.dl h.okl, pushChild_desc tg nd cr xr vr hvr h.rr h.dr h.okr,
    ?_, ?_, rl', rr', okl', okr'⟩
  · rw [← hys]; exact (pend_noTag nd ys h.desc).symm
  · intro hne
    apply h.nel
    have := pend_length tg nd xl
    rw [hne] at this
    exact List.length_eq_zero_iff.mp this.symm
  · intro hne
    apply h.ner
    have := pend_length tg nd xr
    rw [hne] at this
    exact List.length_eq_zero_iff.mp this.symm

end Proofs.BeatsModel
