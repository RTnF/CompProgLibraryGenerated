import Proofs.BeatsLoop1
namespace Proofs.BeatsModel

theorem agree_root (H : Heap) (t : BT) (k : Nat) (h : Agree H t k) : (H k).1 = t.nd := by
  cases t with
  | leaf nd => exact (agree_leaf H nd k).mp h
  | node nd tg l r =>
    rw [agree_node] at h
    show (H k).1 = nd
    rw [h.1]

theorem agree_updateBT (H : Heap) (nd : Nd) (l r : BT) (k : Nat) (h : Agree H (.node nd noTag l r) k) :
    Agree (updateH H k) (updateBT (.node nd noTag l r)) k := by
  rw [agree_node] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [updateBT]
  rw [agree_node]
  have r1 := agree_root H l _ h2
  have r2 := agree_root H r _ h3
  refine ⟨?_, ?_, ?_⟩
  · unfold updateH
    rw [Heap.set_eq, r1, r2, h1]
  · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
  · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)

/-- What the traversal does at a node, decided from the node's summary and its range. -/
inductive Cls
  | stop | whole | down

/-- The generic traversal (all of `chmin`, `chmax`, `add_val`, `update_val`): skip, act on the whole node, or push and recurse. -/
def travBT (cls : Nd → Nat → Nat → Cls) (actBT : BT → BT) : BT → Nat → Nat → BT
  | .leaf nd, lo, hi => match cls nd lo hi with
    | Cls.stop => .leaf nd
    | _ => actBT (.leaf nd)
  | .node nd tg l r, lo, hi => match cls nd lo hi with
    | Cls.stop => .node nd tg l r
    | Cls.whole => actBT (.node nd tg l r)
    | Cls.down => updateBT (.node nd noTag (travBT cls actBT (applyTag tg nd l) lo ((lo + hi) / 2))
        (travBT cls actBT (applyTag tg nd r) ((lo + hi) / 2) hi))
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
