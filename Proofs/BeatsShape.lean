import Proofs.BeatsUpd
namespace Proofs.BeatsModel

inductive Sk where
  | leaf
  | node (l r : Sk)

def BT.skel : BT → Sk
  | .leaf _ => .leaf
  | .node _ _ l r => .node l.skel r.skel

/-- The skeleton of a tree over the positions `[lo, hi)`: split at `(lo + hi) / 2`. -/
def Shape : Nat → Nat → Sk → Prop
  | lo, hi, .leaf => hi = lo + 1
  | lo, hi, .node l r => lo + 1 < hi ∧ Shape lo ((lo + hi) / 2) l ∧ Shape ((lo + hi) / 2) hi r

theorem skel_setBT (v : Int) (t : BT) : (setBT v t).skel = t.skel := by cases t <;> rfl
theorem skel_addBT (x : Int) (t : BT) : (addBT x t).skel = t.skel := by cases t <;> rfl
theorem skel_capMaxBT (x : Int) (t : BT) : (capMaxBT x t).skel = t.skel := by
  unfold capMaxBT; split <;> (try rfl); cases t <;> rfl
theorem skel_capMinBT (x : Int) (t : BT) : (capMinBT x t).skel = t.skel := by
  unfold capMinBT; split <;> (try rfl); cases t <;> rfl
theorem skel_applyTag (tg : Tag) (nd : Nd) (t : BT) : (applyTag tg nd t).skel = t.skel := by
  unfold applyTag
  cases tg.lval with
  | some v => exact skel_setBT v t
  | none => rw [skel_capMinBT, skel_capMaxBT, skel_addBT]

def BT.height : BT → Nat
  | .leaf _ => 0
  | .node _ _ l r => max l.height r.height + 1

theorem height_setBT (v : Int) (t : BT) : (setBT v t).height = t.height := by cases t <;> rfl
theorem height_addBT (x : Int) (t : BT) : (addBT x t).height = t.height := by cases t <;> rfl
theorem height_capMaxBT (x : Int) (t : BT) : (capMaxBT x t).height = t.height := by
  unfold capMaxBT; split <;> (try rfl); cases t <;> rfl
theorem height_capMinBT (x : Int) (t : BT) : (capMinBT x t).height = t.height := by
  unfold capMinBT; split <;> (try rfl); cases t <;> rfl
theorem height_applyTag (tg : Tag) (nd : Nd) (t : BT) : (applyTag tg nd t).height = t.height := by
  unfold applyTag
  cases tg.lval with
  | some v => exact height_setBT v t
  | none => rw [height_capMinBT, height_capMaxBT, height_addBT]

end Proofs.BeatsModel
