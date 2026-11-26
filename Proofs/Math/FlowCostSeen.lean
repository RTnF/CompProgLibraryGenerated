import Proofs.Math.FlowCostParents

namespace Proofs.FlowResidual

variable {Arc Vertex : Type} [DecidableEq Vertex]

def overwrite {α : Type} (old : Vertex → α) (v : Vertex) (x : α) : Vertex → α :=
  fun u => if u = v then x else old u

/-- Reachability is independent of the numeric value saved in the distance array. -/
structure ParentState (n : Network Arc Vertex) (cap : Capacity Arc) (source : Vertex)
    (seen : Vertex → Bool) (label : Vertex → Int) (pred : Vertex → Option Arc)
    (last : Vertex → Nat) (now : Nat) : Prop where
  source_seen : seen source = true
  noParent : ∀ v, seen v = true → pred v = none → v = source ∧ label v = 0
  hasParent : ∀ v a, pred v = some a → n.head a = v ∧ 0 < cap a ∧ seen v = true ∧ seen (n.tail a) = true ∧
    label (n.tail a) + n.cost a ≤ label v ∧ (last v ≤ last (n.tail a) → label (n.tail a) + n.cost a < label v)
  clock : ∀ v, last v < now

theorem parent_state_initial (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex) (initial : Int) :
    ParentState n cap s (overwrite (fun _ => false) s true) (overwrite (fun _ => initial) s 0)
      (fun _ => none) (fun _ => 0) 1 := by
  refine ⟨by simp [overwrite], ?_, ?_, fun _ => Nat.zero_lt_succ 0⟩
  · intro v hv _
    have : v = s := by simpa [overwrite] using hv
    simp [overwrite, this]
  · intro v a h
    cases h

theorem parent_state_relax (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex)
    (seen : Vertex → Bool) (label : Vertex → Int) (pred : Vertex → Option Arc) (last : Vertex → Nat) (now : Nat)
    (old : ParentState n cap s seen label pred last now) (a : Arc)
    (hpos : 0 < cap a) (reached : seen (n.tail a) = true)
    (better : seen (n.head a) = true → label (n.tail a) + n.cost a < label (n.head a)) :
    let v := n.head a
    let next := label (n.tail a) + n.cost a
    ParentState n cap s (overwrite seen v true) (overwrite label v next) (overwrite pred v (some a))
      (overwrite last v now) (now + 1) := by
  dsimp only
  constructor
  · simp [overwrite, old.source_seen]
  · intro v hv hp
    by_cases h : v = n.head a
    · simp [overwrite, h] at hp
    · simpa only [overwrite, h, ite_false] using old.noParent v
        (by simpa [overwrite, h] using hv) (by simpa [overwrite, h] using hp)
  · intro v b hb
    by_cases h : v = n.head a
    · subst v
      have eq : a = b := by simpa [overwrite] using hb
      subst b
      refine ⟨rfl, hpos, by simp [overwrite], by simp [overwrite, reached], ?_, ?_⟩
      · by_cases hu : n.tail a = n.head a
        · have strict := better (hu ▸ reached)
          simp only [overwrite, hu, ite_true] at strict ⊢
          omega
        · simp [overwrite, hu]
      · intro htime
        by_cases hu : n.tail a = n.head a
        · have strict := better (hu ▸ reached)
          simp only [overwrite, hu, ite_true] at strict ⊢
          omega
        · simp only [overwrite, hu, ite_false, ite_true] at htime
          have := old.clock (n.tail a)
          omega
    · have hb' : pred v = some b := by simpa [overwrite, h] using hb
      obtain ⟨head, hbp, seenV, seenTail, hle, hlt⟩ := old.hasParent v b hb'
      refine ⟨head, hbp, by simp [overwrite, h, seenV], by simp [overwrite, seenTail], ?_, ?_⟩
      · by_cases hu : n.tail b = n.head a
        · have strict := better (hu ▸ seenTail)
          simp only [overwrite, hu, h, ite_true, ite_false] at hle ⊢
          omega
        · simpa [overwrite, h, hu] using hle
      · intro htime
        by_cases hu : n.tail b = n.head a
        · have strict := better (hu ▸ seenTail)
          simp only [overwrite, hu, h, ite_true, ite_false] at hle ⊢
          omega
        · simp only [overwrite, hu, h, ite_false] at htime ⊢
          exact hlt htime
  · intro v
    unfold overwrite
    split
    · omega
    · have := old.clock v
      omega

omit [DecidableEq Vertex] in
theorem parent_state_complete (n : Network Arc Vertex) (cap : Capacity Arc) (s : Vertex)
    (seen : Vertex → Bool) (label : Vertex → Int) (pred : Vertex → Option Arc) (last : Vertex → Nat) (now : Nat)
    (old : ParentState n cap s seen label pred last now) (root : label s = 0)
    (closed : ∀ a, 0 < cap a → seen (n.tail a) = true →
      seen (n.head a) = true ∧ label (n.head a) ≤ label (n.tail a) + n.cost a) :
    ValidParents n cap s (fun v => if seen v then some (label v) else none) pred last := by
  constructor
  · simp [old.source_seen, root]
  · intro v d hv hd
    split at hd
    next known =>
      obtain rfl : label v = d := Option.some.inj hd
      cases hp : pred v with
      | none => exact False.elim (hv (old.noParent v known hp).1)
      | some a =>
        obtain ⟨head, pos, _, cameFrom, hle, hstrict⟩ := old.hasParent v a hp
        have hb := (closed a pos cameFrom).2
        rw [head] at hb
        refine ⟨a, label (n.tail a), rfl, head, pos, by simp [cameFrom], by omega, ?_⟩
        have hn : ¬ last v ≤ last (n.tail a) := fun h => lt_irrefl _ (lt_of_le_of_lt hb (hstrict h))
        omega
    next => cases hd

end Proofs.FlowResidual
