import Proofs.BeatsPush
namespace Proofs.BeatsModel

/-- Pending operation on a node's children: a pending assignment `lval`, or a pending addition `ladd` followed by the caps
given by the node's own maximum and minimum. -/
structure Tag where
  lval : Option Int
  ladd : Int

/-- The true array of a node whose children (before the pending operation) hold `zs`. -/
def pend (tg : Tag) (nd : Nd) (zs : List Int) : List Int :=
  match tg.lval with
  | some v => zs.map (fun _ => v)
  | none => ((zs.map (fun w => w + tg.ladd)).map (fun w => min w nd.mx)).map (fun w => max w nd.mn)

theorem pend_append (tg : Tag) (nd : Nd) (xs ys : List Int) : pend tg nd (xs ++ ys) = pend tg nd xs ++ pend tg nd ys := by
  unfold pend
  cases tg.lval <;> simp [List.map_append]

/-- `push` applied to one child with summary `c` and `len` elements. -/
def pushChild (tg : Tag) (nd : Nd) (c : Nd) (len : Int) : Nd :=
  match tg.lval with
  | some v => setNd len v
  | none => pushAdd c tg.ladd nd.mx nd.mn

/-- The conditions under which `push` is exact for a child holding `xs`. -/
def PushOk (tg : Tag) (nd : Nd) (c : Nd) (xs : List Int) : Prop :=
  match tg.lval with
  | some v => -INF < v ∧ v < INF
  | none =>
    (∀ w ∈ xs, -INF < w + tg.ladd ∧ w + tg.ladd < INF) ∧ -INF < nd.mx ∧
    (nd.mx < c.mx + tg.ladd → (if c.smx = -INF then c.smx else c.smx + tg.ladd) < nd.mx) ∧
    (∀ c2 : Nd, Desc c2 ((xs.map (fun w => w + tg.ladd)).map (fun w => min w nd.mx)) → c2.mn < nd.mn → nd.mn < c2.smn)

theorem pushChild_desc (tg : Tag) (nd c : Nd) (xs : List Int) (v0 : Int) (hv0 : v0 ∈ xs) (hr : InRange xs)
    (hd : Desc c xs) (hok : PushOk tg nd c xs) : Desc (pushChild tg nd c xs.length) (pend tg nd xs) := by
  unfold pushChild pend PushOk at *
  cases hl : tg.lval with
  | some v =>
    rw [hl] at hok
    simp only [hl] at *
    have e : xs.map (fun _ => v) = List.replicate xs.length v := by
      apply List.eq_replicate_iff.mpr; simp
    rw [e]
    have hpos : 0 < xs.length := List.length_pos_of_mem hv0
    exact setNd_desc xs.length v hok.1 hok.2 hpos
  | none =>
    rw [hl] at hok
    simp only [hl] at *
    exact pushAdd_desc c xs tg.ladd nd.mx nd.mn v0 hv0 hr hok.1 hd hok.2.1 hok.2.2.1 hok.2.2.2

end Proofs.BeatsModel
