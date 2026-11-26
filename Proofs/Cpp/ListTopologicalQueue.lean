import Proofs.Math.ListTopological
import Proofs.Cpp.Lib.PQ

open Proofs.Cpp

namespace Proofs.Cpp.ListTopological

inductive Discipline where
  | stack
  | minimum

def greater (a b : Int) : Bool := decide (b < a)

def Discipline.push : Discipline → List Int → Int → M (List Int)
  | .stack => stackPush
  | .minimum => pqPush

def Discipline.take (mode : Discipline) (queue : List Int) : M (Int × List Int) := do
  let vertex ← match mode with
    | .stack => stackTop queue
    | .minimum => pqTop greater queue
  let rest ← match mode with
    | .stack => stackPop queue
    | .minimum => pqPop greater queue
  return (vertex, rest)

def Discipline.pushOrder : Discipline → List Nat → Nat → List Nat
  | .stack => fun queue vertex => vertex :: queue
  | .minimum => fun queue vertex => queue ++ [vertex]

def Discipline.pushCost (mode : Discipline) (length : Nat) : Nat :=
  match mode with
  | .stack => 1
  | .minimum => Nat.log2 (length + 1) + 1

def Discipline.takeCost (mode : Discipline) (length : Nat) : Nat :=
  match mode with
  | .stack => 2
  | .minimum => Nat.log2 length + 2

theorem pushOrder_ok (mode : Discipline) : Proofs.ListTopoMath.PushOK mode.pushOrder := by
  intro queue vertex
  cases mode with
  | stack =>
    exact ⟨fun _ => List.mem_cons, fun fresh nd => List.nodup_cons.mpr ⟨fresh, nd⟩⟩
  | minimum =>
    constructor
    · intro y
      simp [Discipline.pushOrder, or_comm]
    · intro fresh nd
      rw [Discipline.pushOrder, List.nodup_append]
      refine ⟨nd, by simp, ?_⟩
      intro u hu v hv hEq
      have hq : u = vertex := hEq.trans (List.mem_singleton.mp hv)
      exact fresh (hq ▸ hu)

theorem push_run (mode : Discipline) (queue : List Int) (vertex : Int) (t : Nat) :
    let pushed := match mode with
      | .stack => vertex :: queue
      | .minimum => queue ++ [vertex]
    (mode.push queue vertex).run t = some (pushed, t + mode.pushCost queue.length) ∧
    pushed.map Int.toNat = mode.pushOrder (queue.map Int.toNat) vertex.toNat ∧
    pushed.length = queue.length + 1 := by
  cases mode <;> simp [Discipline.pushOrder] <;> rfl

private theorem erase_get_perm {α : Type} {queue : List α} {i : Nat} {x : α} (h : queue[i]? = some x) :
    queue.Perm (x :: queue.eraseIdx i) := by
  obtain ⟨hi, hvalue⟩ := List.getElem?_eq_some_iff.mp h
  have hsplit : queue = queue.take i ++ x :: queue.drop (i + 1) := by
    rw [← hvalue, List.getElem_cons_drop]
    exact (List.take_append_drop i queue).symm
  rw [List.eraseIdx_eq_take_drop_succ]
  conv_lhs => rw [hsplit]
  exact List.perm_middle

/-- Both queue disciplines remove exactly one stored vertex. With `minimum`, that vertex is smallest. -/
theorem take_run (mode : Discipline) (queue : List Int) (nonempty : queue ≠ []) (t : Nat) :
    ∃ vertex rest, (mode.take queue).run t = some ((vertex, rest), t + mode.takeCost queue.length) ∧
      queue.Perm (vertex :: rest) ∧ (mode = .minimum → ∀ w ∈ queue, vertex ≤ w) := by
  cases mode with
  | stack =>
    cases queue with
    | nil => contradiction
    | cons vertex rest =>
      exact ⟨vertex, rest, rfl, .refl _, by intro h; cases h⟩
  | minimum =>
    obtain ⟨vertex, hpos, hbest, hmin⟩ := pqBest_spec greater
      (by intro a; simp [greater]) (by intro a b c hb hc; simp [greater] at *; omega) queue nonempty
    let rest := queue.eraseIdx (pqBestIdx greater queue)
    have hperm : queue.Perm (vertex :: rest) := erase_get_perm hpos
    have he : queue.isEmpty = false := by cases queue <;> simp_all
    have hwork : t + 1 + (Nat.log2 queue.length + 1) = t + Discipline.minimum.takeCost queue.length := by
      change t + 1 + (Nat.log2 queue.length + 1) = t + (Nat.log2 queue.length + 2)
      omega
    refine ⟨vertex, rest, ?_, hperm, ?_⟩
    · unfold Discipline.take pqTop pqPop
      rw [hbest, he]
      change some ((vertex, rest), t + 1 + (Nat.log2 queue.length + 1)) = _
      rw [hwork]
    · intro _ w hw
      have h := hmin w hw
      simp [greater] at h
      omega

end Proofs.Cpp.ListTopological

open Proofs.Cpp Proofs.ListTopoMath

namespace Proofs.Cpp.ListTopological

def Discipline.limit (mode : Discipline) (n : Nat) : Nat := mode.pushCost n

theorem push_bound (mode : Discipline) {len n : Nat} (h : len ≤ n) : mode.pushCost len ≤ mode.limit n := by
  cases mode with
  | stack => rfl
  | minimum =>
    change Nat.log2 (len + 1) + 1 ≤ Nat.log2 (n + 1) + 1
    have hle := (Nat.le_log2 (by omega : n + 1 ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le (by omega : len + 1 ≠ 0)) (by omega))
    omega

def seedStep (mode : Discipline) (counts : Array Int) (vertex : Int) (queue : List Int) : M (ForInStep (List Int)) := do
  tick
  if decide (get counts vertex = 0) then
    let queue ← mode.push queue vertex
    return .yield queue
  else
    return .yield queue

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (a : α) (t : Nat) : (pure a : M α).run t = some (a, t) := rfl
private theorem some_bind {α β : Type} (a : α) (fn : α → Option β) : (some a >>= fn) = fn a := rfl

structure SeedResult (mode : Discipline) (n : Nat) (counts : Array Int) (vertices : List Nat)
    (before after : List Int) (t t' : Nat) : Prop where
  membership : ∀ v, v ∈ after.map Int.toNat ↔
    v ∈ before.map Int.toNat ∨ v ∈ vertices ∧ get counts (v : Int) = 0
  nodup : (after.map Int.toNat).Nodup
  nonneg : ∀ x ∈ after, 0 ≤ x
  length : after.length ≤ before.length + vertices.length
  work : t' ≤ t + (1 + mode.limit n) * vertices.length

/-- The generated initial seeding loop inserts each zero-degree vertex exactly once. -/
theorem seed_loop (mode : Discipline) (n : Nat) (counts : Array Int) (vertices : List Nat)
    (vnd : vertices.Nodup) :
    ∀ queue (t : Nat), (queue.map Int.toNat).Nodup → (∀ x ∈ queue, 0 ≤ x) →
      (∀ v ∈ vertices, v ∉ queue.map Int.toNat) → queue.length + vertices.length ≤ n →
      ∃ after t', (forIn (vertices.map Int.ofNat) queue (seedStep mode counts)).run t = some (after, t') ∧
        SeedResult mode n counts vertices queue after t t' := by
  induction vertices with
  | nil =>
    intro q t nd hq dj hn
    exact ⟨q, t, rfl, ⟨by simp, nd, hq, by simp, by simp⟩⟩
  | cons v vs ih =>
    intro q t nd hq dj hn
    obtain ⟨hfresh, hnd⟩ := List.nodup_cons.mp vnd
    have hvq := dj v (by simp)
    have hdis : ∀ u ∈ vs, u ∉ q.map Int.toNat := fun _ hu => dj _ (List.mem_cons_of_mem _ hu)
    rw [List.map_cons, List.forIn_cons, StateT.run_bind]
    have hlen : (v :: vs).length = vs.length + 1 := rfl
    by_cases hzero : get counts (v : Int) = 0
    · obtain ⟨hs, _, hl⟩ := push_run mode q (v : Int) (t + 1)
      let next := match mode with
        | .stack => (v : Int) :: q
        | .minimum => q ++ [(v : Int)]
      have hp : next.map Int.toNat = mode.pushOrder (q.map Int.toNat) v := by
        cases mode <;> simp [next, Discipline.pushOrder]
      have hm : ∀ u, u ∈ next.map Int.toNat ↔ u = v ∨ u ∈ q.map Int.toNat := by
        intro u
        rw [hp]
        exact (pushOrder_ok mode _ _).1 u
      have hnn : ∀ u ∈ next, 0 ≤ u := by
        intro u hu
        cases mode <;> simp [next] at hu
        · rcases hu with rfl | hu
          · omega
          · exact hq u hu
        · rcases hu with hu | rfl
          · exact hq u hu
          · omega
      have hnd' : (next.map Int.toNat).Nodup := by
        rw [hp]
        exact (pushOrder_ok mode _ _).2 hvq nd
      have hdis' : ∀ u ∈ vs, u ∉ next.map Int.toNat := by
        intro u hu e
        rcases (hm u).mp e with rfl | h
        · exact hfresh hu
        · exact hdis u hu h
      have hstep : (seedStep mode counts (Int.ofNat v) q).run t =
          some (.yield next, t + 1 + mode.pushCost q.length) := by
        unfold seedStep
        have hz : get counts (Int.ofNat v) = 0 := hzero
        change (mode.push q (Int.ofNat v)).run (t + 1) = _ at hs
        simp only [hz, decide_true, ite_true, StateT.run_bind, tick_run, some_bind, pure_run, hs]
        rfl
      rw [hstep]
      have hq' : next.length = q.length + 1 := hl
      have hc := push_bound mode (len := q.length) (n := n) (by omega)
      obtain ⟨result, t', hrun, hret⟩ := ih hnd next (t + 1 + mode.pushCost q.length) hnd' hnn hdis' (by omega)
      refine ⟨result, t', hrun, ⟨?_, hret.nodup, hret.nonneg, ?_, ?_⟩⟩
      · intro u
        rw [hret.membership, hm]
        by_cases he : u = v
        · subst u; simp only [hzero, List.mem_cons, true_or, or_true, and_true]
        · simp [he]
      · have := hret.length
        omega
      · have := hret.work
        rw [hlen, Nat.mul_add, Nat.mul_one]
        omega
    · have hstep : (seedStep mode counts (Int.ofNat v) q).run t = some (.yield q, t + 1) := by
        unfold seedStep
        have hz : ¬ get counts (Int.ofNat v) = 0 := hzero
        simp only [hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
      rw [hstep]
      obtain ⟨result, t', hrun, hret⟩ := ih hnd q (t + 1) nd hq hdis (by omega)
      refine ⟨result, t', hrun, ⟨?_, hret.nodup, hret.nonneg, ?_, ?_⟩⟩
      · intro u
        rw [hret.membership]
        by_cases he : u = v
        · subst u; simp only [hzero, List.mem_cons, and_false, or_false]
        · simp [he]
      · have := hret.length
        omega
      · have := hret.work
        rw [hlen, Nat.mul_add, Nat.mul_one]
        omega

end Proofs.Cpp.ListTopological
