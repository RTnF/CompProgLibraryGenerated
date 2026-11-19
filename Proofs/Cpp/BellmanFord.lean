import Proofs.Cpp.Gen.BellmanFord
import Proofs.Cpp.Lib.Basic
import Proofs.Math.BellmanFordParent

/-! # `bellman_ford` (library/graph/bellman_ford.hpp)

The translated loops keep `dist` and `parent` equal to the pure model of `Proofs.BellmanFordExec` /
`Proofs.BellmanFordPExec`: `n - 1` passes of `relaxL`/`relaxPL` (`roundsL`, `roundsPL`), then `n` marking passes
(`markRounds`). The model's theorems describe the result: `Proofs.BellmanFordBridge.bf_spec` (soundness and
completeness of the distances after the relaxation passes), `Proofs.BellmanFordParent.rounds_par` (the parent
invariant `ParInvE`) and `markRounds_id` (no change by the marking when the distances are stable). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.BellmanFordExec Proofs.BellmanFordPExec

namespace Proofs.Cpp.BellmanFord

def natL (a : Array Int) : List Nat := a.toList.map Int.toNat

theorem natL_getD (a : Array Int) (k : Nat) : (natL a).getD k 0 = (a[k]!).toNat := by
  unfold natL
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

theorem toList_set (a : Array Int) (i : Int) (x : Int) : (set a i x).toList = a.toList.set i.toNat x := by
  unfold Proofs.Cpp.set; simp [Array.set!, Array.toList_setIfInBounds]

theorem get_toList (a : Array Int) (i : Int) : get a i = a.toList.getD i.toNat 0 := by
  rw [get_eq]
  by_cases h : i.toNat < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a i.toNat h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a i.toNat h]

theorem nat_val (a : Array Int) (ha : ∀ k : Nat, 0 ≤ a[k]!) (k : Nat) : get a (k : Int) = (((natL a).getD k 0 : Nat) : Int) := by
  rw [get_eq, natL_getD]; simp; have := ha k; omega

section
variable (fr to_ cost : Array Int) (inf : Int) (hfr : ∀ k : Nat, 0 ≤ fr[k]!) (hto : ∀ k : Nat, 0 ≤ to_[k]!)
include hfr hto

/-- One relaxation: the arrays follow `relaxL` and `relaxPL`. -/
theorem relax_step (e : Nat) (dist par : Array Int) :
    let u := get fr e
    let v := get to_ e
    (get dist u ≠ inf → get dist u + get cost e < get dist v →
      (set dist v (get dist u + get cost e)).toList = relaxL inf (natL fr) (natL to_) cost.toList e dist.toList ∧
      (set par v u).toList = relaxPL inf (natL fr) (natL to_) cost.toList e dist.toList par.toList) ∧
    (get dist u ≠ inf → ¬get dist u + get cost e < get dist v →
      dist.toList = relaxL inf (natL fr) (natL to_) cost.toList e dist.toList ∧
      par.toList = relaxPL inf (natL fr) (natL to_) cost.toList e dist.toList par.toList) ∧
    (get dist u = inf →
      dist.toList = relaxL inf (natL fr) (natL to_) cost.toList e dist.toList ∧
      par.toList = relaxPL inf (natL fr) (natL to_) cost.toList e dist.toList par.toList) := by
  intro u v
  have hu : u = (((natL fr).getD e 0 : Nat) : Int) := nat_val fr hfr e
  have hv : v = (((natL to_).getD e 0 : Nat) : Int) := nat_val to_ hto e
  have gu : get dist u = dist.toList.getD ((natL fr).getD e 0) 0 := by rw [get_toList, hu, Int.toNat_natCast]
  have gv : get dist v = dist.toList.getD ((natL to_).getD e 0) 0 := by rw [get_toList, hv, Int.toNat_natCast]
  have gc : get cost (e : Int) = cost.toList.getD e 0 := by rw [get_toList, Int.toNat_natCast]
  unfold relaxL relaxPL
  rw [gu, gv, gc]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h2⟩, toList_set, toList_set, hv, hu, Int.toNat_natCast]
    exact ⟨rfl, rfl⟩
  · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2)]; exact ⟨rfl, rfl⟩
  · rw [if_neg (fun h => h.1 h1), if_neg (fun h => h.1 h1)]; exact ⟨rfl, rfl⟩

/-- One marking step: the arrays follow `markEdge`. -/
theorem mark_step (e : Nat) (dist par : Array Int) :
    let u := get fr e
    let v := get to_ e
    (get dist u ≠ inf → get dist u = -inf →
      ((set dist v (-inf)).toList, (set par v (-1)).toList) =
        markEdge inf (natL fr) (natL to_) cost.toList e (dist.toList, par.toList)) ∧
    (get dist u ≠ inf → ¬get dist u = -inf → get dist u + get cost e < get dist v →
      ((set dist v (-inf)).toList, (set par v (-1)).toList) =
        markEdge inf (natL fr) (natL to_) cost.toList e (dist.toList, par.toList)) ∧
    (get dist u ≠ inf → ¬get dist u = -inf → ¬get dist u + get cost e < get dist v →
      (dist.toList, par.toList) = markEdge inf (natL fr) (natL to_) cost.toList e (dist.toList, par.toList)) ∧
    (get dist u = inf → (dist.toList, par.toList) = markEdge inf (natL fr) (natL to_) cost.toList e (dist.toList, par.toList)) := by
  intro u v
  have hu : u = (((natL fr).getD e 0 : Nat) : Int) := nat_val fr hfr e
  have hv : v = (((natL to_).getD e 0 : Nat) : Int) := nat_val to_ hto e
  have gu : get dist u = dist.toList.getD ((natL fr).getD e 0) 0 := by rw [get_toList, hu, Int.toNat_natCast]
  have gv : get dist v = dist.toList.getD ((natL to_).getD e 0) 0 := by rw [get_toList, hv, Int.toNat_natCast]
  have gc : get cost (e : Int) = cost.toList.getD e 0 := by rw [get_toList, Int.toNat_natCast]
  unfold markEdge markIn
  rw [gu, gv, gc]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_, fun h1 => ?_⟩
  · rw [if_pos h1, if_pos h2, toList_set, toList_set, hv, Int.toNat_natCast]
  · rw [if_pos h1, if_neg h2, if_pos h3, toList_set, toList_set, hv, Int.toNat_natCast]
  · rw [if_pos h1, if_neg h2, if_neg h3]
  · rw [if_neg (fun h => h h1)]

end

section
variable {fr to_ cost : Array Int} {inf : Int}

abbrev PP (fr to_ cost : Array Int) (inf : Int) (e : Nat) (X : List Int) : List Int :=
  passPrefix inf (natL fr) (natL to_) cost.toList e X
abbrev PPP (fr to_ cost : Array Int) (inf : Int) (e : Nat) (X Y : List Int) : List Int :=
  passPrefixP inf (natL fr) (natL to_) cost.toList e X Y

theorem relax_vc (hfr : ∀ k : Nat, 0 ≤ fr[k]!) (hto : ∀ k : Nat, 0 ≤ to_[k]!) (e : Nat) (d p : Array Int)
    (X Y : List Int) (hd : d.toList = PP fr to_ cost inf e X) (hp : p.toList = PPP fr to_ cost inf e X Y) :
    (¬get d (get fr e) = inf → get d (get fr e) + get cost e < get d (get to_ e) →
      (set d (get to_ e) (get d (get fr e) + get cost e)).toList = PP fr to_ cost inf (e + 1) X ∧
      (set p (get to_ e) (get fr e)).toList = PPP fr to_ cost inf (e + 1) X Y) ∧
    (¬get d (get fr e) = inf → ¬get d (get fr e) + get cost e < get d (get to_ e) →
      d.toList = PP fr to_ cost inf (e + 1) X ∧ p.toList = PPP fr to_ cost inf (e + 1) X Y) ∧
    (get d (get fr e) = inf → d.toList = PP fr to_ cost inf (e + 1) X ∧ p.toList = PPP fr to_ cost inf (e + 1) X Y) := by
  simp only [PP, PPP] at hd hp ⊢
  simp only [passPrefix_succ, passPrefixP_succ]
  rw [← hd, ← hp]
  exact relax_step fr to_ cost inf hfr hto e d p

abbrev MP (fr to_ cost : Array Int) (inf : Int) (e : Nat) (s : List Int × List Int) : List Int × List Int :=
  markPrefix inf (natL fr) (natL to_) cost.toList e s

theorem mark_vc (hfr : ∀ k : Nat, 0 ≤ fr[k]!) (hto : ∀ k : Nat, 0 ≤ to_[k]!) (e : Nat) (d p : Array Int)
    (s : List Int × List Int) (h : (d.toList, p.toList) = MP fr to_ cost inf e s) :
    (¬get d (get fr e) = inf → get d (get fr e) = -inf →
      ((set d (get to_ e) (-inf)).toList, (set p (get to_ e) (-1)).toList) = MP fr to_ cost inf (e + 1) s) ∧
    (¬get d (get fr e) = inf → ¬get d (get fr e) = -inf → get d (get fr e) + get cost e < get d (get to_ e) →
      ((set d (get to_ e) (-inf)).toList, (set p (get to_ e) (-1)).toList) = MP fr to_ cost inf (e + 1) s) ∧
    (¬get d (get fr e) = inf → ¬get d (get fr e) = -inf → ¬get d (get fr e) + get cost e < get d (get to_ e) →
      (d.toList, p.toList) = MP fr to_ cost inf (e + 1) s) ∧
    (get d (get fr e) = inf → (d.toList, p.toList) = MP fr to_ cost inf (e + 1) s) := by
  simp only [MP] at h ⊢
  simp only [markPrefix_succ]
  rw [← h]
  exact mark_step fr to_ cost inf hfr hto e d p

end

/-- `bellman_ford(from, to, cost, dist, parent, n, inf)` for `n ≥ 1` and nonnegative vertex numbers in `from`/`to`:
the output is the model's result, in `1 + (n - 1)(1 + m) + n (1 + m)` steps (`O(n m)`). -/
theorem bellman_ford_spec (fr to_ cost dist par : Array Int) (n : Nat) (inf : Int) (hn : 1 ≤ n)
    (hfr : ∀ k : Nat, 0 ≤ fr[k]!) (hto : ∀ k : Nat, 0 ≤ to_[k]!) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.bellman_ford (Cost := Int) fr to_ cost dist par n inf
    ⦃⇓ r c => ⌜(r.1.toList, r.2.toList) = markRounds inf (natL fr) (natL to_) cost.toList fr.size n
        (roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList,
          roundsPL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList par.toList) ∧
      c = t0 + 1 + (n - 1) * (1 + fr.size) + n * (1 + fr.size)⌝⦄ := by
  mvcgen [cp.bellman_ford]
  case inv1 =>
    exact ⇓⟨xs, d, p⟩ c => ⌜d.toList = roundsL inf (natL fr) (natL to_) cost.toList fr.size xs.prefix.length dist.toList ∧
      p.toList = roundsPL inf (natL fr) (natL to_) cost.toList fr.size xs.prefix.length dist.toList par.toList ∧
      c = t0 + 1 + xs.prefix.length * (1 + fr.size)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _ _ _
    exact ⇓⟨xs, d, p⟩ c => ⌜d.toList = passPrefix inf (natL fr) (natL to_) cost.toList xs.prefix.length
        (roundsL inf (natL fr) (natL to_) cost.toList fr.size pi.length dist.toList) ∧
      p.toList = passPrefixP inf (natL fr) (natL to_) cost.toList xs.prefix.length
        (roundsL inf (natL fr) (natL to_) cost.toList fr.size pi.length dist.toList)
        (roundsPL inf (natL fr) (natL to_) cost.toList fr.size pi.length dist.toList par.toList) ∧
      c = t0 + 1 + pi.length * (1 + fr.size) + 1 + xs.prefix.length⌝
  case inv3 =>
    exact ⇓⟨xs, d, p⟩ c => ⌜(d.toList, p.toList) = markRounds inf (natL fr) (natL to_) cost.toList fr.size
        xs.prefix.length (roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList,
          roundsPL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList par.toList) ∧
      c = t0 + 1 + (n - 1) * (1 + fr.size) + xs.prefix.length * (1 + fr.size)⌝
  case inv4 =>
    rename_i pi _ _ _ _ _ _ _ _
    exact ⇓⟨xs, d, p⟩ c => ⌜(d.toList, p.toList) = markPrefix inf (natL fr) (natL to_) cost.toList xs.prefix.length
        (markRounds inf (natL fr) (natL to_) cost.toList fr.size pi.length
          (roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList,
            roundsPL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList par.toList)) ∧
      c = t0 + 1 + (n - 1) * (1 + fr.size) + pi.length * (1 + fr.size) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [size] at *
  all_goals (try (have e := range_cursor ‹range 0 (fr.size : Int) = _ ++ _ :: _›; simp at e; subst e))
  -- relaxation passes
  all_goals (try (obtain ⟨hd, hp, hc⟩ := ‹_ = passPrefix _ _ _ _ _ _ ∧ _ = passPrefixP _ _ _ _ _ _ _ ∧ _›
                  have R := relax_vc hfr hto _ _ _ _ _ hd hp
                  first
                  | exact ⟨(R.1 ‹_› ‹_›).1, (R.1 ‹_› ‹_›).2, by omega⟩
                  | exact ⟨(R.2.1 ‹_› (Int.not_lt.mpr ‹_›)).1, (R.2.1 ‹_› (Int.not_lt.mpr ‹_›)).2, by omega⟩
                  | exact ⟨(R.2.2 ‹_›).1, (R.2.2 ‹_›).2, by omega⟩))
  -- marking passes
  all_goals (try (obtain ⟨h, hc⟩ := ‹(_, _) = markPrefix _ _ _ _ _ _ ∧ _›
                  have R := mark_vc hfr hto _ _ _ _ h
                  first
                  | exact ⟨R.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨R.2.1 ‹_› ‹_› ‹_›, by omega⟩
                  | exact ⟨R.2.2.1 ‹_› ‹_› (Int.not_lt.mpr ‹_›), by omega⟩
                  | exact ⟨R.2.2.2 ‹_›, by omega⟩))
  · obtain ⟨hd, hp, hc⟩ := ‹_ = roundsL _ _ _ _ _ _ _ ∧ _›
    exact ⟨hd, hp, by omega⟩
  · obtain ⟨hd, hp, hc⟩ := ‹_ = passPrefix _ _ _ _ _ _ ∧ _›
    refine ⟨hd, hp, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · exact ⟨rfl, rfl, ‹_›⟩
  · obtain ⟨h, hc⟩ := ‹(_, _) = markRounds _ _ _ _ _ _ _ ∧ _›
    exact ⟨h, by omega⟩
  · obtain ⟨h, hc⟩ := ‹(_, _) = markPrefix _ _ _ _ _ _ ∧ _›
    refine ⟨h, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · obtain ⟨hd, hp, hc⟩ := ‹_ = roundsL _ _ _ _ _ _ _ ∧ _›
    have e : (range 0 ((n : Int) - 1)).length = n - 1 := by rw [range_length]; omega
    rw [e] at hd hp hc
    exact ⟨by rw [hd, hp]; rfl, by omega⟩
  · obtain ⟨h, hc⟩ := ‹(_, _) = markRounds _ _ _ _ _ _ _ ∧ _›
    exact ⟨h, hc⟩

/-- Without a reachable negative cycle (the distances after the relaxation passes are stable and none is `-inf`), the
marking passes change nothing: the output is the result of the `n - 1` relaxation passes. -/
theorem bellman_ford_stable (fr to_ cost dist par : Array Int) (n : Nat) (inf : Int) (hn : 1 ≤ n)
    (hfr : ∀ k : Nat, 0 ≤ fr[k]!) (hto : ∀ k : Nat, 0 ≤ to_[k]!) (hFn : ∀ x ∈ natL fr, x < n)
    (hDl : dist.size = n)
    (hst : Proofs.BellmanFordParent.Stable inf (natL fr) (natL to_) cost.toList fr.size
      (roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList))
    (hneg : ∀ x ∈ roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList, x ≠ -inf) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.bellman_ford (Cost := Int) fr to_ cost dist par n inf
    ⦃⇓ r c => ⌜r.1.toList = roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList ∧
      r.2.toList = roundsPL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList par.toList ∧
      c = t0 + 1 + (n - 1) * (1 + fr.size) + n * (1 + fr.size)⌝⦄ := by
  obtain ⟨r, c, hrun, h, hc⟩ := run_of_triple (bellman_ford_spec fr to_ cost dist par n inf hn hfr hto t0)
  apply triple_of_run r c hrun
  have hlen : (roundsL inf (natL fr) (natL to_) cost.toList fr.size (n - 1) dist.toList).length = n := by
    rw [roundsL_length]; simp [hDl]
  rw [Proofs.BellmanFordParent.markRounds_id _ _ _ _ _ _ _ _ (by simp [natL]) hFn hlen hst hneg] at h
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2, hc⟩

end Proofs.Cpp.BellmanFord
