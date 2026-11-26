import Proofs.Cpp.Lib.Basic

/-! # Kahn's algorithm with any choice of a ready vertex (the math of `ListGraph::topological_sort`)

`out v` lists the targets of the edges of `v` (with multiplicity). The state is the in-degree array `d`, the order
`P` built so far and the ready vertices `R` (a stack or a priority queue; any element may be taken). -/

namespace Proofs.ListTopoMath

open Proofs.Cpp

/-- The number of edges `u -> w` with `u < k`, `u ∉ P`. -/
def inRest (out : Nat → List Int) (P : List Nat) (w : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => inRest out P w k + if k ∈ P then 0 else (out k).count (w : Int)

structure KInv (n : Nat) (out : Nat → List Int) (d : Array Int) (P R : List Nat) : Prop where
  dsz : d.size = n
  plt : ∀ x ∈ P, x < n
  pnd : P.Nodup
  rlt : ∀ x ∈ R, x < n
  rnd : R.Nodup
  rdis : ∀ x ∈ R, x ∉ P
  cnt : ∀ w < n, d[w]! = (inRest out P w n : Int)
  ready : ∀ w < n, w ∉ P → (d[w]! = 0 ↔ w ∈ R)
  topo : ∀ j (hj : j < P.length), ∀ u < n, ((P[j] : Nat) : Int) ∈ out u → u ∈ P.take j

/-- One edge `x -> t` of the picked vertex: `if (--in_count[t] == 0) push(t)`. -/
def dstep (push : List Nat → Nat → List Nat) (st : Array Int × List Nat) (t : Int) : Array Int × List Nat :=
  let d' := Cpp.set st.1 t (Cpp.get st.1 t - 1)
  if Cpp.get d' t = 0 then (d', push st.2 t.toNat) else (d', st.2)

/-- A push adds exactly its element. -/
def PushOK (push : List Nat → Nat → List Nat) : Prop :=
  ∀ R x, (∀ y, y ∈ push R x ↔ y = x ∨ y ∈ R) ∧ (x ∉ R → R.Nodup → (push R x).Nodup)

theorem inRest_snoc (out : Nat → List Int) (P : List Nat) (x w : Nat) (hx : x ∉ P) (k : Nat) :
    inRest out P w k = inRest out (P ++ [x]) w k + if x < k then (out x).count (w : Int) else 0 := by
  induction k with
  | zero => simp [inRest]
  | succ k ih =>
    simp only [inRest, ih]
    by_cases e : k = x
    · subst e; simp [hx]
    · have h1 : (k ∈ P ++ [x]) ↔ k ∈ P := by simp [e]
      by_cases hk : k ∈ P
      · simp [hk, e]; split <;> split <;> omega
      · simp [hk, e]; split <;> split <;> omega

theorem inRest_zero_of (out : Nat → List Int) (P : List Nat) (w k : Nat) (h : inRest out P w k = 0) :
    ∀ u < k, u ∉ P → (w : Int) ∉ out u := by
  induction k with
  | zero => intro u hu; omega
  | succ k ih =>
    intro u hu huP hm
    simp only [inRest] at h
    by_cases e : u = k
    · subst e; simp [huP] at h; exact List.count_eq_zero.mp h.2 hm
    · exact ih (by omega) u (by omega) huP hm

theorem dstep_spec (push : List Nat → Nat → List Nat) (st : Array Int × List Nat) (t : Nat)
    (ht : t < st.1.size) :
    (dstep push st (t : Int)).1.size = st.1.size ∧
    (∀ w, (dstep push st (t : Int)).1[w]! = st.1[w]! - if w = t then 1 else 0) ∧
    (dstep push st (t : Int)).2 = if st.1[t]! - 1 = 0 then push st.2 t else st.2 := by
  have hset : ∀ w, (Cpp.set st.1 (t : Int) (Cpp.get st.1 (t : Int) - 1))[w]! =
      if w = t then st.1[t]! - 1 else st.1[w]! := by
    intro w; rw [getElemBang_set _ _ _ _ (by simpa using ht)]; simp [get_natCast]
  have hz : Cpp.get (Cpp.set st.1 (t : Int) (Cpp.get st.1 (t : Int) - 1)) (t : Int) = st.1[t]! - 1 := by
    rw [get_natCast, hset]; simp
  unfold dstep
  simp only [hz, Int.toNat_natCast]
  refine ⟨by split <;> simp, fun w => ?_, by split <;> simp⟩
  split <;> (simp only; rw [hset]; split <;> simp_all)

theorem count_cons_nat (t : Nat) (l : List Int) (w : Nat) :
    (((t : Int) :: l).count (w : Int)) = l.count (w : Int) + if w = t then 1 else 0 := by
  rw [List.count_cons]
  by_cases h : w = t
  · subst h; simp
  · have : ¬ ((t : Int) == (w : Int)) = true := by simp; omega
    simp [h, this]

/-- The decrement loop over the targets `ts` (all in `[0, n)`): each counter drops by the multiplicity of its
vertex, and a vertex is pushed exactly when its counter reaches 0. Counters never go below the multiplicity. -/
theorem dfold {n : Nat} (push : List Nat → Nat → List Nat) (hP : PushOK push) (ts : List Int)
    (hts : ∀ t ∈ ts, 0 ≤ t ∧ t < n) (st : Array Int × List Nat) (hsz : st.1.size = n) (hnd : st.2.Nodup)
    (hge : ∀ w < n, ((ts.count (w : Int) : Nat) : Int) ≤ st.1[w]!)
    (hdis : ∀ w ∈ st.2, ts.count (w : Int) = 0) :
    let r := ts.foldl (dstep push) st
    r.1.size = n ∧ (∀ w < n, r.1[w]! = st.1[w]! - ts.count (w : Int)) ∧
    (∀ w, w ∈ r.2 ↔ w ∈ st.2 ∨ (w < n ∧ 0 < ts.count (w : Int) ∧ r.1[w]! = 0)) ∧ r.2.Nodup := by
  induction ts generalizing st with
  | nil => exact ⟨hsz, fun w _ => by simp, fun w => by simp, hnd⟩
  | cons t ts ih =>
    intro r
    have ht := hts t (by simp)
    obtain ⟨t, rfl⟩ : ∃ t' : Nat, t = (t' : Int) := ⟨t.toNat, by omega⟩
    have htn : t < n := by omega
    obtain ⟨s1, s2, s3⟩ := dstep_spec push st t (by omega)
    set st' := dstep push st (t : Int) with hst'
    have hge' : ∀ w < n, ((ts.count (w : Int) : Nat) : Int) ≤ st'.1[w]! := by
      intro w hw
      have := hge w hw; rw [count_cons_nat] at this; rw [s2]; split <;> simp_all <;> omega
    have hnew : st.1[t]! - 1 = 0 → t ∉ st.2 := by
      intro h0 hm; have := hdis t hm; rw [count_cons_nat] at this; simp at this
    have hnd' : st'.2.Nodup := by
      rw [s3]; split
      · rename_i h0; exact (hP st.2 t).2 (hnew h0) hnd
      · exact hnd
    have hdis' : ∀ w ∈ st'.2, ts.count (w : Int) = 0 := by
      intro w hw
      rw [s3] at hw
      split at hw
      · rename_i h0
        rcases ((hP st.2 t).1 w).mp hw with rfl | hw
        · have := hge w htn; rw [count_cons_nat] at this; simp at this; omega
        · have := hdis w hw; rw [count_cons_nat] at this; omega
      · have := hdis w hw; rw [count_cons_nat] at this; omega
    obtain ⟨r1, r2, r3, r4⟩ := ih (fun x hx => hts x (by simp [hx])) st' (by rw [s1]; exact hsz) hnd' hge' hdis'
    have hr : r = ts.foldl (dstep push) st' := rfl
    rw [hr]
    refine ⟨r1, fun w hw => ?_, fun w => ?_, r4⟩
    · rw [r2 w hw, s2, count_cons_nat]; split <;> simp <;> omega
    · rw [r3 w, s3]
      constructor
      · rintro (h | ⟨hw, hc, h0⟩)
        · split at h
          · rcases ((hP st.2 t).1 w).mp h with rfl | h
            · rename_i h0
              refine Or.inr ⟨htn, by rw [count_cons_nat]; simp, ?_⟩
              have hc0 := hdis' w (by rw [s3, if_pos h0]; exact ((hP st.2 w).1 w).mpr (Or.inl rfl))
              rw [r2 w htn, s2, hc0]; simp; omega
            · exact Or.inl h
          · exact Or.inl h
        · exact Or.inr ⟨hw, by rw [count_cons_nat]; omega, h0⟩
      · rintro (h | ⟨hw, hc, h0⟩)
        · left; split
          · exact ((hP st.2 t).1 w).mpr (Or.inr h)
          · exact h
        · by_cases hc' : 0 < ts.count (w : Int)
          · exact Or.inr ⟨hw, hc', h0⟩
          · have hcz : ts.count (w : Int) = 0 := by omega
            rw [count_cons_nat, hcz] at hc
            have hwt : w = t := by by_contra h; simp [h] at hc
            subst hwt
            have : st.1[w]! - 1 = 0 := by rw [r2 w hw, s2, hcz] at h0; simpa using h0
            left; rw [if_pos this]; exact ((hP st.2 w).1 w).mpr (Or.inl rfl)

def ValidT (n : Nat) (out : Nat → List Int) : Prop := ∀ u < n, ∀ t ∈ out u, 0 ≤ t ∧ t < n

theorem count_le_inRest (out : Nat → List Int) (P : List Nat) (x w : Nat) (hx : x ∉ P) (n : Nat) (hxn : x < n) :
    (out x).count (w : Int) ≤ inRest out P w n := by
  have := inRest_snoc out P x w hx n; rw [if_pos hxn] at this; omega

/-- Taking a ready vertex `x` (the ready list is `x` and `R0`) and running the decrement loop over its edges. -/
theorem pick_step {n : Nat} {out : Nat → List Int} (hV : ValidT n out) (push : List Nat → Nat → List Nat)
    (hP : PushOK push) {d : Array Int} {P R R0 : List Nat} {x : Nat} (hI : KInv n out d P R)
    (hR : R.Perm (x :: R0)) :
    let r := (out x).foldl (dstep push) (d, R0)
    KInv n out r.1 (P ++ [x]) r.2 := by
  intro r
  have hxR : x ∈ R := hR.mem_iff.mpr List.mem_cons_self
  have hxn : x < n := hI.rlt x hxR
  have hxP : x ∉ P := hI.rdis x hxR
  have hdx : d[x]! = 0 := ((hI.ready x hxn hxP).mpr hxR)
  have hR0nd : R0.Nodup := (hR.nodup_iff.mp hI.rnd).of_cons
  have hxR0 : x ∉ R0 := (List.nodup_cons.mp (hR.nodup_iff.mp hI.rnd)).1
  have hR0 : ∀ y ∈ R0, y ∈ R := fun y hy => hR.mem_iff.mpr (by simp [hy])
  have hge : ∀ w < n, (((out x).count (w : Int) : Nat) : Int) ≤ d[w]! := by
    intro w hw; rw [hI.cnt w hw]; exact_mod_cast count_le_inRest out P x w hxP n hxn
  have hdis : ∀ w ∈ R0, (out x).count (w : Int) = 0 := by
    intro w hw
    have hwn := hI.rlt w (hR0 w hw)
    have h0 := (hI.ready w hwn (hI.rdis w (hR0 w hw))).mpr (hR0 w hw)
    have := hge w hwn; rw [h0] at this; omega
  obtain ⟨r1, r2, r3, r4⟩ := dfold push hP (out x) (hV x hxn) (d, R0) hI.dsz hR0nd hge hdis
  have hcnt' : ∀ w < n, r.1[w]! = (inRest out (P ++ [x]) w n : Int) := by
    intro w hw
    rw [r2 w hw, hI.cnt w hw]
    have := inRest_snoc out P x w hxP n; rw [if_pos hxn] at this
    push_cast [this]; omega
  -- a target of x is not in P (its predecessors would all be in P)
  have htgt : ∀ w < n, 0 < (out x).count (w : Int) → w ∉ P := by
    intro w hw hc hwP
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hwP
    have := hI.topo j hj x hxn (by rw [e]; exact List.count_pos_iff.mp hc)
    exact hxP (List.mem_of_mem_take this)
  refine ⟨r1, ?_, ?_, ?_, r4, ?_, hcnt', ?_, ?_⟩
  · intro y hy; simp at hy; rcases hy with hy | rfl
    · exact hI.plt y hy
    · exact hxn
  · rw [List.nodup_append]; exact ⟨hI.pnd, by simp, fun a ha b hb => by simp at hb; subst hb; exact fun e => hxP (e ▸ ha)⟩
  · intro y hy
    rcases (r3 y).mp hy with hy | ⟨hyn, _, _⟩
    · exact hI.rlt y (hR0 y hy)
    · exact hyn
  · intro y hy
    rcases (r3 y).mp hy with hy | ⟨hyn, hc, _⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hI.rdis y (hR0 y hy), fun e => hxR0 (e ▸ hy)⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨htgt y hyn hc, fun e => ?_⟩
      subst e
      have := hge y hyn; rw [hdx] at this; omega
  · intro w hw hwP
    simp only [List.mem_append, List.mem_singleton, not_or] at hwP
    rw [r3 w]
    constructor
    · intro h0
      by_cases hc : 0 < (out x).count (w : Int)
      · exact Or.inr ⟨hw, hc, h0⟩
      · left
        have hc0 : (out x).count (w : Int) = 0 := by omega
        have : d[w]! = 0 := by rw [r2 w hw, hc0] at h0; simpa using h0
        have hwR := (hI.ready w hw hwP.1).mp this
        have hm := hR.mem_iff.mp hwR
        simp only [List.mem_cons] at hm
        rcases hm with h | h
        · exact absurd h hwP.2
        · exact h
    · rintro (h | ⟨_, _, h0⟩)
      · rw [r2 w hw, hdis w h]
        simp
        exact (hI.ready w hw hwP.1).mpr (hR0 w h)
      · exact h0
  · intro j hj u hu hm
    by_cases hjP : j < P.length
    · have := hI.topo j hjP u hu (by simpa [List.getElem_append_left hjP] using hm)
      rw [List.take_append_of_le_length (by omega)]; exact this
    · have hjx : j = P.length := by simp at hj; omega
      subst hjx
      simp at hm ⊢
      by_contra hup
      have h0 : inRest out P x n = 0 := by have := hI.cnt x hxn; rw [hdx] at this; omega
      exact inRest_zero_of out P x n h0 u hu hup hm

theorem inRest_nil (out : Nat → List Int) (w k : Nat) :
    inRest out [] w k = ((List.range k).flatMap out).count (w : Int) := by
  induction k with
  | zero => simp [inRest]
  | succ k ih => simp [inRest, ih, List.range_succ, List.flatMap_append, List.count_append]

theorem inRest_pos (out : Nat → List Int) (P : List Nat) (w k : Nat) (h : 0 < inRest out P w k) :
    ∃ u < k, u ∉ P ∧ (w : Int) ∈ out u := by
  induction k with
  | zero => simp [inRest] at h
  | succ k ih =>
    simp only [inRest] at h
    by_cases hk : k ∈ P
    · simp [hk] at h; obtain ⟨u, hu, h1, h2⟩ := ih h; exact ⟨u, by omega, h1, h2⟩
    · by_cases hc : 0 < (out k).count (w : Int)
      · exact ⟨k, by omega, hk, List.count_pos_iff.mp hc⟩
      · have hc0 : (out k).count (w : Int) = 0 := by omega
        simp [hk, hc0] at h
        obtain ⟨u, hu, h1, h2⟩ := ih h
        exact ⟨u, by omega, h1, h2⟩

/-- The initial state: the in-degrees and the vertices without incoming edges. -/
theorem kinv_init {n : Nat} {out : Nat → List Int} (d : Array Int) (hsz : d.size = n)
    (hd : ∀ w < n, d[w]! = (((List.range n).flatMap out).count (w : Int) : Int)) (R : List Nat) (hnd : R.Nodup)
    (hR : ∀ y, y ∈ R ↔ y < n ∧ d[y]! = 0) : KInv n out d [] R := by
  refine ⟨hsz, by simp, List.nodup_nil, fun y hy => ((hR y).mp hy).1, hnd, fun y _ => by simp, ?_, ?_, ?_⟩
  · intro w hw; rw [hd w hw, inRest_nil]
  · intro w hw _; rw [hR w]; simp [hw]
  · intro j hj; simp at hj

/-- At the end (no ready vertex): `P` is a topological order of the vertices it contains, and every other vertex has
an incoming edge from a vertex outside `P` (so `P` misses a vertex only if the graph has a cycle). -/
theorem kinv_final {n : Nat} {out : Nat → List Int} {d : Array Int} {P : List Nat} (hI : KInv n out d P []) :
    P.Nodup ∧ (∀ x ∈ P, x < n) ∧
    (∀ j (hj : j < P.length), ∀ u < n, ((P[j] : Nat) : Int) ∈ out u → u ∈ P.take j) ∧
    ∀ w < n, w ∉ P → ∃ u < n, u ∉ P ∧ (w : Int) ∈ out u := by
  refine ⟨hI.pnd, hI.plt, hI.topo, fun w hw hwP => ?_⟩
  have h1 := hI.ready w hw hwP
  have h2 := hI.cnt w hw
  have : d[w]! ≠ 0 := fun h => by simpa using h1.mp h
  exact inRest_pos out P w n (by omega)

end Proofs.ListTopoMath

namespace Proofs.ListTopoMath

/-- The live ready set is the available vertices whose predecessors have all been output. -/
theorem ready_iff {n : Nat} {out : Nat → List Int} {d : Array Int} {P R : List Nat}
    (inv : KInv n out d P R) {w : Nat} (hw : w < n) (hwP : w ∉ P) :
    w ∈ R ↔ ∀ u < n, (w : Int) ∈ out u → u ∈ P := by
  rw [← inv.ready w hw hwP, inv.cnt w hw]
  constructor
  · intro zero u hu he
    by_contra hup
    exact inRest_zero_of out P w n (by omega) u hu hup he
  · intro pred
    by_contra hn
    obtain ⟨u, hu, hp, he⟩ := inRest_pos out P w n (by omega)
    exact hp (pred u hu he)

/-- A complete order lists each vertex once, with each predecessor before its target. -/
structure CompleteOrder (n : Nat) (out : Nat → List Int) (P : List Nat) : Prop where
  range : ∀ x ∈ P, x < n
  nodup : P.Nodup
  complete : ∀ x < n, x ∈ P
  ordered : ∀ j (hj : j < P.length), ∀ u < n, ((P[j] : Nat) : Int) ∈ out u → u ∈ P.take j

private theorem first_outside (P Q : List Nat) (hn : ∃ w ∈ Q, w ∉ P) :
    ∃ j, ∃ h : j < Q.length, Q[j] ∉ P ∧ ∀ u ∈ Q.take j, u ∈ P := by
  induction Q with
  | nil => simp at hn
  | cons w Q ih =>
    by_cases hw : w ∈ P
    · have htail : ∃ u ∈ Q, u ∉ P := by
        obtain ⟨u, hu, huP⟩ := hn
        rcases List.mem_cons.mp hu with rfl | ht
        · exact False.elim (huP hw)
        · exact ⟨u, ht, huP⟩
      obtain ⟨j, hj, hJ, hp⟩ := ih htail
      refine ⟨j + 1, by simpa using hj, hJ, ?_⟩
      intro u hu
      simp only [List.take_succ_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hw
      · exact hp u hu
    · exact ⟨0, by simp, hw, by simp⟩

/-- At a stuck search, any complete topological order would begin with some excluded ready vertex. -/
theorem complete_if_order_exists {n : Nat} {out : Nat → List Int} {d : Array Int} {P Q : List Nat}
    (done : KInv n out d P []) (order : CompleteOrder n out Q) : ∀ x < n, x ∈ P := by
  intro x hx
  by_contra hn
  obtain ⟨j, hj, hmissing, hpre⟩ := first_outside P Q ⟨x, order.complete x hx, hn⟩
  let w := Q[j]
  have hw := order.range w (List.getElem_mem hj)
  have hall : ∀ u < n, (w : Int) ∈ out u → u ∈ P :=
    fun u hu he => hpre u (order.ordered j hj u hu he)
  have hready := (ready_iff done hw hmissing).mpr hall
  exact List.not_mem_nil hready

/-- The order always chooses a smallest vertex among those whose predecessors are already in the prefix. -/
def GreedyPrefix (n : Nat) (out : Nat → List Int) (P : List Nat) : Prop :=
  ∀ j (hj : j < P.length) w, w < n → w ∉ P.take j →
    (∀ u < n, (w : Int) ∈ out u → u ∈ P.take j) → P[j] ≤ w

private theorem first_difference (P Q : List Nat) (hlen : P.length = Q.length) (hne : P ≠ Q) :
    ∃ j, ∃ hj : j < P.length, ∃ hq : j < Q.length, P.take j = Q.take j ∧ P[j] ≠ Q[j] := by
  induction P generalizing Q with
  | nil => exact False.elim (hne (List.length_eq_zero_iff.mp hlen.symm).symm)
  | cons p P ih =>
    cases Q with
    | nil => simp at hlen
    | cons q Q =>
      by_cases hpq : p = q
      · subst q
        obtain ⟨j, hj, hq, hp, hd⟩ := ih Q (by simpa using hlen) (by simpa using hne)
        exact ⟨j + 1, by simpa using hj, by simpa using hq, by simp [hp], hd⟩
      · exact ⟨0, by simp, by simp, rfl, hpq⟩

/-- For any different topological order the first differing vertex is strictly larger. -/
theorem greedy_lex_first {n : Nat} {out : Nat → List Int} {P Q : List Nat}
    (Pvalid : CompleteOrder n out P) (Qvalid : CompleteOrder n out Q)
    (greedy : GreedyPrefix n out P) (hne : P ≠ Q) :
    ∃ j, ∃ hj : j < P.length, ∃ hq : j < Q.length, P.take j = Q.take j ∧ P[j] < Q[j] := by
  have hs : P ⊆ Q := fun _ h => Qvalid.complete _ (Pvalid.range _ h)
  have ht : Q ⊆ P := fun _ h => Pvalid.complete _ (Qvalid.range _ h)
  have hlen := Nat.le_antisymm (Pvalid.nodup.length_le_of_subset hs) (Qvalid.nodup.length_le_of_subset ht)
  obtain ⟨j, hj, hq, hp, hd⟩ := first_difference P Q hlen hne
  have hmem := List.getElem_mem hq
  have hlt := Qvalid.range _ hmem
  have hfresh : Q[j] ∉ Q.take j := by
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hin : i < j := by simp at hi; omega
    have hiQ : i < Q.length := by omega
    have he' : Q[i] = Q[j] := by simpa using he
    have := (List.Nodup.getElem_inj Qvalid.nodup).mp he'
    omega
  have hle := greedy j hj Q[j] hlt (by rwa [hp]) (by rw [hp]; exact Qvalid.ordered j hq)
  exact ⟨j, hj, hq, hp, by omega⟩

end Proofs.ListTopoMath

namespace Proofs.ListTopoMath

/-- Selecting the smallest ready vertex extends the greedy prefix by one vertex. -/
theorem greedy_extend {n : Nat} {out : Nat → List Int} {d : Array Int} {P R : List Nat}
    {v : Nat} (h : GreedyPrefix n out P) (inv : KInv n out d P R) (min : ∀ w ∈ R, v ≤ w) :
    GreedyPrefix n out (P ++ [v]) := by
  intro j hj w hw hfresh hpred
  have hlength : (P ++ [v]).length = P.length + 1 := by simp
  by_cases hp : j < P.length
  · have he : (P ++ [v]).take j = P.take j := List.take_append_of_le_length (by omega)
    rw [he] at hfresh hpred
    rw [List.getElem_append_left hp]
    exact h j hp w hw hfresh hpred
  · have he : j = P.length := by omega
    subst j
    simp only [List.take_left, List.getElem_append_right (Nat.le_refl _), Nat.sub_self] at hfresh hpred ⊢
    exact min w ((ready_iff inv hw hfresh).mpr hpred)

/-- A vertex is either processed or ready at most once, so the queues and prefixes share n slots. -/
theorem frontier_width {n : Nat} {out : Nat → List Int} {d : Array Int} {P R : List Nat}
    (inv : KInv n out d P R) : P.length + R.length ≤ n := by
  have hnd : (P ++ R).Nodup := by
    rw [List.nodup_append]
    refine ⟨inv.pnd, inv.rnd, ?_⟩
    intro p hp r hr eq
    subst p
    exact inv.rdis r hr hp
  have hsub : P ++ R ⊆ List.range n := by
    intro v hv
    apply List.mem_range.mpr
    rcases List.mem_append.mp hv with hp | hr
    · exact inv.plt v hp
    · exact inv.rlt v hr
  simpa using hnd.length_le_of_subset hsub

end Proofs.ListTopoMath
