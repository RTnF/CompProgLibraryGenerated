import Proofs.Cpp.Gen.UnionFind
import Proofs.Cpp.Lib.Basic

/-! # `UnionFind` (library/union_find/union_find.hpp) -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.UnionFind

/-- `i` (an element, `i + 1 < ps.size`) has the parent `j`. -/
def Parent (ps : Array Int) (i j : Nat) : Prop := i + 1 < ps.size ∧ 0 ≤ ps[i]! ∧ ps[i]!.toNat = j

/-- Following parents from `a` reaches `b`. -/
inductive Reach (ps : Array Int) : Nat → Nat → Prop where
  | refl (a : Nat) : Reach ps a a
  | step (a b c : Nat) : Parent ps a b → Reach ps b c → Reach ps a c

/-- The forest invariant: parents of elements are elements, and `rank` strictly decreases along parent links. -/
structure Forest (ps : Array Int) (rank : Nat → Nat) : Prop where
  pos : 1 ≤ ps.size
  inside : ∀ i, i + 1 < ps.size → 0 ≤ ps[i]! → ps[i]!.toNat + 1 < ps.size
  decrease : ∀ i, i + 1 < ps.size → 0 ≤ ps[i]! → rank ps[i]!.toNat < rank i

theorem countP_lt {α : Type} (p q : α → Bool) (l : List α) (h : ∀ x ∈ l, p x → q x) (x : α) (hx : x ∈ l)
    (hq : q x) (hp : ¬p x) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.countP_cons]
    have hm := List.countP_mono_left (l := l) (p := p) (q := q) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rcases List.mem_cons.mp hx with e | e
    · subst e
      have : p x = false := by simpa using hp
      rw [this, hq]; simp only [Bool.false_eq_true, ite_false, ite_true]; omega
    · have ih' := ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) e
      by_cases hpy : p y = true
      · simp [hpy, h y (by simp) hpy]; omega
      · simp only [Bool.not_eq_true] at hpy
        rw [hpy]; simp only [Bool.false_eq_true, ite_false]; omega

/-- A rank bounded by the number of elements `N`: the number of elements of smaller rank. -/
def nrank (rank : Nat → Nat) (N : Nat) (i : Nat) : Nat := (List.range N).countP (fun j => decide (rank j < rank i))

theorem nrank_le (rank : Nat → Nat) (N i : Nat) : nrank rank N i ≤ N := by
  unfold nrank
  exact Nat.le_trans (List.countP_le_length) (by simp)

theorem nrank_lt (rank : Nat → Nat) (N i j : Nat) (hj : j < N) (h : rank j < rank i) : nrank rank N j < nrank rank N i :=
  countP_lt _ _ _ (fun x _ hx => by simp at hx ⊢; omega) j (by simpa using hj) (by simpa using h) (by simp)

theorem reach_snoc (ps : Array Int) (a x p : Nat) (h : Reach ps a x) (hp : Parent ps x p) : Reach ps a p := by
  induction h with
  | refl _ => exact Reach.step _ _ _ hp (Reach.refl _)
  | step a b c hab _ ih => exact Reach.step _ _ _ hab (ih hp)

theorem find_root_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a : Nat) (ha : a + 1 < uf.ps.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.find_root uf a
    ⦃⇓ r c => ⌜0 ≤ r ∧ Reach uf.ps a r.toNat ∧ r.toNat + 1 < uf.ps.size ∧ uf.ps[r.toNat]! < 0 ∧
      c ≤ t0 + 2 + rank a⌝⦄ := by
  mvcgen [cp.UnionFind.find_root]
  case inv =>
    exact ⟨fun x c => ⌜0 ≤ x ∧ x.toNat + 1 < uf.ps.size ∧ Reach uf.ps a x.toNat ∧ c + rank x.toNat ≤ t0 + 1 + rank a⌝,
      fun x c => ⌜0 ≤ x ∧ Reach uf.ps a x.toNat ∧ x.toNat + 1 < uf.ps.size ∧ uf.ps[x.toNat]! < 0 ∧
        c ≤ t0 + 2 + rank a⌝,
      fun x => nrank rank (uf.ps.size - 1) x.toNat⟩
  all_goals simp +zetaDelta [get] at *
  case vc2.step.isTrue =>
    rename_i H h
    obtain ⟨h0, h1, h2, h3⟩ := H
    exact ⟨h0, h2, h1, h, by omega⟩
  case vc3.step.isFalse =>
    rename_i H _ h
    obtain ⟨h0, h1, h2, h3⟩ := H
    have hin := hF.inside _ h1 h
    have hdec := hF.decrease _ h1 h
    have hlt := nrank_lt rank (uf.ps.size - 1) _ _ (by omega) hdec
    exact ⟨⟨h, by omega, reach_snoc _ _ _ _ h2 ⟨h1, h, rfl⟩, by omega⟩, hlt⟩
  case vc4.pre =>
    have := nrank_le rank (uf.ps.size - 1) a
    exact ⟨⟨ha, Reach.refl _, by omega⟩, by simp only [fuel]; omega⟩
  case vc5.post.success => exact ‹_ ∧ _›

/-- The roots: elements with a negative entry. -/
def IsRoot (ps : Array Int) (r : Nat) : Prop := r + 1 < ps.size ∧ ps[r]! < 0

theorem reach_root_unique (ps : Array Int) (a r1 r2 : Nat) (h1 : Reach ps a r1) (h2 : Reach ps a r2)
    (hr1 : ps[r1]! < 0) (hr2 : ps[r2]! < 0) : r1 = r2 := by
  induction h1 generalizing r2 with
  | refl x =>
    cases h2 with
    | refl _ => rfl
    | step _ b _ hp _ => exact absurd hp.2.1 (by omega)
  | step x b c hxb _ ih =>
    cases h2 with
    | refl _ => exact absurd hxb.2.1 (by omega)
    | step _ b' _ hxb' hb' =>
      have : b = b' := by rw [← hxb.2.2, ← hxb'.2.2]
      subst this
      exact ih r2 hb' hr1 hr2

@[spec] theorem find_root_wp (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a : Int) (ha0 : 0 ≤ a) (ha : a.toNat + 1 < uf.ps.size) {Q : PostCond Int PS} :
    ⦃fun t => ⌜∀ r c, (0 ≤ r ∧ Reach uf.ps a.toNat r.toNat ∧ r.toNat + 1 < uf.ps.size ∧ uf.ps[r.toNat]! < 0 ∧
      c ≤ t + 2 + rank a.toNat) → (Q.1 r c).down⌝⦄ cp.UnionFind.find_root uf a ⦃Q⦄ := by
  have e : a = ((a.toNat : Nat) : Int) := by omega
  rw [e]
  exact wp_of_triple (fun t0 => find_root_spec uf rank hF hN a.toNat ha t0)

theorem wp_of {α : Type} {x : M α} {Q : PostCond α PS} {c : Nat} (h : ⦃fun s => ⌜s = c⌝⦄ x ⦃Q⦄) :
    (wp⟦x⟧ Q c).down := (Triple.iff.mp h) c (by simp)

theorem same_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a b : Int) (ha0 : 0 ≤ a) (ha : a.toNat + 1 < uf.ps.size) (hb0 : 0 ≤ b) (hb : b.toNat + 1 < uf.ps.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.same uf a b
    ⦃⇓ res c => ⌜(res = true ↔ ∃ r, Reach uf.ps a.toNat r ∧ Reach uf.ps b.toNat r ∧ uf.ps[r]! < 0) ∧
      c ≤ t0 + 5 + rank a.toNat + rank b.toNat⌝⦄ := by
  mvcgen [cp.UnionFind.same]
  all_goals simp +zetaDelta [size] at *
  case vc6.isTrue.isTrue.isTrue.isTrue =>
    intro r c h0 h1 h2 h3 hc
    refine (Triple.iff.mp (find_root_wp ⟨uf.ps⟩ rank hF hN b hb0 hb)) c ?_
    intro r' c' ⟨h0', h1', h2', h3', hc'⟩
    simp only [WP.pure, SPred.down_pure]
    refine ⟨⟨fun e => ⟨r'.toNat, e ▸ h1, h1', h3'⟩, fun ⟨z, hz1, hz2, hz3⟩ => ?_⟩, by omega⟩
    have e1 := reach_root_unique _ _ _ _ h1 hz1 h3 hz3
    have e2 := reach_root_unique _ _ _ _ h1' hz2 h3' hz3
    omega
  all_goals (rename_i h; first | (have := of_decide_eq_false h; omega) | omega)

theorem size_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a : Int) (ha0 : 0 ≤ a) (ha : a.toNat + 1 < uf.ps.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.size_ uf a
    ⦃⇓ res c => ⌜(∃ r, Reach uf.ps a.toNat r ∧ uf.ps[r]! < 0 ∧ res = 0 - uf.ps[r]!) ∧ c ≤ t0 + 2 + rank a.toNat⌝⦄ := by
  mvcgen [cp.UnionFind.size_]
  case inv =>
    exact ⟨fun x c => ⌜0 ≤ x ∧ x.toNat + 1 < uf.ps.size ∧ Reach uf.ps a.toNat x.toNat ∧
        c + rank x.toNat ≤ t0 + 1 + rank a.toNat⌝,
      fun x c => ⌜0 ≤ x ∧ Reach uf.ps a.toNat x.toNat ∧ uf.ps[x.toNat]! < 0 ∧ c ≤ t0 + 2 + rank a.toNat⌝,
      fun x => nrank rank (uf.ps.size - 1) x.toNat⟩
  all_goals simp +zetaDelta [get, size] at *
  case vc2.step.isTrue =>
    have H := ‹(0 : Int) ≤ _ ∧ _ + 1 < uf.ps.size ∧ _›
    rename_i h
    obtain ⟨h0, h1, h2, h3⟩ := H
    exact ⟨h0, h2, h, by omega⟩
  case vc3.step.isFalse =>
    have H := ‹(0 : Int) ≤ _ ∧ _ + 1 < uf.ps.size ∧ _›
    rename_i h
    obtain ⟨h0, h1, h2, h3⟩ := H
    have hin := hF.inside _ h1 h
    have hdec := hF.decrease _ h1 h
    have hlt := nrank_lt rank (uf.ps.size - 1) _ _ (by omega) hdec
    exact ⟨⟨h, by omega, reach_snoc _ _ _ _ h2 ⟨h1, h, rfl⟩, by omega⟩, hlt⟩
  case vc4.isTrue.isTrue.pre =>
    have := nrank_le rank (uf.ps.size - 1) a.toNat
    exact ⟨⟨ha0, ha, Reach.refl _, by omega⟩, by simp only [fuel]; omega⟩
  case vc5.isTrue.isTrue.post.success =>
    have H := ‹(0 : Int) ≤ _ ∧ Reach _ _ _ ∧ _›
    obtain ⟨h0, h1, h2, h3⟩ := H
    exact ⟨⟨_, h1, h2, rfl⟩, h3⟩
  all_goals (rename_i h; first | (have := of_decide_eq_false h; omega) | omega)

theorem num_groups_spec (uf : cp.UnionFind) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.num_groups uf
    ⦃⇓ res c => ⌜res = -1 - uf.ps[uf.ps.size - 1]! ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.UnionFind.num_groups]
  all_goals simp +zetaDelta [get, size] at *
  assumption

theorem init_int_spec (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.init_int n
    ⦃⇓ uf c => ⌜uf.ps.size = n.toNat + 1 ∧ (∀ i, i < n.toNat → uf.ps[i]! = -1) ∧ uf.ps[n.toNat]! = -1 - n ∧
      Forest uf.ps (fun _ => 0) ∧ c = t0 + 1 + (n.toNat + 1)⌝⦄ := by
  mvcgen [cp.UnionFind.init_int]
  all_goals simp +zetaDelta [get, size] at *
  case vc1.isTrue =>
    have hs : (replicate (n + 1) (-1 : Int)).size = n.toNat + 1 := by simp [replicate]; omega
    have hg : ∀ i, (set (replicate (n + 1) (-1 : Int)) n (-1 - n))[i]! =
        if i = n.toNat then -1 - n else if i < n.toNat + 1 then -1 else default := by
      intro i
      rw [getElemBang_set _ _ _ _ (by omega)]
      split
      · rfl
      · simp [replicate]
        split
        · rw [getElem!_pos _ _ (by simp; omega)]; simp
        · rw [getElem!_neg _ _ (by simp; omega)]; rfl
    have hneg : ∀ i, i + 1 < (set (replicate (n + 1) (-1 : Int)) n (-1 - n)).size →
        (set (replicate (n + 1) (-1 : Int)) n (-1 - n))[i]! < 0 := by
      intro i hi
      rw [size_set, hs] at hi
      rw [hg i]
      split
      · omega
      · rw [if_pos (by omega)]; omega
    refine ⟨hs, fun i hi => ?_, by rw [hg, if_pos rfl], ⟨by simp [hs], fun i hi h => absurd h (by
      have := hneg i hi; omega), fun i hi h => absurd h (by have := hneg i hi; omega)⟩, by omega⟩
    rw [hg, if_neg (by omega), if_pos (by omega)]
  all_goals omega

theorem init_0_spec (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.init_0
    ⦃⇓ uf c => ⌜uf.ps = [-1].toArray ∧ Forest uf.ps (fun _ => 0) ∧ c = t0 + 2⌝⦄ := by
  mvcgen [cp.UnionFind.init_0]
  all_goals simp +zetaDelta [get, size] at *
  refine ⟨rfl, ⟨by simp [replicate], fun i hi => absurd hi (by simp [replicate]), fun i hi => absurd hi (by simp [replicate])⟩, ‹_›⟩

theorem reach_rank (ps : Array Int) (rank : Nat → Nat) (hF : Forest ps rank) (x y : Nat) (h : Reach ps x y) :
    x = y ∨ rank y < rank x := by
  induction h with
  | refl _ => exact Or.inl rfl
  | step a b c hab _ ih =>
    have hd := hF.decrease a hab.1 hab.2.1
    rw [hab.2.2] at hd
    rcases ih with e | e
    · subst e; exact Or.inr hd
    · exact Or.inr (Nat.lt_trans e hd)

theorem root_reach_eq (ps : Array Int) (x y : Nat) (hx : ps[x]! < 0) (h : Reach ps x y) : y = x := by
  cases h with
  | refl _ => rfl
  | step _ b _ hp _ => exact absurd hp.2.1 (by omega)

theorem reach_next (ps : Array Int) (x y p : Nat) (h : Reach ps x y) (hxy : x ≠ y) (hp : Parent ps x p) :
    Reach ps p y := by
  cases h with
  | refl _ => exact absurd rfl hxy
  | step _ b _ hb hr =>
    have : b = p := by rw [← hb.2.2, ← hp.2.2]
    exact this ▸ hr

/-- The invariant of the compression loop of `root`: `ps` is `ps0` with some nodes of the path from `a0` (all of
rank above the current `a`) pointing at the root `r`. -/
def CInv (ps0 : Array Int) (rank : Nat → Nat) (a0 r : Nat) (ps : Array Int) (a : Nat) : Prop :=
  ps.size = ps0.size ∧ Forest ps rank ∧ Reach ps0 a0 a ∧ Reach ps0 a r ∧ IsRoot ps0 r ∧ a + 1 < ps0.size ∧
    ∀ i, ps[i]! = ps0[i]! ∨ (Reach ps0 a0 i ∧ i ≠ r ∧ ps[i]! = (r : Int) ∧ rank a < rank i)

theorem cinv_step (ps0 : Array Int) (rank : Nat → Nat) (hF0 : Forest ps0 rank) (a0 r : Nat) (ps : Array Int) (a : Nat)
    (H : CInv ps0 rank a0 r ps a) (hne : a ≠ r) :
    ps[a]! = ps0[a]! ∧ 0 ≤ ps0[a]! ∧ CInv ps0 rank a0 r (set ps (a : Int) (r : Int)) ps0[a]!.toNat ∧
      rank ps0[a]!.toNat < rank a := by
  obtain ⟨hs, hF, h1, h2, ⟨hr1, hr2⟩, ha, hm⟩ := H
  have e : ps[a]! = ps0[a]! := by
    rcases hm a with e | ⟨_, _, _, hlt⟩
    · exact e
    · omega
  have hnn : 0 ≤ ps0[a]! := by
    by_contra hneg
    exact hne (root_reach_eq ps0 a r (by omega) h2).symm
  have hpar : Parent ps0 a ps0[a]!.toNat := ⟨ha, hnn, rfl⟩
  have hdec := hF0.decrease a ha hnn
  have hin := hF0.inside a ha hnn
  have hra : rank r < rank a := by
    rcases reach_rank ps0 rank hF0 a r h2 with e' | e'
    · exact absurd e' hne
    · exact e'
  have hg : ∀ k, (set ps (a : Int) (r : Int))[k]! = if k = a then (r : Int) else ps[k]! := by
    intro k; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
  refine ⟨e, hnn, ⟨by simp [hs], ⟨by simp; exact hF.pos, fun i hi h => ?_, fun i hi h => ?_⟩,
    reach_snoc _ _ _ _ h1 hpar, reach_next _ _ _ _ h2 hne hpar, ⟨hr1, hr2⟩, by omega, fun i => ?_⟩, hdec⟩
  · simp only [size_set] at hi ⊢
    rw [hg] at h ⊢
    split
    · simp; omega
    · rename_i hia; rw [if_neg hia] at h; exact hF.inside i hi h
  · simp only [size_set] at hi
    rw [hg] at h ⊢
    split
    · rename_i hia; subst hia; simp; exact hra
    · rename_i hia; rw [if_neg hia] at h; exact hF.decrease i hi h
  · rw [hg]
    split
    · rename_i hia; subst hia; exact Or.inr ⟨h1, hne, rfl, hdec⟩
    · rcases hm i with e' | ⟨q1, q2, q3, q4⟩
      · exact Or.inl e'
      · exact Or.inr ⟨q1, q2, q3, Nat.lt_trans hdec q4⟩

theorem cinv_step_int (ps0 : Array Int) (rank : Nat → Nat) (hF0 : Forest ps0 rank) (a0 : Nat) (r : Int) (ps : Array Int)
    (a : Int) (ha : 0 ≤ a) (hr : 0 ≤ r) (H : CInv ps0 rank a0 r.toNat ps a.toNat) (hne : ¬a = r) :
    ps[a.toNat]! = ps0[a.toNat]! ∧ 0 ≤ ps0[a.toNat]! ∧ CInv ps0 rank a0 r.toNat (set ps a r) ps0[a.toNat]!.toNat ∧
      rank ps0[a.toNat]!.toNat < rank a.toNat := by
  have := cinv_step ps0 rank hF0 a0 r.toNat ps a.toNat H (by omega)
  rwa [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hr] at this

theorem root_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a : Int) (ha0 : 0 ≤ a) (ha : a.toNat + 1 < uf.ps.size) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.root uf a
    ⦃⇓ res c => ⌜0 ≤ res.1 ∧ Reach uf.ps a.toNat res.1.toNat ∧ IsRoot uf.ps res.1.toNat ∧
      res.2.ps.size = uf.ps.size ∧ Forest res.2.ps rank ∧
      (∀ i, res.2.ps[i]! = uf.ps[i]! ∨ (Reach uf.ps a.toNat i ∧ i ≠ res.1.toNat ∧ res.2.ps[i]! = res.1)) ∧
      c ≤ t0 + 3 + 2 * rank a.toNat⌝⦄ := by
  mvcgen [cp.UnionFind.root]
  case vc1.inv =>
    exact ⟨fun x c => ⌜0 ≤ x ∧ x.toNat + 1 < uf.ps.size ∧ Reach uf.ps a.toNat x.toNat ∧
        c + rank x.toNat ≤ t0 + 1 + rank a.toNat⌝,
      fun x c => ⌜0 ≤ x ∧ Reach uf.ps a.toNat x.toNat ∧ x.toNat + 1 < uf.ps.size ∧ uf.ps[x.toNat]! < 0 ∧
        c ≤ t0 + 2 + rank a.toNat⌝,
      fun x => nrank rank (uf.ps.size - 1) x.toNat⟩
  case vc5.inv =>
    rename_i r s _
    exact ⟨fun ⟨ps, x⟩ c => ⌜0 ≤ x ∧ CInv uf.ps rank a.toNat r.toNat ps x.toNat ∧
        c + rank x.toNat ≤ s + rank a.toNat⌝,
      fun ⟨ps, _⟩ c => ⌜ps.size = uf.ps.size ∧ Forest ps rank ∧
        (∀ i, ps[i]! = uf.ps[i]! ∨ (Reach uf.ps a.toNat i ∧ i ≠ r.toNat ∧ ps[i]! = r)) ∧
        c ≤ s + rank a.toNat + 1⌝,
      fun ⟨_, x⟩ => nrank rank (uf.ps.size - 1) x.toNat⟩
  all_goals simp +zetaDelta [get, size] at *
  case vc2.step.isTrue =>
    have H := ‹(0 : Int) ≤ _ ∧ _ + 1 < uf.ps.size ∧ _›
    rename_i h
    obtain ⟨h0, h1, h2, h3⟩ := H
    exact ⟨h0, h2, h1, h, by omega⟩
  case vc3.step.isFalse =>
    have H := ‹(0 : Int) ≤ _ ∧ _ + 1 < uf.ps.size ∧ _›
    rename_i h
    obtain ⟨h0, h1, h2, h3⟩ := H
    have hin := hF.inside _ h1 h
    have hdec := hF.decrease _ h1 h
    have hlt := nrank_lt rank (uf.ps.size - 1) _ _ (by omega) hdec
    exact ⟨⟨h, by omega, reach_snoc _ _ _ _ h2 ⟨h1, h, rfl⟩, by omega⟩, hlt⟩
  case vc4.isTrue.isTrue.pre =>
    have := nrank_le rank (uf.ps.size - 1) a.toNat
    exact ⟨⟨ha0, ha, Reach.refl _, by omega⟩, by simp only [fuel]; omega⟩
  case vc6.step.isTrue =>
    obtain ⟨r0, -, -, -, -⟩ := ‹(0 : Int) ≤ _ ∧ Reach _ _ _ ∧ _›
    obtain ⟨h0, ⟨hs, hF', h1, h2, hr, hlt, hm⟩, hc⟩ := ‹(0 : Int) ≤ _ ∧ CInv _ _ _ _ _ _ ∧ _›
    rename_i he
    rw [he] at hc
    refine ⟨hs, hF', fun i => ?_, by omega⟩
    rcases hm i with e | ⟨q1, q2, q3, -⟩
    · exact Or.inl e
    · exact Or.inr ⟨q1, q2, by rw [q3, Int.toNat_of_nonneg r0]⟩
  case vc7.step.isFalse =>
    obtain ⟨r0, -, -, -, -⟩ := ‹(0 : Int) ≤ _ ∧ Reach _ _ _ ∧ _›
    obtain ⟨h0, H, hc⟩ := ‹(0 : Int) ≤ _ ∧ CInv _ _ _ _ _ _ ∧ _›
    rename_i hne
    obtain ⟨e1, e2, e3, e4⟩ := cinv_step_int uf.ps rank hF _ _ _ _ h0 r0 H hne
    have hlt := nrank_lt rank (uf.ps.size - 1) _ _ (by have := e3.2.2.2.2.2.1; omega) e4
    rw [e1]
    exact ⟨⟨e2, e3, by omega⟩, hlt⟩
  case vc8.isTrue.isTrue.post.success.pre =>
    obtain ⟨r0, r1, r2, r3, r4⟩ := ‹(0 : Int) ≤ _ ∧ Reach _ _ _ ∧ _›
    have := nrank_le rank (uf.ps.size - 1) a.toNat
    exact ⟨⟨ha0, rfl, hF, Reach.refl _, r1, ⟨r2, r3⟩, ha, fun i => Or.inl rfl⟩, by simp only [fuel]; omega⟩
  case vc9.isTrue.isTrue.post.success.post.success =>
    obtain ⟨r0, r1, r2, r3, r4⟩ := ‹(0 : Int) ≤ _ ∧ Reach _ _ _ ∧ _›
    obtain ⟨q1, q2, q3, q4⟩ := ‹_ = uf.ps.size ∧ Forest _ rank ∧ _›
    exact ⟨r0, r1, ⟨r2, r3⟩, q1, q2, q3, by omega⟩
  all_goals (rename_i h; first | (have := of_decide_eq_false h; omega) | omega)

/-- `ps` after linking the root `y` under the root `x` (`x` takes the sizes, the sentinel counts one tree less). -/
def uniteArr (ps : Array Int) (x y : Int) : Array Int :=
  let ps2 := set (set ps x (get ps x + get ps y)) y x
  set ps2 ((ps.size : Int) - 1) (get ps2 ((ps.size : Int) - 1) + 1)

open Classical in
/-- The rank after `unite`: the tree of `y` moves below `x`. -/
noncomputable def urank (ps : Array Int) (rank : Nat → Nat) (x y : Nat) (i : Nat) : Nat :=
  rank i + (if Reach ps i y then rank x + 1 else 0)

theorem uniteArr_get (ps : Array Int) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxs : x.toNat + 1 < ps.size)
    (hys : y.toNat + 1 < ps.size) (hxy : x ≠ y) (i : Nat) (hi : i + 1 < ps.size) :
    (uniteArr ps x y)[i]! = if i = y.toNat then x else if i = x.toNat then ps[x.toNat]! + ps[y.toNat]! else ps[i]! := by
  unfold uniteArr
  simp only [get]
  rw [getElemBang_set _ _ _ _ (by simp; omega), if_neg (by omega), getElemBang_set _ _ _ _ (by simp; omega),
    getElemBang_set _ _ _ _ (by omega)]

theorem unite_forest (ps : Array Int) (rank : Nat → Nat) (hF : Forest ps rank) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hrx : IsRoot ps x.toNat) (hry : IsRoot ps y.toNat) (hxy : x ≠ y) :
    Forest (uniteArr ps x y) (urank ps rank x.toNat y.toNat) ∧ (uniteArr ps x y).size = ps.size := by
  have hs : (uniteArr ps x y).size = ps.size := by simp [uniteArr]
  have hxy' : x.toNat ≠ y.toNat := by omega
  have nx : ¬ Reach ps x.toNat y.toNat := fun h => hxy' (root_reach_eq ps _ _ hrx.2 h).symm
  have hx1 := hrx.1
  have hx2 := hrx.2
  have hy2 := hry.2
  refine ⟨⟨by rw [hs]; exact hF.pos, fun i hi h => ?_, fun i hi h => ?_⟩, hs⟩
  · rw [hs] at hi ⊢
    have hg := uniteArr_get ps x y hx hy hrx.1 hry.1 hxy i hi
    by_cases h1 : i = y.toNat
    · rw [hg, if_pos h1]; omega
    · by_cases h2 : i = x.toNat
      · rw [hg, if_neg h1, if_pos h2] at h; omega
      · rw [hg, if_neg h1, if_neg h2] at h ⊢; exact hF.inside i hi h
  · rw [hs] at hi
    have hg := uniteArr_get ps x y hx hy hrx.1 hry.1 hxy i hi
    unfold urank
    by_cases h1 : i = y.toNat
    · rw [hg, if_pos h1]
      subst h1
      rw [if_neg nx, if_pos (Reach.refl _)]; omega
    · by_cases h2 : i = x.toNat
      · rw [hg, if_neg h1, if_pos h2] at h; omega
      · rw [hg, if_neg h1, if_neg h2] at h ⊢
        have hd := hF.decrease i hi h
        have hp : Parent ps i ps[i]!.toNat := ⟨hi, h, rfl⟩
        by_cases hr : Reach ps i y.toNat
        · rw [if_pos hr, if_pos (reach_next _ _ _ _ hr h1 hp)]; omega
        · rw [if_neg hr, if_neg (fun h' => hr (Reach.step _ _ _ hp h'))]; omega

theorem unite_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hF : Forest uf.ps rank) (hN : uf.ps.size < 2 ^ 63)
    (a b : Int) (ha0 : 0 ≤ a) (ha : a.toNat + 1 < uf.ps.size) (hb0 : 0 ≤ b) (hb : b.toNat + 1 < uf.ps.size)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.unite uf a b
    ⦃⇓ res c => ⌜∃ r1 r2 : Int, 0 ≤ r1 ∧ 0 ≤ r2 ∧ Reach uf.ps a.toNat r1.toNat ∧ Reach uf.ps b.toNat r2.toNat ∧
      IsRoot uf.ps r1.toNat ∧ IsRoot uf.ps r2.toNat ∧
      (r1 = r2 → res.1 = r1 ∧ res.2.ps = uf.ps) ∧
      (r1 ≠ r2 → (get uf.ps r2 < get uf.ps r1 → res.1 = r2 ∧ res.2.ps = uniteArr uf.ps r2 r1) ∧
        (¬ get uf.ps r2 < get uf.ps r1 → res.1 = r1 ∧ res.2.ps = uniteArr uf.ps r1 r2)) ∧
      res.2.ps.size = uf.ps.size ∧ (∃ rank', Forest res.2.ps rank') ∧
      c ≤ t0 + 6 + rank a.toNat + rank b.toNat⌝⦄ := by
  mvcgen [cp.UnionFind.unite]
  all_goals simp +zetaDelta [size] at *
  case vc6.isTrue.isTrue.isTrue.isTrue =>
    intro r c h0 h1 h2 h3 hc
    refine (Triple.iff.mp (find_root_wp ⟨uf.ps⟩ rank hF hN b hb0 hb)) c ?_
    intro r' c' ⟨h0', h1', h2', h3', hc'⟩
    dsimp only
    have hr1 : IsRoot uf.ps r.toNat := ⟨h2, h3⟩
    have hr2 : IsRoot uf.ps r'.toNat := ⟨h2', h3'⟩
    split
    · next he =>
      simp only [WP.pure, SPred.down_pure]
      exact ⟨r, h0, r', h0', h1, h1', hr1, hr2, fun _ => ⟨rfl, trivial⟩, fun hne => absurd he hne, trivial,
        ⟨rank, hF⟩, by omega⟩
    · next hne =>
      have hne' : r' ≠ r := fun e => hne e.symm
      split
      · next hlt =>
        simp only [WP.pure, SPred.down_pure]
        obtain ⟨hF2, hs2⟩ := unite_forest uf.ps rank hF r' r h0' h0 hr2 hr1 hne'
        refine ⟨r, h0, r', h0', h1, h1', hr1, hr2, fun e => absurd e hne, fun _ => ⟨fun _ => ⟨rfl, rfl⟩,
          fun hle => absurd hlt (by omega)⟩, ?_, ⟨_, hF2⟩, by omega⟩
        exact hs2
      · next hlt =>
        simp only [WP.pure, SPred.down_pure]
        obtain ⟨hF2, hs2⟩ := unite_forest uf.ps rank hF r r' h0 h0' hr1 hr2 hne
        refine ⟨r, h0, r', h0', h1, h1', hr1, hr2, fun e => absurd e hne, fun _ => ⟨fun h => absurd h hlt,
          fun _ => ⟨rfl, rfl⟩⟩, ?_, ⟨_, hF2⟩, by omega⟩
        exact hs2
  all_goals (rename_i h; first | (have := of_decide_eq_false h; omega) | omega)

end Proofs.Cpp.UnionFind
