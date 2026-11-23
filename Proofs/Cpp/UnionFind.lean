import Proofs.Cpp.Gen.UnionFind
import Proofs.Cpp.Lib.Basic

/-! # `UnionFind` (library/union_find/union_find.hpp)

The array `_ps` holds a forest: a root `r` has `_ps[r] < 0`, another element its parent. `root` is the generated
self-recursion `root_rec` with path compression, proved by induction on the fuel (bounded through `nrank`). Path
compression keeps the roots, their entries and the root of every element (`Comp`). -/
open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.UnionFind

/-- `i` (an element, `i < ps.size`) has the parent `j`. -/
def Parent (ps : Array Int) (i j : Nat) : Prop := i < ps.size ∧ 0 ≤ ps[i]! ∧ ps[i]!.toNat = j

/-- Following parents from `a` reaches `b`. -/
inductive Reach (ps : Array Int) : Nat → Nat → Prop where
  | refl (a : Nat) : Reach ps a a
  | step (a b c : Nat) : Parent ps a b → Reach ps b c → Reach ps a c

/-- The forest invariant: parents of elements are elements, and `rank` strictly decreases along parent links. -/
structure Forest (ps : Array Int) (rank : Nat → Nat) : Prop where
  inside : ∀ i, i < ps.size → 0 ≤ ps[i]! → ps[i]!.toNat < ps.size
  decrease : ∀ i, i < ps.size → 0 ≤ ps[i]! → rank ps[i]!.toNat < rank i

/-- The roots: elements with a negative entry. -/
def IsRoot (ps : Array Int) (r : Nat) : Prop := r < ps.size ∧ ps[r]! < 0

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


theorem compress_step (ps ps1 : Array Int) (rank : Nat → Nat) (hF : Forest ps rank) (a : Int) (ha0 : 0 ≤ a)
    (ha : a.toNat < ps.size) (hp0 : 0 ≤ ps[a.toNat]!) (r : Int) (hr0 : 0 ≤ r)
    (hreach : Reach ps ps[a.toNat]!.toNat r.toNat) (hroot : IsRoot ps r.toNat) (hs : ps1.size = ps.size)
    (hF1 : Forest ps1 rank)
    (hfr : ∀ i, ps1[i]! = ps[i]! ∨ Reach ps ps[a.toNat]!.toNat i ∧ ¬i = r.toNat ∧ ps1[i]! = r) :
    (set ps1 a r)[a.toNat]! = r ∧ Reach ps a.toNat r.toNat ∧ Forest (set ps1 a r) rank ∧
      (∀ i, (set ps1 a r)[i]! = ps[i]! ∨ Reach ps a.toNat i ∧ ¬i = r.toNat ∧ (set ps1 a r)[i]! = r) ∧
      rank ps[a.toNat]!.toNat < rank a.toNat := by
  have ha1 : a.toNat < ps1.size := by omega
  have hget : ∀ k, (set ps1 a r)[k]! = if k = a.toNat then r else ps1[k]! := fun k => getElemBang_set _ _ _ _ ha1
  have hpar : Parent ps a.toNat ps[a.toNat]!.toNat := ⟨ha, hp0, rfl⟩
  have hra : Reach ps a.toNat r.toNat := Reach.step _ _ _ hpar hreach
  have hne : a.toNat ≠ r.toNat := fun e => by
    have := hroot.2
    rw [← e] at this
    omega
  have hrk : rank r.toNat < rank a.toNat := by
    rcases reach_rank ps rank hF _ _ hra with e | e
    · exact absurd e hne
    · exact e
  refine ⟨by rw [hget]; simp, hra, ⟨fun i hi h0 => ?_, fun i hi h0 => ?_⟩, fun i => ?_, hF.decrease _ ha hp0⟩
  · rw [size_set] at hi
    rw [hget] at h0 ⊢
    split
    · have := hroot.1; rw [size_set]; omega
    · rename_i hia; simp only [hia, ite_false] at h0; rw [size_set]; exact hF1.inside i hi h0
  · rw [size_set] at hi
    rw [hget] at h0 ⊢
    split
    · rename_i hia; subst hia; exact hrk
    · rename_i hia; simp only [hia, ite_false] at h0; exact hF1.decrease i hi h0
  · rw [hget]
    split
    · rename_i hia; subst hia; exact Or.inr ⟨Reach.refl _, hne, rfl⟩
    · rcases hfr i with e | ⟨hR, hni, e⟩
      · exact Or.inl e
      · exact Or.inr ⟨Reach.step _ _ _ hpar hR, hni, e⟩

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

/-- A node on the path from `a` to the root `r` reaches `r`. -/
theorem reach_to_root (ps : Array Int) (a i r : Nat) (h : Reach ps a i) (hr : Reach ps a r) (hroot : ps[r]! < 0) :
    Reach ps i r := by
  induction h with
  | refl _ => exact hr
  | step x b c hxb _ ih =>
    have hne : x ≠ r := fun e => by subst e; exact absurd hxb.2.1 (by omega)
    exact ih (reach_next _ _ _ _ hr hne hxb)

/-- `ps1` has the same roots (with the same entries) as `ps`, and every root reached in `ps1` is reached in `ps`:
the effect of path compression. -/
structure Comp (ps ps1 : Array Int) : Prop where
  size : ps1.size = ps.size
  root_iff : ∀ x, IsRoot ps1 x ↔ IsRoot ps x
  root_val : ∀ x, IsRoot ps x → ps1[x]! = ps[x]!
  reach : ∀ i x, Reach ps1 i x → IsRoot ps1 x → Reach ps i x

theorem comp_refl (ps : Array Int) : Comp ps ps :=
  ⟨rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ _ h _ => h⟩

theorem comp_trans (ps ps1 ps2 : Array Int) (h1 : Comp ps ps1) (h2 : Comp ps1 ps2) : Comp ps ps2 :=
  ⟨h2.size.trans h1.size, fun x => (h2.root_iff x).trans (h1.root_iff x),
    fun x hx => (h2.root_val x ((h1.root_iff x).mpr hx)).trans (h1.root_val x hx),
    fun i x hr hx => h1.reach i x (h2.reach i x hr hx) ((h2.root_iff x).mp hx)⟩

theorem compress_comp (ps ps1 : Array Int) (a : Nat) (r : Int) (hr0 : 0 ≤ r) (hra : Reach ps a r.toNat)
    (hroot : IsRoot ps r.toNat) (hs : ps1.size = ps.size)
    (hfr : ∀ i, ps1[i]! = ps[i]! ∨ (Reach ps a i ∧ i ≠ r.toNat ∧ ps1[i]! = r)) : Comp ps ps1 := by
  have hch : ∀ i, Reach ps a i → i ≠ r.toNat → 0 ≤ ps[i]! := fun i hi hne => by
    by_contra hneg
    exact hne (reach_root_unique ps a i r.toNat hi hra (by omega) hroot.2)
  have hsign : ∀ i : Nat, (ps1[i]! < (0 : Int) ↔ ps[i]! < (0 : Int)) := fun i => by
    rcases hfr i with e | ⟨hi, hne, e⟩
    · rw [e]
    · have := hch i hi hne; rw [e]; omega
  refine ⟨hs, fun x => ?_, fun x hx => ?_, fun i x hR hx => ?_⟩
  · unfold IsRoot; rw [hs, hsign]
  · rcases hfr x with e | ⟨hi, hne, e⟩
    · exact e
    · exact absurd hx.2 (by have := hch x hi hne; omega)
  · induction hR with
    | refl _ => exact Reach.refl _
    | step i j x hij _ ih =>
      have ih := ih hx
      rcases hfr i with e | ⟨hi, hne, e⟩
      · exact Reach.step _ _ _ ⟨by rw [← hs]; exact hij.1, by rw [← e]; exact hij.2.1, by rw [← e]; exact hij.2.2⟩ ih
      · have hj : j = r.toNat := by rw [← hij.2.2, e]
        subst hj
        have := root_reach_eq ps _ _ hroot.2 ih
        subst this
        exact reach_to_root ps a i _ hi hra hroot.2

/-- `root` (with path compression), by induction on the fuel. -/
theorem root_rec_spec (f : Nat) : ∀ (uf : cp.UnionFind) (rank : Nat → Nat) (a : Int),
    Forest uf._ps rank → uf._n = uf._ps.size → 0 ≤ a → a.toNat < uf._ps.size →
    nrank rank uf._ps.size a.toNat < f → ∀ t0 : Nat,
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.root_rec f uf a
    ⦃⇓ res c => ⌜0 ≤ res.1 ∧ Reach uf._ps a.toNat res.1.toNat ∧ IsRoot uf._ps res.1.toNat ∧
      res.2._ps.size = uf._ps.size ∧ res.2._n = uf._n ∧ res.2._num_groups = uf._num_groups ∧
      Forest res.2._ps rank ∧
      (∀ i, res.2._ps[i]! = uf._ps[i]! ∨ (Reach uf._ps a.toNat i ∧ i ≠ res.1.toNat ∧ res.2._ps[i]! = res.1)) ∧
      c ≤ t0 + 1 + rank a.toNat⌝⦄ := by
  induction f with
  | zero => intro _ _ _ _ _ _ _ h; omega
  | succ f ih =>
    intro uf rank a hF hn ha0 ha hf t0
    obtain ⟨ps, ng, n⟩ := uf
    simp only at hF hn ha hf ⊢
    subst hn
    by_cases hr : ps[a.toNat]! < 0
    · mvcgen [cp.UnionFind.root_rec]
      all_goals simp +zetaDelta [get] at *
      all_goals first
        | exact ⟨ha0, Reach.refl _, ⟨ha, hr⟩, hF, by omega⟩
        | (exfalso; omega)
        | (exfalso; simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
        | (simp_all <;> (exfalso; omega))
        | simp_all
    · have hp0 : 0 ≤ ps[a.toNat]! := by omega
      have hpin := hF.inside _ ha hp0
      have hdec := hF.decrease _ ha hp0
      have hlt := nrank_lt rank ps.size _ _ hpin hdec
      have hT := fun t => ih ⟨ps, ng, ps.size⟩ rank (get ps a) hF rfl hp0 (by simpa [get] using hpin)
        (by simp only [get]; omega) t
      have hW := fun (Q : PostCond (Int × cp.UnionFind) PS) => wp_of_triple (Q := Q) hT
      mvcgen [cp.UnionFind.root_rec, hW]
      all_goals simp +zetaDelta [get] at *
      case vc2.neg.isTrue.isFalse =>
        intro r b c h0 h1 h2 h3 h4 h5 h6 h7 hc
        obtain ⟨e, hra, hF2, hfr2, hrk⟩ := compress_step ps b._ps rank hF a ha0 ha hp0 r h0 h1 h2 h3 h6 h7
        rw [e]
        exact ⟨h0, hra, h2, h3, h4, h5, hF2, hfr2, by omega⟩
      all_goals first
        | (exfalso; omega)
        | (exfalso; simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
        | (simp_all <;> (exfalso; omega))
        | simp_all

/-- The invariant of the object: a forest over `_n = _ps.size < 2^31` elements. -/
def Inv (uf : cp.UnionFind) (rank : Nat → Nat) : Prop :=
  Forest uf._ps rank ∧ uf._n = uf._ps.size ∧ uf._ps.size < 2 ^ 31

/-- The root `r` of `a`. -/
def RootOf (ps : Array Int) (a r : Nat) : Prop := Reach ps a r ∧ IsRoot ps r

theorem rootOf_unique (ps : Array Int) (a r1 r2 : Nat) (h1 : RootOf ps a r1) (h2 : RootOf ps a r2) : r1 = r2 :=
  reach_root_unique ps a r1 r2 h1.1 h2.1 h1.2.2 h2.2.2

theorem root_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hI : Inv uf rank) (a : Int) (ha0 : 0 ≤ a)
    (ha : a < uf._n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.root uf a
    ⦃⇓ res c => ⌜0 ≤ res.1 ∧ RootOf uf._ps a.toNat res.1.toNat ∧ Comp uf._ps res.2._ps ∧
      Inv res.2 rank ∧ res.2._n = uf._n ∧ res.2._num_groups = uf._num_groups ∧
      c ≤ t0 + 1 + rank a.toNat⌝⦄ := by
  obtain ⟨hF, hn, hN⟩ := hI
  have hlt := nrank_le rank uf._ps.size a.toNat
  have T := root_rec_spec fuel uf rank a hF hn ha0 (by omega) (by simp only [fuel]; omega) t0
  unfold cp.UnionFind.root
  obtain ⟨res, c, hrun, h⟩ := run_of_triple T
  refine triple_of_run res c hrun ?_
  obtain ⟨h0, hR, hroot, hs1, hn1, hg1, hF1, hfr, hc⟩ := h
  exact ⟨h0, ⟨hR, hroot⟩, compress_comp _ _ _ _ h0 hR hroot hs1 hfr, ⟨hF1, by omega, by omega⟩, hn1, hg1, hc⟩

theorem root_wp (uf : cp.UnionFind) (rank : Nat → Nat) (a : Int) {Q : PostCond (Int × cp.UnionFind) PS} :
    ⦃fun t => ⌜Inv uf rank ∧ 0 ≤ a ∧ a < uf._n ∧ ∀ res c, (0 ≤ res.1 ∧ RootOf uf._ps a.toNat res.1.toNat ∧
      Comp uf._ps res.2._ps ∧ Inv res.2 rank ∧ res.2._n = uf._n ∧ res.2._num_groups = uf._num_groups ∧
      c ≤ t + 1 + rank a.toNat) → (Q.1 res c).down⌝⦄ cp.UnionFind.root uf a ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro t ht
  simp only [SPred.down_pure] at ht
  obtain ⟨hI, ha0, ha, hQ⟩ := ht
  obtain ⟨res, c, hrun, hp⟩ := run_of_triple (root_spec uf rank hI a ha0 ha t)
  simp [wp, hrun]
  exact hQ res c hp

theorem rootOf_comp (ps ps1 : Array Int) (h : Comp ps ps1) (b y : Nat) (hy : RootOf ps1 b y) : RootOf ps b y :=
  ⟨h.reach b y hy.1 hy.2, (h.root_iff y).mp hy.2⟩

theorem same_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hI : Inv uf rank) (a b : Int) (ha0 : 0 ≤ a)
    (ha : a < uf._n) (hb0 : 0 ≤ b) (hb : b < uf._n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.same uf a b
    ⦃⇓ res c => ⌜(∃ r1 r2 : Nat, RootOf uf._ps a.toNat r1 ∧ RootOf uf._ps b.toNat r2 ∧ (res.1 = true ↔ r1 = r2)) ∧
      Comp uf._ps res.2._ps ∧ Inv res.2 rank ∧ res.2._n = uf._n ∧ res.2._num_groups = uf._num_groups ∧
      c ≤ t0 + 3 + rank a.toNat + rank b.toNat⌝⦄ := by
  obtain ⟨ps, ng, n⟩ := uf
  mvcgen [cp.UnionFind.same, root_wp]
  all_goals simp +zetaDelta at *
  case vc2.isTrue.isTrue =>
    refine ⟨hI, ha0, ha, ?_⟩
    intro r1 st1 c h0 hR hC hI1 hn1 hg1 hc
    apply (Triple.iff.mp (root_wp ⟨st1._ps, st1._num_groups, st1._n⟩ rank b)) c
    refine ⟨hI1, hb0, show b < st1._n by omega, ?_⟩
    intro res c' ⟨h0', hR', hC', hI2, hn2, hg2, hc'⟩
    refine ⟨⟨r1.toNat, ⟨hR, res.1.toNat, rootOf_comp ps st1._ps hC b.toNat _ hR', by omega⟩⟩, comp_trans _ _ _ hC hC',
      hI2, by simp only at hn2; omega, by simp only at hg2; omega, by omega⟩
  all_goals (exfalso; simp_all; omega)

theorem size_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hI : Inv uf rank) (a : Int) (ha0 : 0 ≤ a)
    (ha : a < uf._n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.size_ uf a
    ⦃⇓ res c => ⌜(∃ r : Nat, RootOf uf._ps a.toNat r ∧ res.1 = -uf._ps[r]!) ∧
      Comp uf._ps res.2._ps ∧ Inv res.2 rank ∧ res.2._n = uf._n ∧ res.2._num_groups = uf._num_groups ∧
      c ≤ t0 + 2 + rank a.toNat⌝⦄ := by
  obtain ⟨ps, ng, n⟩ := uf
  mvcgen [cp.UnionFind.size_, root_wp]
  all_goals simp +zetaDelta at *
  case vc2.isTrue =>
    refine ⟨hI, ha0, ha, ?_⟩
    intro r st1 c h0 hR hC hI1 hn1 hg1 hc
    refine ⟨⟨r.toNat, hR, ?_⟩, hC, hI1, hn1, hg1, by omega⟩
    simp only [get]
    rw [hC.root_val _ hR.2]
  all_goals (exfalso; simp_all; omega)

theorem num_groups_spec (uf : cp.UnionFind) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.num_groups uf
    ⦃⇓ res c => ⌜res.1 = uf._num_groups ∧ res.2 = uf ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.UnionFind.num_groups]
  all_goals simp +zetaDelta at *
  all_goals omega

theorem init_0_spec (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.init_0
    ⦃⇓ r c => ⌜r._ps.size = 0 ∧ r._n = 0 ∧ r._num_groups = 0 ∧ Inv r (fun _ => 0) ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.UnionFind.init_0]
  all_goals simp +zetaDelta [Inv] at *
  refine ⟨⟨fun i hi => by simp at hi, fun i hi => by simp at hi⟩, by omega⟩

theorem init_int_spec (n : Int) (hn : 0 ≤ n) (hN : n < 2 ^ 31) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.init_int n
    ⦃⇓ r c => ⌜r._ps.size = n.toNat ∧ (∀ i, i < n.toNat → IsRoot r._ps i ∧ r._ps[i]! = -1) ∧ r._n = n ∧
      r._num_groups = n ∧ Inv r (fun _ => 0) ∧ c = t0 + 1 + n.toNat⌝⦄ := by
  mvcgen [cp.UnionFind.init_int]
  all_goals simp +zetaDelta [Inv, replicate] at *
  · have hg : ∀ i, i < n.toNat → (Array.replicate n.toNat (-1 : Int))[i]! = -1 := fun i hi => by
      rw [getElem!_pos _ _ (by simpa using hi)]; simp
    refine ⟨fun i hi => ⟨⟨by simp; omega, by rw [hg i (by omega)]; omega⟩, hg i (by omega)⟩,
      ⟨⟨fun i hi h => ?_, fun i hi h => ?_⟩, hn, hN⟩, by omega⟩
    all_goals (simp at hi; rw [hg i (by omega)] at h; omega)
  all_goals (exfalso; omega)

/-- `_ps[x] += _ps[y]; _ps[y] = x;` -/
def link (ps : Array Int) (x y : Int) : Array Int := set (set ps x (get ps x + get ps y)) y x

open Classical in
/-- The rank after linking: the tree of `y` moves below `x`. -/
noncomputable def urank (ps : Array Int) (rank : Nat → Nat) (x y : Nat) (i : Nat) : Nat :=
  rank i + (if Reach ps i y then rank x + 1 else 0)

theorem link_get (ps : Array Int) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxs : x.toNat < ps.size)
    (hys : y.toNat < ps.size) (hxy : x ≠ y) (i : Nat) :
    (link ps x y)[i]! = if i = y.toNat then x else if i = x.toNat then ps[x.toNat]! + ps[y.toNat]! else ps[i]! := by
  unfold link
  simp only [get]
  rw [getElemBang_set _ _ _ _ (by simp; omega), getElemBang_set _ _ _ _ (by omega)]

theorem link_forest (ps : Array Int) (rank : Nat → Nat) (hF : Forest ps rank) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hrx : IsRoot ps x.toNat) (hry : IsRoot ps y.toNat) (hxy : x ≠ y) :
    Forest (link ps x y) (urank ps rank x.toNat y.toNat) ∧ (link ps x y).size = ps.size := by
  have hs : (link ps x y).size = ps.size := by simp [link]
  have hxy' : x.toNat ≠ y.toNat := by omega
  have nx : ¬ Reach ps x.toNat y.toNat := fun h => hxy' (root_reach_eq ps _ _ hrx.2 h).symm
  have hx1 := hrx.1
  have hx2 := hrx.2
  have hy2 := hry.2
  refine ⟨⟨fun i hi h => ?_, fun i hi h => ?_⟩, hs⟩
  · rw [hs] at hi ⊢
    have hg := link_get ps x y hx hy hrx.1 hry.1 hxy i
    by_cases h1 : i = y.toNat
    · rw [hg, if_pos h1]; omega
    · by_cases h2 : i = x.toNat
      · rw [hg, if_neg h1, if_pos h2] at h; omega
      · rw [hg, if_neg h1, if_neg h2] at h ⊢; exact hF.inside i hi h
  · rw [hs] at hi
    have hg := link_get ps x y hx hy hrx.1 hry.1 hxy i
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

theorem unite_spec (uf : cp.UnionFind) (rank : Nat → Nat) (hI : Inv uf rank) (a b : Int) (ha0 : 0 ≤ a)
    (ha : a < uf._n) (hb0 : 0 ≤ b) (hb : b < uf._n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.UnionFind.unite uf a b
    ⦃⇓ res c => ⌜∃ r1 r2 : Int, 0 ≤ r1 ∧ 0 ≤ r2 ∧ RootOf uf._ps a.toNat r1.toNat ∧ RootOf uf._ps b.toNat r2.toNat ∧
      ∃ ps2, Comp uf._ps ps2 ∧ res.2._n = uf._n ∧
      (r1 = r2 → res.1 = r1 ∧ res.2._ps = ps2 ∧ res.2._num_groups = uf._num_groups) ∧
      (r1 ≠ r2 → res.2._num_groups = uf._num_groups - 1 ∧
        (-uf._ps[r1.toNat]! < -uf._ps[r2.toNat]! → res.1 = r2 ∧ res.2._ps = link ps2 r2 r1) ∧
        (¬ -uf._ps[r1.toNat]! < -uf._ps[r2.toNat]! → res.1 = r1 ∧ res.2._ps = link ps2 r1 r2)) ∧
      (∃ rank', Inv res.2 rank') ∧ c ≤ t0 + 3 + rank a.toNat + rank b.toNat⌝⦄ := by
  obtain ⟨ps, ng, n⟩ := uf
  mvcgen [cp.UnionFind.unite, root_wp]
  all_goals simp +zetaDelta at *
  case vc2.isTrue.isTrue =>
    refine ⟨hI, ha0, ha, ?_⟩
    intro r1 st1 c h0 hR hC hI1 hn1 hg1 hc
    apply (Triple.iff.mp (root_wp ⟨st1._ps, st1._num_groups, st1._n⟩ rank b)) c
    refine ⟨hI1, hb0, show b < st1._n by omega, ?_⟩
    intro res c' ⟨h0', hR', hC', hI2, hn2, hg2, hc'⟩
    obtain ⟨r2, st2⟩ := res
    simp only at h0' hR' hC' hI2 hn2 hg2 hc' ⊢
    have hR2 : RootOf ps b.toNat r2.toNat := rootOf_comp ps st1._ps hC b.toNat _ hR'
    have hC2 : Comp ps st2._ps := comp_trans _ _ _ hC hC'
    have hx2 : IsRoot st2._ps r1.toNat := (hC2.root_iff _).mpr hR.2
    have hy2 : IsRoot st2._ps r2.toNat := (hC2.root_iff _).mpr hR2.2
    have vx : st2._ps[r1.toNat]! = ps[r1.toNat]! := hC2.root_val _ hR.2
    have vy : st2._ps[r2.toNat]! = ps[r2.toNat]! := hC2.root_val _ hR2.2
    obtain ⟨hF2, hn2', hN2⟩ := hI2
    split
    · rename_i he
      subst he
      simp only [WP.pure, SPred.down_pure]
      exact ⟨r1, h0, r1, h0, hR, hR2, st2._ps, hC2, by omega, fun _ => ⟨rfl, rfl, by omega⟩,
        fun h => absurd rfl h, ⟨rank, hF2, hn2', hN2⟩, by omega⟩
    · rename_i hne
      have hne' : r2 ≠ r1 := fun e => hne e.symm
      split
      · rename_i hlt
        simp only [get] at hlt
        rw [vx, vy] at hlt
        simp only [WP.pure, SPred.down_pure]
        obtain ⟨hF3, hs3⟩ := link_forest st2._ps rank hF2 r2 r1 h0' h0 hy2 hx2 hne'
        refine ⟨r1, h0, r2, h0', hR, hR2, st2._ps, hC2, by omega, fun e => absurd e hne,
          fun _ => ⟨by omega, fun _ => ⟨rfl, rfl⟩, fun h => absurd hlt (by omega)⟩,
          ⟨_, hF3, by simp only [link, size_set] at hs3 ⊢; omega, by simp only [link, size_set]; omega⟩, by omega⟩
      · rename_i hlt
        simp only [get] at hlt
        rw [vx, vy] at hlt
        simp only [WP.pure, SPred.down_pure]
        obtain ⟨hF3, hs3⟩ := link_forest st2._ps rank hF2 r1 r2 h0 h0' hx2 hy2 hne
        refine ⟨r1, h0, r2, h0', hR, hR2, st2._ps, hC2, by omega, fun e => absurd e hne,
          fun _ => ⟨by omega, fun h => absurd h (by omega), fun _ => ⟨rfl, rfl⟩⟩,
          ⟨_, hF3, by simp only [link, size_set] at hs3 ⊢; omega, by simp only [link, size_set]; omega⟩, by omega⟩
  all_goals (exfalso; simp_all; omega)

end Proofs.Cpp.UnionFind
