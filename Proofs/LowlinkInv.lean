import Proofs.LowlinkGraph

namespace Proofs.LowlinkInv
open Proofs.PrimMath (Rtc)

/-! ### The abstract machine of the iterative lowlink -/

/-- Pointwise update. -/
def upd {α : Type} (f : Nat → α) (v : Nat) (a : α) : Nat → α := fun x => if x = v then a else f x

theorem upd_same {α : Type} (f : Nat → α) (v : Nat) (a : α) : upd f v a v = a := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) (v : Nat) (a : α) (x : Nat) (h : x ≠ v) : upd f v a x = f x := by simp [upd, h]

/-- The arc `q` leaves `x` (CSR positions `hd x ≤ q < hd (x+1)`) and ends at `tg q`. -/
def AdjH (hd tg : Nat → Nat) (x w : Nat) : Prop := ∃ q, hd x ≤ q ∧ q < hd (x + 1) ∧ tg q = w

structure GH (n : Nat) (hd tg : Nat → Nat) : Prop where
  mono : ∀ x, x < n → hd x ≤ hd (x + 1)
  adj_lt : ∀ x w, AdjH hd tg x w → x < n ∧ w < n
  sym : ∀ x w, AdjH hd tg x w → AdjH hd tg w x
  irrefl : ∀ x, ¬ AdjH hd tg x x

/-- The state of the machine: the arrays as functions, the ghost finishing times `Fi` and visiting order `Vis`. -/
structure St where
  O : Nat → Int
  L : Nat → Int
  P : Nat → Int
  Sp : Nat → Int
  It : Nat → Int
  Fi : Nat → Int
  Sk : Nat → Nat
  Vis : List Nat
  sp : Nat

/-- `u` is the parent of `v`. -/
abbrev Pr (P : Nat → Int) (u v : Nat) : Prop := P v = (u : Int)

abbrev DescM (P : Nat → Int) (a x : Nat) : Prop := Rtc (Pr P) a x

/-- `y` is finished for every vertex strictly between `v` and `x`. -/
def Settled (st : St) (v x : Nat) : Prop :=
  DescM st.P v x ∧ ∀ y, DescM st.P v y → DescM st.P y x → y ≠ v → 0 ≤ st.Fi y

/-- The end of the interval of the subtree of `v`. -/
def finE (st : St) (v : Nat) : Int := if 0 ≤ st.Fi v then st.Fi v else (st.Vis.length : Int)

structure MInv (n : Nat) (hd tg : Nat → Nat) (st : St) : Prop where
  vis_nd : st.Vis.Nodup
  vis_lt : ∀ v ∈ st.Vis, v < n
  vis_ord : ∀ t, t < st.Vis.length → st.O (st.Vis.getD t 0) = (t : Int)
  unv_ord : ∀ v, v ∉ st.Vis → st.O v = -1
  par_none : ∀ v, v ∉ st.Vis → st.P v = -1
  par_ok : ∀ u v, Pr st.P u v → u ∈ st.Vis ∧ AdjH hd tg u v ∧ st.O u < st.O v
  fin_unv : ∀ v, v ∉ st.Vis → st.Fi v = -1
  fin_ok : ∀ v ∈ st.Vis, 0 ≤ st.Fi v → st.O v < st.Fi v ∧ st.Fi v ≤ (st.Vis.length : Int)
  sp_le : st.sp ≤ st.Vis.length
  sk_mem : ∀ i, i < st.sp → st.Sk i ∈ st.Vis ∧ st.Fi (st.Sk i) < 0
  sk_par : ∀ i, i + 1 < st.sp → Pr st.P (st.Sk i) (st.Sk (i + 1))
  sk_root : 0 < st.sp → st.P (st.Sk 0) = -1
  sk_cover : ∀ v ∈ st.Vis, st.Fi v < 0 → ∃ i, i < st.sp ∧ st.Sk i = v
  interval : ∀ v ∈ st.Vis, ∀ y ∈ st.Vis, (DescM st.P v y ↔ st.O v ≤ st.O y ∧ st.O y < finE st v)
  nbr_fin : ∀ x ∈ st.Vis, 0 ≤ st.Fi x → ∀ w, AdjH hd tg x w → w ∈ st.Vis ∧ st.O w < st.Fi x
  desc_fin : ∀ v ∈ st.Vis, 0 ≤ st.Fi v → ∀ x, DescM st.P v x → 0 ≤ st.Fi x ∧ st.Fi x ≤ st.Fi v
  it_rng : ∀ x ∈ st.Vis, (hd x : Int) ≤ st.It x ∧ st.It x ≤ (hd (x + 1) : Int)
  it_scan : ∀ x ∈ st.Vis, ∀ q : Nat, hd x ≤ q → (q : Int) < st.It x → tg q ∈ st.Vis
  it_fin : ∀ x ∈ st.Vis, 0 ≤ st.Fi x → st.It x = (hd (x + 1) : Int)
  low_le : ∀ v ∈ st.Vis, 0 ≤ st.L v ∧ st.L v ≤ st.O v
  low_mem : ∀ v ∈ st.Vis, st.L v = st.O v ∨
    ∃ x w, DescM st.P v x ∧ AdjH hd tg x w ∧ st.P x ≠ (w : Int) ∧ st.O w = st.L v
  low_min : ∀ v ∈ st.Vis, ∀ x w q : Nat, Settled st v x → hd x ≤ q → (q : Int) < st.It x → tg q = w →
    st.P x ≠ (w : Int) → st.L v ≤ st.O w
  sep_cnt : ∀ p ∈ st.Vis, st.Sp p =
    ((st.Vis.filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c))).length : Int)
  sep_unv : ∀ v, v ∉ st.Vis → st.Sp v = 0
  par_neg : ∀ v, st.P v < 0 → st.P v = -1


namespace MInv
variable {n : Nat} {hd tg : Nat → Nat} {st : St}

theorem ord_idx (I : MInv n hd tg st) {v : Nat} (hv : v ∈ st.Vis) : ∃ t, t < st.Vis.length ∧ st.O v = (t : Int) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hv
  refine ⟨t, ht, ?_⟩
  have := I.vis_ord t ht
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at this

theorem ord_lt_len (I : MInv n hd tg st) {v : Nat} (hv : v ∈ st.Vis) : 0 ≤ st.O v ∧ st.O v < (st.Vis.length : Int) := by
  obtain ⟨t, ht, h⟩ := I.ord_idx hv
  rw [h]
  omega

theorem vis_of_nn (I : MInv n hd tg st) {v : Nat} (h : 0 ≤ st.O v) : v ∈ st.Vis := by
  apply Classical.byContradiction
  intro hv
  have := I.unv_ord v hv
  omega

theorem ord_inj (I : MInv n hd tg st) {u v : Nat} (hu : u ∈ st.Vis) (hv : v ∈ st.Vis) (h : st.O u = st.O v) : u = v := by
  obtain ⟨t1, h1, rfl⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨t2, h2, rfl⟩ := List.mem_iff_getElem.mp hv
  have e1 := I.vis_ord t1 h1
  have e2 := I.vis_ord t2 h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at e2
  simp only [Option.getD_some] at e1 e2
  have ht : t1 = t2 := by omega
  subst ht
  rfl

theorem par_vis (I : MInv n hd tg st) {u v : Nat} (h : Pr st.P u v) : v ∈ st.Vis := by
  apply Classical.byContradiction
  intro hv
  have := I.par_none v hv
  unfold Pr at h
  omega

theorem desc_vis (I : MInv n hd tg st) {v x : Nat} (hv : v ∈ st.Vis) (h : DescM st.P v x) : x ∈ st.Vis := by
  induction h with
  | refl => exact hv
  | tail _ hbc _ => exact I.par_vis hbc

theorem desc_vis_rev (I : MInv n hd tg st) {v x : Nat} (h : DescM st.P v x) (hx : x ∈ st.Vis) : v ∈ st.Vis := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact ih (I.par_ok _ _ hbc).1

theorem desc_ord (I : MInv n hd tg st) {v x : Nat} (hv : v ∈ st.Vis) (h : DescM st.P v x) : st.O v ≤ st.O x := by
  induction h with
  | refl => exact Int.le_refl _
  | tail hab hbc ih =>
    have hb := I.desc_vis hv hab
    have := (I.par_ok _ _ hbc).2.2
    omega

theorem desc_ord_lt (I : MInv n hd tg st) {v x : Nat} (hv : v ∈ st.Vis) (h : DescM st.P v x) (hne : v ≠ x) :
    st.O v < st.O x := by
  cases h with
  | refl => exact absurd rfl hne
  | tail hab hbc =>
    have hb := I.desc_vis hv hab
    have h1 := I.desc_ord hv hab
    have := (I.par_ok _ _ hbc).2.2
    omega

theorem stack_desc (I : MInv n hd tg st) {i j : Nat} (hij : i ≤ j) (hj : j < st.sp) : DescM st.P (st.Sk i) (st.Sk j) := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact Rtc.refl _
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact Rtc.refl _
    · exact Rtc.tail (ih (by omega) (by omega)) (I.sk_par j hj)

theorem stack_ord (I : MInv n hd tg st) {i j : Nat} (hij : i < j) (hj : j < st.sp) : st.O (st.Sk i) < st.O (st.Sk j) := by
  have hi := (I.sk_mem i (by omega)).1
  have hd := I.stack_desc (Nat.le_of_lt hij) hj
  apply I.desc_ord_lt hi hd
  intro h
  -- equal vertices on the stack would have equal orders along the chain
  have h1 : st.O (st.Sk i) < st.O (st.Sk (i + 1)) := (I.par_ok _ _ (I.sk_par i (by omega))).2.2
  have h2 : st.O (st.Sk (i + 1)) ≤ st.O (st.Sk j) :=
    I.desc_ord (I.sk_mem (i + 1) (by omega)).1 (I.stack_desc (by omega) hj)
  rw [h] at h1
  omega

/-- A vertex that is not finished is an ancestor of the top of the stack. -/
theorem unfin_desc_top (I : MInv n hd tg st) {v : Nat} (hv : v ∈ st.Vis) (hf : st.Fi v < 0) (hsp : 0 < st.sp) :
    DescM st.P v (st.Sk (st.sp - 1)) := by
  obtain ⟨i, hi, rfl⟩ := I.sk_cover v hv hf
  exact I.stack_desc (by omega) (by omega)

/-- A finished vertex is not an ancestor of the top of the stack. -/
theorem fin_not_desc_top (I : MInv n hd tg st) {v : Nat} (hv : v ∈ st.Vis) (hf : 0 ≤ st.Fi v) (hsp : 0 < st.sp) :
    ¬ DescM st.P v (st.Sk (st.sp - 1)) := by
  intro h
  have := (I.desc_fin v hv hf _ h).1
  have := (I.sk_mem (st.sp - 1) (by omega)).2
  omega

theorem vis_len_le (I : MInv n hd tg st) : st.Vis.length ≤ n := by
  have hsub : st.Vis ⊆ List.range n := fun v hv => List.mem_range.mpr (I.vis_lt v hv)
  have := List.Nodup.length_le_of_subset I.vis_nd hsub
  simpa using this

theorem sep_le (I : MInv n hd tg st) {p : Nat} (hp : p ∈ st.Vis) : st.Sp p ≤ (st.Vis.length : Int) := by
  rw [I.sep_cnt p hp]
  have := List.length_filter_le (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c)) st.Vis
  exact_mod_cast this

/-- The parent of the top `v` of the stack. -/
theorem top_parent (I : MInv n hd tg st) {v : Nat} (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v) :
    (st.sp = 1 → st.P v = -1) ∧ (2 ≤ st.sp → st.P v = ((st.Sk (st.sp - 2) : Nat) : Int)) := by
  constructor
  · intro h1
    have := I.sk_root hsp
    have e : st.sp - 1 = 0 := by omega
    rw [e] at hv
    rw [← hv]
    exact this
  · intro h2
    have := I.sk_par (st.sp - 2) (by omega)
    have e : st.sp - 2 + 1 = st.sp - 1 := by omega
    rw [e, hv] at this
    exact this

end MInv

end Proofs.LowlinkInv
