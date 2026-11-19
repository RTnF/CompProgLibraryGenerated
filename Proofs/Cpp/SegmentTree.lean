import Proofs.Cpp.Gen.SegmentTree
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.Lowbit
import Proofs.Cpp.Lib.SegmentTreeMath

/-! # `SegmentTree<M>` (library/segment_tree/segment_tree.hpp)

The monoid `M` is any type whose instances of `M::e()` and `op` compute a monoid `Mon M` of
`Proofs.Cpp.SegmentTreeMath` in `cE` and `cOp` steps (`Ops`); the predicates of the searches compute a pure
`p : M → Bool` in `cF` steps. `Valid m st v` says that `st` is the tree of the values `v`. Every member is proved for
all inputs that satisfy its preconditions: the result, the termination and an upper bound on the steps
(construction `O(n)`, `set`/`product`/searches `O(log n)`, `get`/`product_all` `O(1)`). -/


open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath

namespace Proofs.Cpp.SegmentTree

variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

/-- The instances of `M::e()` and `op` compute the monoid `m` in `cE` and `cOp` steps. -/
structure Ops (m : Mon M) (cE cOp : Nat) : Prop where
  e : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
    (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄
  op : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
    (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄

/-- `st` is the segment tree of the values `v`. -/
structure Valid (m : Mon M) (st : cp.SegmentTree M) (v : List M) : Prop where
  n : st.n = v.length
  nn : 0 ≤ st.n_node
  hn : 0 ≤ st.h_node
  shape : (v = [] ∧ st.n_node = 0 ∧ st.h_node = 0) ∨
    (st.n_node.toNat = 2 ^ st.h_node.toNat ∧ 1 ≤ st.h_node ∧ v.length ≤ st.n_node.toNat ∧
      (st.h_node = 1 ∨ 2 ^ (st.h_node.toNat - 1) < v.length))
  size : st.node.size = 2 * st.n_node.toNat
  allV : AllV m (fun i => st.node[i]!) (2 * st.n_node.toNat)
  tree : TInv m (fun i => st.node[i]!) st.n_node.toNat
  leaf : ∀ i, i < v.length → st.node[st.n_node.toNat + i]! = v[i]!
  pad : ∀ j, v.length ≤ j → j < st.n_node.toNat → st.node[st.n_node.toNat + j]! = m.e

/-- The height of a tree of at most `2^29` values is at most `30`. -/
theorem height_le (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (hsmall : v.length ≤ 2 ^ 29) :
    st.h_node.toNat ≤ 30 := by
  rcases hv.shape with ⟨-, -, h0⟩ | ⟨-, h1, -, h2 | h2⟩
  · simp [h0]
  · omega
  · by_contra hc
    have : 2 ^ 30 ≤ 2 ^ (st.h_node.toNat - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `get(idx)` for `0 ≤ idx < n`. -/
theorem get_spec (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (idx : Int) (h0 : 0 ≤ idx)
    (hi : idx < v.length) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.get_ st idx ⦃⇓ r c => ⌜r.1 = v[idx.toNat]! ∧ r.2 = st ∧ c = t0 + 1⌝⦄ := by
  have hn := hv.n
  have hnn := hv.nn
  mvcgen [cp.SegmentTree.get_]
  all_goals simp +zetaDelta at *
  · refine ⟨?_, by omega⟩
    rw [get_eq, show (idx + st.n_node).toNat = st.n_node.toNat + idx.toNat by omega]
    simpa using hv.leaf idx.toNat (by omega)
  · omega

/-- `product_all()` for `n ≥ 1`. -/
theorem product_all_spec (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (hne : v ≠ [])
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.product_all st
    ⦃⇓ r c => ⌜r.1 = rf m (fun i => v[i]!) 0 v.length ∧ r.2 = st ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.SegmentTree.product_all]
  rcases hv.shape with ⟨h1, _⟩ | ⟨hN, hh, hle, -⟩
  · exact absurd h1 hne
  have hNpos : 2 ≤ st.n_node.toNat := by
    have : 2 ^ 1 ≤ 2 ^ st.h_node.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hN]; exact this
  have hroot := node_rf m (fun i => st.node[i]!) st.n_node.toNat hv.allV hv.tree st.h_node.toNat 1 (le_refl _)
    (by rw [hN] <;> omega)
  simp only [Nat.one_mul] at hroot
  have hpad := rf_pad m (fun i => st.node[i]!) st.n_node.toNat v.length st.n_node.toNat hv.allV hle (le_refl _)
    (by omega) hv.pad
  rw [← hN] at hroot
  rw [show st.n_node.toNat + v.length - st.n_node.toNat = v.length by omega,
    show 2 * st.n_node.toNat - st.n_node.toNat = st.n_node.toNat by omega] at hpad
  refine ⟨?_, rfl, by omega⟩
  rw [get_eq, show (1 : Int).toNat = 1 from rfl, ← hroot, hpad]
  have := rf_shift m (fun i => st.node[i]!) st.n_node.toNat v.length 0
  simp only [Nat.add_zero] at this
  rw [this]
  apply rf_congr
  intro j _ hj
  exact hv.leaf j (by omega)

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath

theorem shr_one (x : Int) : shr x 1 = x / 2 := by simp [shr, Int.shiftRight_eq_div_pow]

theorem half_mul (z y K B : Nat) (h1 : z * 2 ≤ y) (h2 : y * K ≤ B) : z * (K * 2) ≤ B :=
  calc z * (K * 2) = (z * 2) * K := by ring
    _ ≤ y * K := Nat.mul_le_mul_right _ h1
    _ ≤ B := h2

theorem land_one (x : Int) (hx : 0 ≤ x) : land x 1 = x % 2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp [land]

variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
/-- One iteration of the product loop on `int` indices (`prod_step`). -/
theorem prod_step_int (m : Mon M) (node : Array M) (N : Nat) (T : M)
    (hV : AllV m (fun i => node[i]!) (2 * N)) (hTr : TInv m (fun i => node[i]!) N)
    (x y : Int) (lo ro : M) (hx : 0 ≤ x) (hxy : x < y)
    (hP : PInv m (fun i => node[i]!) N T x.toNat y.toNat lo ro) :
    0 ≤ shr (if land x 1 ≠ 0 then x + 1 else x) 1 ∧ 0 ≤ shr (if land y 1 ≠ 0 then y - 1 else y) 1 ∧
    PInv m (fun i => node[i]!) N T (shr (if land x 1 ≠ 0 then x + 1 else x) 1).toNat
      (shr (if land y 1 ≠ 0 then y - 1 else y) 1).toNat
      (if land x 1 ≠ 0 then m.op lo (get node x) else lo)
      (if land y 1 ≠ 0 then m.op (get node (y - 1)) ro else ro) ∧
    shr (if land y 1 ≠ 0 then y - 1 else y) 1 - shr (if land x 1 ≠ 0 then x + 1 else x) 1 < y - x := by
  have key := prod_step m (fun i => node[i]!) N T hV hTr x.toNat y.toNat lo ro hP (by omega)
  rw [land_one x hx, land_one y (by omega)]
  simp only [shr_one, get_eq]
  have hxm : x % 2 = (x.toNat % 2 : Nat) := by omega
  have hym : y % 2 = (y.toNat % 2 : Nat) := by omega
  unfold pl1 pr1 pleft pright at key
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with h2 | h2 <;>
    simp only [h1, h2] at key <;>
    simp only [hxm, hym, h1, h2] <;> norm_num <;> simp at key
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rwa [show (x / 2).toNat = x.toNat / 2 by omega, show (y / 2).toNat = y.toNat / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rwa [show (x / 2).toNat = x.toNat / 2 by omega, show ((y - 1) / 2).toNat = (y.toNat - 1) / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rwa [show ((x + 1) / 2).toNat = (x.toNat + 1) / 2 by omega, show (y / 2).toNat = y.toNat / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rwa [show ((x + 1) / 2).toNat = (x.toNat + 1) / 2 by omega,
      show ((y - 1) / 2).toNat = (y.toNat - 1) / 2 by omega]

/-- The leaves of a valid tree read as the values. -/
theorem leaves_rf (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (l k : Nat)
    (hk : l + k ≤ v.length) :
    rf m (fun i => st.node[i]!) (st.n_node.toNat + l) k = rf m (fun i => v[i]!) l k := by
  rw [rf_shift]
  apply rf_congr
  intro j _ hj
  exact hv.leaf j (by omega)

theorem product_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (st : cp.SegmentTree M) (v : List M)
    (hv : Valid m st v) (hsmall : v.length ≤ 2 ^ 29) (l r : Int) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ v.length)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.product st l r
    ⦃⇓ res c => ⌜res.1 = rf m (fun i => v[i]!) l.toNat (r - l).toNat ∧ res.2 = st ∧
      c ≤ t0 + 2 + 2 * cE + cOp + (st.h_node.toNat + 1) * (1 + 2 * cOp)⌝⦄ := by
  have hn := hv.n
  have hnn := hv.nn
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  set a : Nat → M := fun i => st.node[i]! with ha
  set N := st.n_node.toNat with hN
  set T := rf m a (N + l.toNat) (r - l).toNat with hT
  have hTv : T = rf m (fun i => v[i]!) l.toNat (r - l).toNat := leaves_rf m st v hv _ _ (by omega)
  have hlen : v.length ≤ N := by
    rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, -⟩
    · simp [h1]
    · exact h3
  mvcgen [cp.SegmentTree.product, hE, hOp]
  case vc1.inv =>
    exact ⟨fun ⟨l', r', lo, ro⟩ c => ⌜0 ≤ l' ∧ 0 ≤ r' ∧
              (PInv m a N T l'.toNat r'.toNat lo ro ∨ (l' = r' ∧ lo = m.e ∧ ro = m.e ∧ l = r)) ∧
              ∃ k, k ≤ st.h_node.toNat + 1 ∧ r'.toNat * 2 ^ k ≤ 2 * N ∧
                c ≤ t0 + 1 + 2 * cE + k * (1 + 2 * cOp)⌝,
           fun ⟨_, _, lo, ro⟩ c => ⌜m.op lo ro = T ∧ c ≤ t0 + 2 + 2 * cE + (st.h_node.toNat + 1) * (1 + 2 * cOp)⌝,
           fun ⟨l', r', _, _⟩ => (r' - l').toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × M × M›).2.2.2 = ro at *
    generalize (‹ℤ × ℤ × M × M›).2.2.1 = lo at *
    generalize (‹ℤ × ℤ × M × M›).2.1 = y at *
    generalize (‹ℤ × ℤ × M × M›).1 = x at *)
  case vc2.step.isTrue =>
    obtain ⟨h0, h1, hP | ⟨hxy, hlo, hro, hlr'⟩, k, hk, -, hc⟩ := ‹_ ∧ _ ∧ (_ ∨ _) ∧ _›
    · refine ⟨?_, by nlinarith⟩
      apply PInv_exit m _ _ _ _ _ _ _ hP; omega
    · refine ⟨?_, by nlinarith⟩
      rw [hlo, hro, m.lid _ m.he, hlr', sub_self]; rfl
  case vc7.isTrue.pre =>
    refine ⟨?_, by simp [fuel]; omega⟩
    have hcost : ∃ k, k ≤ st.h_node.toNat + 1 ∧ (r + st.n_node).toNat * 2 ^ k ≤ 2 * st.n_node.toNat ∧
        t0 + 1 + cE + cE ≤ t0 + 1 + 2 * cE + k * (1 + 2 * cOp) := ⟨0, by omega, by simp; omega, by omega⟩
    rcases eq_or_lt_of_le hlr with heq | hlt
    · refine ⟨by omega, by omega, Or.inr ?_, ?_⟩
      · first | exact ⟨by omega, rfl, rfl, heq⟩ | exact heq | simp [heq]
      · first | exact hcost | (obtain ⟨k, h1, h2, h3⟩ := hcost; exact ⟨k, h1, h2, by omega⟩)
    · have hN2 : 1 ≤ st.n_node.toNat := by
        rcases hv.shape with ⟨h1, _⟩ | ⟨h1, h2, _, -⟩
        · simp [h1] at hr; omega
        · rw [h1]; exact Nat.one_le_two_pow
      refine ⟨by omega, by omega, Or.inl ⟨by omega, by omega, by omega, m.he, m.he, ?_⟩, ?_⟩
      · rw [m.lid _ (rf_V m _ _ hv.allV _ _ (by omega)), m.rid _ (rf_V m _ _ hv.allV _ _ (by omega))]
        congr 1 <;> omega
      · first | exact hcost | (obtain ⟨k, h1, h2, h3⟩ := hcost; exact ⟨k, h1, h2, by omega⟩)
  case vc8.isTrue.post.success =>
    obtain ⟨h1, h2⟩ := ‹m.op _ _ = _ ∧ _›
    exact ⟨by rw [h1]; exact hTv, by omega⟩
  case vc9.isFalse => omega
  all_goals
    clear hTv
    obtain ⟨h0, h1, hP | ⟨hxy, -⟩, k, hk, hy, hc⟩ := ‹_ ∧ _ ∧ (_ ∨ _) ∧ _›
    swap; · omega
    have key := prod_step_int m st.node st.n_node.toNat _ hv.allV hv.tree _ _ _ _ h0 (by omega) hP
    simp only [*, ne_eq, not_false_eq_true, ite_true, ite_false, not_true_eq_false] at key
    have hP1 := hP.1
    have hshape : st.n_node.toNat = 2 ^ st.h_node.toNat := by
      rcases hv.shape with ⟨-, h2, -⟩ | ⟨h1, -, -, -⟩
      · have := hP.2.2.1; omega
      · exact h1
    have hk1 : k + 1 ≤ st.h_node.toNat + 1 := by
      have hy2 : 2 ≤ y.toNat := by omega
      have h2k : 2 * 2 ^ k ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hshape]
        calc 2 * 2 ^ k ≤ y.toNat * 2 ^ k := Nat.mul_le_mul_right _ hy2
          _ ≤ _ := hy
      have : 2 ^ k ≤ 2 ^ st.h_node.toNat := by omega
      have := (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp this
      omega
    refine ⟨⟨key.1, key.2.1, Or.inl key.2.2.1, k + 1, hk1, ?_, ?_⟩, key.2.2.2, by omega⟩
    · rw [pow_succ]
      first
        | (have : (shr (y - 1) 1).toNat * 2 ≤ y.toNat := by rw [shr_one]; omega
           exact half_mul _ _ _ _ this hy)
        | (have : (shr y 1).toNat * 2 ≤ y.toNat := by rw [shr_one]; omega
           exact half_mul _ _ _ _ this hy)
    · have : (k + 1) * (1 + 2 * cOp) = k * (1 + 2 * cOp) + (1 + 2 * cOp) := by ring
      omega

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath
variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem shr_div (x i : Int) : shr x i = x / ((2 ^ i.toNat : Nat) : Int) := by
  simp [shr, Int.shiftRight_eq_div_pow]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem fun_set (node : Array M) (i : Int) (x : M) (hi : i.toNat < node.size) :
    (fun j => (Cpp.set node i x)[j]!) = upd (fun j => node[j]!) i.toNat x := by
  funext j
  rw [getElemBang_set _ _ _ _ hi]
  rfl

theorem update_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (st : cp.SegmentTree M) (i : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.update st i
    ⦃⇓ st' c => ⌜st' = { st with node := Cpp.set st.node i (m.op (Cpp.get st.node (i * 2)) (Cpp.get st.node (i * 2 + 1))) } ∧
      c = t0 + 1 + cOp⌝⦄ := by
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  mvcgen [cp.SegmentTree.update, hOp]
  all_goals simp +zetaDelta at *
  all_goals omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem getD_list_set (v : List M) (i k : Nat) (x : M) (hi : i < v.length) :
    (v.set i x)[k]! = if k = i then x else v[k]! := by
  by_cases h : k = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

/-- The update loop of `set`: the leaf `p` holds the new value; the inner nodes off the path from `p / 2^i` to the
root hold the products of their children. -/
def SetInv (m : Mon M) (N h p : Nat) (a0 : Nat → M) (node : Array M) (i : Int) : Prop :=
  node.size = 2 * N ∧ 1 ≤ i ∧ i ≤ h + 1 ∧ SInv m (fun j => node[j]!) N (p / 2 ^ i.toNat) ∧
    AllV m (fun j => node[j]!) (2 * N) ∧ ∀ j, N ≤ j → node[j]! = a0 j

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem setinv_step (m : Mon M) (N h p : Nat) (hN : N = 2 ^ h) (hpN : N ≤ p) (hp2 : p < 2 * N) (a0 : Nat → M)
    (node : Array M) (i : Int) (P : Int) (hP : P = (p : Int)) (hI : SetInv m N h p a0 node i) (hih : i ≤ h) :
    SetInv m N h p a0 (Cpp.set node (shr P i) (m.op (Cpp.get node (shr P i * 2)) (Cpp.get node (shr P i * 2 + 1))))
      (i + 1) := by
  obtain ⟨hsz, h1, h2, hS, hV, hL⟩ := hI
  have hj : shr P i = ((p / 2 ^ i.toNat : Nat) : Int) := by rw [shr_div, hP]; norm_cast
  set j := p / 2 ^ i.toNat with hjdef
  have hi1 : 1 ≤ i.toNat := by omega
  have hpow : 2 ^ i.toNat ≤ N := by
    rw [hN]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj1 : 1 ≤ j := by
    rw [hjdef]; exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
  have hjN : j < N := by
    rw [hjdef]
    have : 2 ≤ 2 ^ i.toNat := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i.toNat := Nat.pow_le_pow_right (by norm_num) hi1
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by nlinarith)
  rw [hj]
  simp only [get_eq]
  rw [show (((j : Nat) : Int) * 2).toNat = 2 * j by omega, show (((j : Nat) : Int) * 2 + 1).toNat = 2 * j + 1 by omega]
  have hF := fun_set node (j : Int) (m.op node[2 * j]! node[2 * j + 1]!) (by simp; omega)
  simp only [Int.toNat_natCast] at hF
  unfold SetInv
  rw [hF]
  refine ⟨by simp [hsz], by omega, by omega, ?_, ?_, ?_⟩
  · have := sinv_step m (fun j => node[j]!) N j hS hj1
    rwa [show (i + 1).toNat = i.toNat + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
  · intro k hk
    simp only [upd]
    split
    · exact m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
    · exact hV k hk
  · intro k hk
    have := congrFun hF k
    rw [this]
    simp only [upd, if_neg (show k ≠ j by omega)]
    exact hL k hk

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem setinv_init (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (p : Nat)
    (hpN : st.n_node.toNat ≤ p) (hp2 : p < 2 * st.n_node.toNat) (val : M) (hval : m.V val) (P : Int)
    (hP : P.toNat = p) (hh : 0 ≤ st.h_node) :
    SetInv m st.n_node.toNat st.h_node.toNat p (fun j => (Cpp.set st.node P val)[j]!) (Cpp.set st.node P val) 1 := by
  have hsz := hv.size
  have hF := fun_set st.node P val (by omega)
  rw [hP] at hF
  unfold SetInv
  refine ⟨by simp [hsz], by omega, by omega, ?_, ?_, fun _ _ => rfl⟩
  all_goals rw [hF]
  · have := sinv_init m (fun j => st.node[j]!) st.n_node.toNat p val hv.tree hpN
    simpa using this
  · intro k hk
    simp only [upd]
    split
    · exact hval
    · exact hv.allV k hk

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem setinv_done (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v)
    (hN : st.n_node.toNat = 2 ^ st.h_node.toNat) (idx : Int) (h0 : 0 ≤ idx) (hi : idx < v.length) (val : M)
    (node : Array M) (i : Int)
    (hI : SetInv m st.n_node.toNat st.h_node.toNat (idx + st.n_node).toNat
      (fun j => (Cpp.set st.node (idx + st.n_node) val)[j]!) node i) (hih : ¬ i ≤ st.h_node) :
    Valid m ⟨st.n, st.n_node, st.h_node, node⟩ (v.set idx.toNat val) := by
  obtain ⟨hsz, h1, h2, hS, hV, hL⟩ := hI
  have hnn := hv.nn
  have hsz0 := hv.size
  have hlen : v.length ≤ st.n_node.toNat := by
    rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, -⟩
    · simp [h1] at hi; omega
    · exact h3
  have hi' : i.toNat = st.h_node.toNat + 1 := by omega
  have hzero : (idx + st.n_node).toNat / 2 ^ i.toNat = 0 := by
    rw [hi', pow_succ, ← hN]
    exact Nat.div_eq_of_lt (by omega)
  rw [hzero] at hS
  have hL' : ∀ k, (Cpp.set st.node (idx + st.n_node) val)[k]! =
      if k = (idx + st.n_node).toNat then val else st.node[k]! := fun k =>
    getElemBang_set _ _ _ _ (by omega)
  refine ⟨by simpa using hv.n, hv.nn, hv.hn, ?_, hsz, hV, sinv_zero m _ _ hS, ?_, ?_⟩
  · rcases hv.shape with ⟨h1, _⟩ | ⟨h1, h2, h3, h4⟩
    · simp [h1] at hi; omega
    · right; exact ⟨h1, h2, by simpa using h3, by simpa using h4⟩
  · intro k hk
    dsimp only
    simp only [List.length_set] at hk
    rw [hL _ (by omega)]; dsimp only; rw [hL', getD_list_set _ _ _ _ (by omega)]
    by_cases hke : k = idx.toNat
    · simp [hke, show st.n_node.toNat + idx.toNat = (idx + st.n_node).toNat by omega]
    · rw [if_neg (by omega), if_neg hke]; exact hv.leaf k hk
  · intro k hk1 hk2
    dsimp only at hk2 ⊢
    simp only [List.length_set] at hk1
    rw [hL _ (by omega)]; dsimp only; rw [hL', if_neg (by omega)]
    exact hv.pad k hk1 hk2

theorem set_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (st : cp.SegmentTree M) (v : List M)
    (hv : Valid m st v) (hsmall : v.length ≤ 2 ^ 29) (idx : Int) (h0 : 0 ≤ idx) (hi : idx < v.length) (val : M)
    (hval : m.V val) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.set_ st idx val
    ⦃⇓ st' c => ⌜Valid m st' (v.set idx.toNat val) ∧ c = t0 + 2 + st.h_node.toNat * (2 + cOp)⌝⦄ := by
  have hn := hv.n
  have hnn := hv.nn
  have hU : ∀ (st : cp.SegmentTree M) (i : Int) {Q : PostCond (cp.SegmentTree M) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.SegmentTree.update st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.SegmentTree.update, hOp]
  rcases hv.shape with ⟨hnil, -⟩ | ⟨hN, hh, hle, -⟩
  · simp [hnil] at hi; omega
  have hlen : v.length ≤ st.n_node.toNat := hle
  have hht := height_le m st v hv hsmall
  mvcgen [cp.SegmentTree.set_, hU]
  case vc1.inv =>
    exact ⟨fun ⟨n', nn', hh', node', i⟩ c => ⌜n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧
              SetInv m st.n_node.toNat st.h_node.toNat (idx + st.n_node).toNat
                (fun j => (Cpp.set st.node (idx + st.n_node) val)[j]!) node' i ∧
              c = t0 + 1 + (i.toNat - 1) * (2 + cOp)⌝,
           fun ⟨n', nn', hh', node', _⟩ c => ⌜Valid m ⟨n', nn', hh', node'⟩ (v.set idx.toNat val) ∧
              c = t0 + 2 + st.h_node.toNat * (2 + cOp)⌝,
           fun ⟨_, _, hh', _, i⟩ => (hh' + 1 - i).toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × ℤ›).2.2.2.2 = i at *
    generalize (‹ℤ × ℤ × ℤ × Array M × ℤ›).2.2.2.1 = node' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × ℤ›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × ℤ›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × ℤ›).1 = n' at *)
  all_goals have hpN : st.n_node.toNat ≤ (idx + st.n_node).toNat := by omega
  all_goals have hp2 : (idx + st.n_node).toNat < 2 * st.n_node.toNat := by omega
  case vc2.step.isTrue =>
    obtain ⟨rfl, rfl, rfl, hI, hc⟩ := ‹n' = st.n ∧ _›
    have h2 := hI.2.2.1
    refine ⟨setinv_done m st v hv hN idx h0 hi val node' i hI (by omega), ?_⟩
    have : i.toNat - 1 = st.h_node.toNat := by omega
    rw [this] at hc; omega
  case vc3.step.isFalse =>
    obtain ⟨rfl, rfl, rfl, hI, hc⟩ := ‹n' = st.n ∧ _›
    have h1 := hI.2.1
    refine ⟨⟨rfl, rfl, rfl, setinv_step m _ _ _ hN hpN hp2 _ _ _ _ (by omega) hI (by omega), ?_⟩, ?_⟩
    · have e : (i + 1).toNat - 1 = (i.toNat - 1) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]; omega
    · omega
  case vc4.inr.isTrue.pre =>
    refine ⟨⟨setinv_init m st v hv _ hpN hp2 val hval _ rfl hv.hn, by omega⟩, by simp [fuel]; omega⟩
  case vc5.inr.isTrue.post.success =>
    exact ‹Valid m _ _ ∧ _›
  case vc6.inr.isFalse =>
    omega

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath
variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

/-- The element at a cursor of `rangeDown a b` is `b` minus the length of the prefix. -/
theorem rangeDown_cursor {a b cur : Int} {pref suff : List Int} (h : rangeDown a b = pref ++ cur :: suff) :
    cur = b - pref.length ∧ pref.length < (b - a + 1).toNat := by
  have hl : pref.length < (rangeDown a b).length := by rw [h]; simp
  have e := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl pref.length), Nat.sub_self, List.getElem?_cons_zero] at e
  simp only [rangeDown, List.length_map, List.length_range] at e hl
  rw [List.getElem?_map, List.getElem?_range hl] at e
  simp at e
  exact ⟨by omega, hl⟩

/-- The height loop: `n_node = 2^h_node` is the least power of two `≥ n` reached so far (`0` before the first
iteration). -/
def HInv (n : Nat) (nn hh : Int) : Prop :=
  (hh = 0 ∧ nn = 0) ∨ (1 ≤ hh ∧ 0 ≤ nn ∧ nn.toNat = 2 ^ hh.toNat ∧ (hh = 1 ∨ 2 ^ (hh.toNat - 1) < n) ∧ 0 < n)

theorem hinv_step (n : Nat) (nn hh : Int) (hI : HInv n nn hh) (hlt : nn < n) :
    HInv n (shl 1 (hh + 1)) (hh + 1) := by
  right
  have hpos : 0 ≤ hh := by rcases hI with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hn0 : 0 < n := by rcases hI with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  refine ⟨by omega, ?_, ?_, ?_, hn0⟩
  · simp only [shl]; positivity
  · simp only [shl, one_mul]; rw [Int.toNat_pow_of_nonneg (by norm_num)]; simp
  · rcases hI with ⟨rfl, rfl⟩ | ⟨h1, h2, h3, _⟩
    · left; rfl
    · right; rw [show (hh + 1).toNat - 1 = hh.toNat by omega, ← h3]; omega

theorem hinv_bounds (n : Nat) (nn hh : Int) (hI : HInv n nn hh) :
    (nn = 0 ∧ hh = 0) ∨ (nn.toNat ≤ 2 * n ∧ hh.toNat + 1 ≤ nn.toNat) := by
  rcases hI with h | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h.2, h.1⟩
  · right
    have hlt := Nat.lt_two_pow_self (n := hh.toNat)
    refine ⟨?_, by omega⟩
    rcases h4 with h4 | h4
    · rw [h3, show hh.toNat = 1 by omega]; omega
    · rw [h3, show hh.toNat = (hh.toNat - 1) + 1 by omega, pow_succ]; omega

theorem hinv_le (n : Nat) (hn : n ≤ 2 ^ 29) (nn hh : Int) (hI : HInv n nn hh) (hlt : nn < n) : hh < 29 := by
  rcases hI with ⟨rfl, _⟩ | ⟨h1, h2, h3, _⟩
  · omega
  · by_contra hc
    have : 2 ^ 29 ≤ 2 ^ hh.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
/-- The leaf loop: the first `k0` values are in place, every other node holds `e`. -/
def LeafInv (v : Array M) (e : M) (N k0 : Nat) (node : Array M) : Prop :=
  node.size = 2 * N ∧ ∀ k, k < 2 * N → node[k]! = if N ≤ k ∧ k < N + k0 then v[k - N]! else e

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem leafinv_init (v : Array M) (e : M) (N : Nat) :
    LeafInv v e N 0 (Cpp.replicate ((N : Int) * 2) e) := by
  refine ⟨by simp [replicate]; omega, fun k hk => ?_⟩
  simp only [Nat.add_zero, show ¬ (N ≤ k ∧ k < N) by omega, ite_false]
  rw [getElem!_pos _ _ (by simp [replicate]; omega)]
  simp [replicate]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem leafinv_step (v : Array M) (e : M) (N k0 : Nat) (node : Array M) (hI : LeafInv v e N k0 node)
    (hk : k0 < v.size) (hvN : v.size ≤ N) :
    LeafInv v e N (k0 + 1) (Cpp.set node ((N : Int) + (k0 : Int)) (Cpp.get v (k0 : Int))) := by
  obtain ⟨hsz, hL⟩ := hI
  refine ⟨by simp [hsz], fun k hk2 => ?_⟩
  rw [getElemBang_set _ _ _ _ (by omega), show ((N : Int) + (k0 : Int)).toNat = N + k0 by omega]
  by_cases h : k = N + k0
  · subst h; simp [get_eq]
  · rw [if_neg h, hL k hk2]
    by_cases h2 : N ≤ k ∧ k < N + k0
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- The build loop: the leaves are in place and the inner nodes `j' > j` hold the products of their children. -/
def BuildInv (m : Mon M) (v : Array M) (N j : Nat) (node : Array M) : Prop :=
  node.size = 2 * N ∧ AllV m (fun k => node[k]!) (2 * N) ∧
    (∀ k, N ≤ k → k < 2 * N → node[k]! = if k < N + v.size then v[k - N]! else m.e) ∧
    BInv m (fun k => node[k]!) N j

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem buildinv_init (m : Mon M) (v : Array M) (hV : ∀ x ∈ v.toList, m.V x) (N : Nat) (hvN : v.size ≤ N)
    (node : Array M) (hI : LeafInv v m.e N v.size node) : BuildInv m v N (N - 1) node := by
  obtain ⟨hsz, hL⟩ := hI
  refine ⟨hsz, fun k hk => ?_, fun k h1 h2 => ?_, binv_init m _ N⟩
  · show m.V node[k]!
    rw [hL k hk]
    split
    · apply hV; rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      simp only [Array.getElem?_eq_getElem (show k - N < v.size by omega), Option.getD_some]
      exact Array.getElem_mem_toList _
    · exact m.he
  · rw [hL k h2]
    by_cases h : k < N + v.size
    · rw [if_pos ⟨h1, h⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]

omit [Cpp.StaticCall "e" M M] in
theorem buildinv_step (m : Mon M) (v : Array M) (N j : Nat) (node : Array M) (hI : BuildInv m v N j node)
    (hj1 : 1 ≤ j) (hjN : j < N) :
    BuildInv m v N (j - 1) (Cpp.set node (j : Int) (m.op (Cpp.get node ((j : Int) * 2)) (Cpp.get node ((j : Int) * 2 + 1)))) := by
  obtain ⟨hsz, hV, hL, hB⟩ := hI
  simp only [get_eq, show ((j : Int) * 2).toNat = 2 * j by omega, show ((j : Int) * 2 + 1).toNat = 2 * j + 1 by omega]
  have hF := fun_set node (j : Int) (m.op node[2 * j]! node[2 * j + 1]!) (by simp; omega)
  try simp only [Int.toNat_natCast] at hF
  unfold BuildInv
  rw [hF]
  refine ⟨by simp [hsz], fun k hk => ?_, fun k h1 h2 => ?_, binv_step m _ N j hB hj1⟩
  · simp only [upd]; split
    · exact m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
    · exact hV k hk
  · rw [getElemBang_set _ _ _ _ (by simp; omega), if_neg (by simp; omega)]; exact hL k h1 h2

omit [Cpp.StaticCall "e" M M] in
theorem buildinv_done (m : Mon M) (v : Array M) (n nn hh : Int) (hn : n = v.size) (hH : HInv v.size nn hh)
    (hge : ¬ nn < n) (node : Array M) (hI : BuildInv m v nn.toNat 0 node) :
    Valid m ⟨n, nn, hh, node⟩ v.toList := by
  obtain ⟨hsz, hV, hL, hB⟩ := hI
  have hnn : 0 ≤ nn := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  refine ⟨by simpa using hn, hnn, by dsimp only; rcases hH with ⟨h, _⟩ | ⟨h, _⟩ <;> omega, ?_, hsz, hV,
    binv_end m _ _ hB, ?_, ?_⟩
  · rcases hH with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left; refine ⟨?_, h2, h1⟩
      have : v.size = 0 := by omega
      simpa using this
    · right; exact ⟨h3, h1, by simp; omega, by simpa using h4.1⟩
  · intro i hi
    simp only [Array.length_toList] at hi
    dsimp only
    rw [hL _ (by omega) (by omega), if_pos (by omega), show nn.toNat + i - nn.toNat = i by omega]
    simp [Array.getElem!_eq_getD, hi]
  · intro i h1 h2
    simp only [Array.length_toList] at h1
    dsimp only at h2 ⊢
    rw [hL _ (by omega) (by omega), if_neg (by omega)]

omit [Cpp.StaticCall "e" M M] in
theorem buildinv_step_int (m : Mon M) (v : Array M) (NN : Int) (hNN : 0 ≤ NN) (k : Nat) (node : Array M)
    (hI : BuildInv m v NN.toNat (NN.toNat - 1 - k) node) (hk : k < (NN - 1 - 1 + 1).toNat) :
    BuildInv m v NN.toNat (NN.toNat - 1 - (k + 1))
      (Cpp.set node (NN - 1 - k) (m.op (Cpp.get node ((NN - 1 - k) * 2)) (Cpp.get node ((NN - 1 - k) * 2 + 1)))) := by
  have hj := buildinv_step m v NN.toNat (NN.toNat - 1 - k) node hI (by omega) (by omega)
  rw [show ((NN.toNat - 1 - k : Nat) : Int) = NN - 1 - k by omega,
    show NN.toNat - 1 - k - 1 = NN.toNat - 1 - (k + 1) by omega] at hj
  exact hj

theorem cost_step (s a k c : Nat) (h : s = a + k * (2 + c)) : s + 1 + 1 + c = a + (k + 1) * (2 + c) := by
  rw [h, Nat.add_mul, Nat.one_mul]; omega

theorem init_vec_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (v : Array M) (hV : ∀ x ∈ v.toList, m.V x)
    (hsmall : v.size ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.init_vec v
    ⦃⇓ st c => ⌜Valid m st v.toList ∧ c ≤ t0 + 3 + cE + (11 + 2 * cOp) * v.size⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hU : ∀ (st : cp.SegmentTree M) (i : Int) {Q : PostCond (cp.SegmentTree M) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.SegmentTree.update st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.SegmentTree.update, hOp]
  mvcgen [cp.SegmentTree.init_vec, hE, hU]
  case vc1.inv =>
    exact ⟨fun ⟨nn, hh⟩ c => ⌜HInv v.size nn hh ∧ hh ≤ 29 ∧ c = t0 + 1 + hh.toNat⌝,
           fun ⟨nn, hh⟩ c => ⌜HInv v.size nn hh ∧ hh ≤ 29 ∧ v.size ≤ nn ∧ c = t0 + 2 + hh.toNat⌝,
           fun ⟨_, hh⟩ => (30 - hh).toNat⟩
  case inv1 =>
    rename_i s1 h1 n r nn hh s h t2 node
    exact ⇓⟨xs, node'⟩ c => ⌜LeafInv v m.e r.1.toNat xs.prefix.length node' ∧
      c = s + cE + 2 * r.1.toNat + xs.prefix.length⌝
  case inv2 =>
    rename_i s2 h2 n r1 nn hh s1 h1 t2 node r s h
    exact ⇓⟨xs, n', nn', hh', node'⟩ c => ⌜n' = v.size ∧ nn' = r1.1 ∧ hh' = r1.2 ∧
      BuildInv m v r1.1.toNat (r1.1.toNat - 1 - xs.prefix.length) node' ∧
      c = s1 + cE + 2 * r1.1.toNat + v.size + xs.prefix.length * (2 + cOp)⌝
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    obtain ⟨hI, hle, hc⟩ := ‹HInv _ _ _ ∧ _›
    exact ⟨hI, hle, by simpa [size] using ‹size v ≤ _›, by omega⟩
  case vc3.step.isFalse =>
    obtain ⟨hI, hle, hc⟩ := ‹HInv _ _ _ ∧ _›
    have hlt : (‹ℤ × ℤ›).1 < (v.size : Int) := by simpa [size] using ‹_ < size v›
    have h29 := hinv_le v.size hsmall _ _ hI hlt
    have h0 : 0 ≤ (‹ℤ × ℤ›).2 := by rcases hI with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact ⟨⟨hinv_step _ _ _ hI hlt, by omega, by omega⟩, by omega⟩
  case vc4.pre =>
    exact ⟨⟨Or.inl ⟨rfl, rfl⟩, ‹_ = _›⟩, by simp [fuel]⟩
  case vc5.step =>
    have e := range_cursor ‹range _ _ = _ ++ _ :: _›
    have hl := range_prefix_length ‹range _ _ = _ ++ _ :: _›
    simp +zetaDelta [size] at hl e
    obtain ⟨hI, hc⟩ := ‹LeafInv _ _ _ _ _ ∧ _›
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    have h0 : 0 ≤ (‹ℤ × ℤ›).1 := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    subst e
    have := leafinv_step v m.e _ _ _ hI hl (by omega)
    rw [Int.toNat_of_nonneg h0] at this
    exact ⟨this, by omega⟩
  case vc6.post.success.pre =>
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    have h0 : 0 ≤ (‹ℤ × ℤ›).1 := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have := leafinv_init v m.e (‹ℤ × ℤ›).1.toNat
    rw [Int.toNat_of_nonneg h0] at this
    exact ⟨this, by omega⟩
  case vc7.step =>
    obtain ⟨e, hl⟩ := rangeDown_cursor ‹rangeDown _ _ = _ ++ _ :: _›
    obtain ⟨hn1, hn2, hn3, hI, hc⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _ ∧ BuildInv _ _ _ _ _ ∧ _›
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    have h0 : 0 ≤ (‹ℤ × ℤ›).1 := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    subst e
    exact ⟨hn1, hn2, hn3, buildinv_step_int m v _ h0 _ _ hI hl, cost_step _ _ _ _ hc⟩
  case vc8.post.success.post.success.pre =>
    obtain ⟨hI, hc⟩ := ‹LeafInv _ _ _ _ _ ∧ _›
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    simp [range, size] at hI hc
    exact ⟨by simp [size], buildinv_init m v (fun x hx => hV x (by simpa using hx)) _ (by omega) _ hI, hc⟩
  case vc9.post.success.post.success.post.success =>
    obtain ⟨hn1, hn2, hn3, hI, hc⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _ ∧ BuildInv _ _ _ _ _ ∧ _›
    obtain ⟨hH, -, hvN, hc1⟩ := ‹HInv _ _ _ ∧ _›
    simp [rangeDown] at hI hc
    refine ⟨?_, ?_⟩
    · rw [← hn2, ← hn3] at hH
      rw [← hn2] at hvN hI
      exact buildinv_done m v _ _ _ hn1 hH (by omega) _ hI
    · rcases hinv_bounds _ _ _ hH with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hc hvN; rw [h2] at hc1; simp at hc hc1 hvN; omega
      · have hm : ((‹ℤ × ℤ›).1.toNat - 1) * (2 + cOp) ≤ (2 * v.size) * (2 + cOp) :=
          Nat.mul_le_mul_right _ (by omega)
        have e1 : (2 * v.size) * (2 + cOp) = 4 * v.size + 2 * (cOp * v.size) := by ring
        have e2 : (11 + 2 * cOp) * v.size = 11 * v.size + 2 * (cOp * v.size) := by ring
        rw [e2]; omega

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath
variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

theorem init_int_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (n_ : Int) (h0 : 0 ≤ n_)
    (hs : n_ ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.init_int n_
    ⦃⇓ st c => ⌜Valid m st (List.replicate n_.toNat m.e) ∧
      c ≤ t0 + 4 + 2 * cE + (12 + 2 * cOp) * n_.toNat⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hB := init_vec_spec m cE cOp hO
  mvcgen [cp.SegmentTree.init_int, hE, hB]
  all_goals simp +zetaDelta at *
  case vc1.hV =>
    intro x hx
    simp [replicate] at hx
    rw [hx.2]; exact m.he
  case vc2.hsmall => simp [replicate]; omega
  case vc3.post.success =>
    obtain ⟨hv, hc⟩ := ‹Valid _ _ _ ∧ _›
    refine ⟨by simpa [replicate] using hv, ?_⟩
    simp [replicate] at hc
    have : (12 + 2 * cOp) * n_.toNat = n_.toNat + (11 + 2 * cOp) * n_.toNat := by ring
    omega

theorem init_0_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.init_0 (M := M)
    ⦃⇓ st c => ⌜Valid m st [] ∧ c ≤ t0 + 5 + 2 * cE⌝⦄ := by
  have hB := init_int_spec m cE cOp hO
  mvcgen [cp.SegmentTree.init_0, hB]
  all_goals simp +zetaDelta at *
  obtain ⟨hv, hc⟩ := ‹Valid _ _ _ ∧ _›
  exact ⟨hv, by omega⟩

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath
variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

theorem mod_two (x : Int) (hx : 0 ≤ x) : Cpp.mod x 2 = x % 2 := by
  simp [Cpp.mod]; exact Int.tmod_eq_emod_of_nonneg hx

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem climb_int (m : Mon M) (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (p : M → Bool) (S : Nat) (x : Int)
    (sm : M) (t : Nat) (hx : 0 ≤ x) (hev : Cpp.mod x 2 = 0) (hI : RInv m a N p S x.toNat sm t) :
    0 ≤ shr x 1 ∧ shr x 1 < x ∧ RInv m a N p S (shr x 1).toNat sm (t + 1) ∧
      (shr x 1).toNat * 2 ^ (t + 1) = x.toNat * 2 ^ t := by
  rw [mod_two x hx] at hev
  have h1 := hI.1
  have := rinv_climb m a N h hN p S x.toNat sm t hI (by omega)
  rw [shr_one, show (x / 2).toNat = x.toNat / 2 by omega]
  refine ⟨by omega, by omega, this, ?_⟩
  rw [pow_succ]; have : x.toNat = 2 * (x.toNat / 2) := by omega
  conv_rhs => rw [this]
  ring

theorem odd_of_not_mod (x : Int) (hx : 0 ≤ x) (h : ¬ Cpp.mod x 2 = 0) : x.toNat % 2 = 1 := by
  rw [mod_two x hx] at h; omega

theorem even_of_mod (x : Int) (hx : 0 ≤ x) (h : Cpp.mod x 2 = 0) : x.toNat % 2 = 0 := by
  rw [mod_two x hx] at h; omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem rinv_height (m : Mon M) (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (p : M → Bool) (S x : Nat) (sm : M)
    (t : Nat) (hI : RInv m a N p S x sm t) : t = h - Nat.log2 x := by
  obtain ⟨h1, h2, h3, -⟩ := hI
  have hp := Nat.two_pow_pos t
  exact height_eq N h x t hN h1 h2 (by nlinarith)

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem rinv_bound (m : Mon M) (a : Nat → M) (N : Nat) (p : M → Bool) (S x : Nat) (sm : M)
    (t : Nat) (hI : RInv m a N p S x sm t) : x < 2 * N := by
  obtain ⟨h1, h2, h3, -⟩ := hI
  have hp := Nat.two_pow_pos t
  nlinarith

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem dinv_v (m : Mon M) (a : Nat → M) (N : Nat) (p : M → Bool) (S x : Nat) (sm : M)
    (t : Nat) (hI : DInv m a N p S x sm t) : m.V sm := hI.1.2.2.2.2.1

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem descent_int (m : Mon M) (node : Array M) (N : Nat) (hV : AllV m (fun i => node[i]!) (2 * N))
    (hT : TInv m (fun i => node[i]!) N) (p : M → Bool) (S : Nat) (ld : Int) (smd : M) (t : Nat) (hd0 : 0 ≤ ld)
    (hlt : ld < N) (hD : DInv m (fun i => node[i]!) N p S ld.toNat smd t) :
    ∃ t', t = t' + 1 ∧
      (p (m.op smd (Cpp.get node (ld * 2))) = true →
        DInv m (fun i => node[i]!) N p S (ld * 2 + 1).toNat (m.op smd (Cpp.get node (ld * 2))) t') ∧
      (p (m.op smd (Cpp.get node (ld * 2))) = false → DInv m (fun i => node[i]!) N p S (ld * 2).toNat smd t') := by
  obtain ⟨t', ht, h1, h2⟩ := dinv_step m (fun i => node[i]!) N hV hT p S ld.toNat smd t hD (by omega)
  refine ⟨t', ht, fun h => ?_, fun h => ?_⟩
  · rw [get_eq, show (ld * 2).toNat = 2 * ld.toNat by omega] at h ⊢
    rw [show (ld * 2 + 1).toNat = 2 * ld.toNat + 1 by omega]
    exact h1 h
  · rw [get_eq, show (ld * 2).toNat = 2 * ld.toNat by omega] at h
    rw [show (ld * 2).toNat = 2 * ld.toNat by omega]
    exact h2 h

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
/-- A failing step of the search never ends inside the padding: there the leaf is `e`. -/
theorem pad_contra (m : Mon M) (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (p : M → Bool) (S x : Nat)
    (hS : st.n_node.toNat ≤ S) (hSx : S ≤ x) (hx2 : x < 2 * st.n_node.toNat)
    (h1 : p (rf m (fun i => st.node[i]!) S (x - S)) = true)
    (h2 : p (rf m (fun i => st.node[i]!) S (x + 1 - S)) = false) : x < st.n_node.toNat + v.length := by
  by_contra hc
  have hpad := hv.pad (x - st.n_node.toNat) (by omega) (by omega)
  rw [show st.n_node.toNat + (x - st.n_node.toNat) = x by omega] at hpad
  have e : x + 1 - S = (x - S) + 1 := by omega
  rw [e, rf_add m _ _ hv.allV _ _ _ (by omega), show S + (x - S) = x by omega, rf_one m _ _ (by
    show m.V st.node[x]!; rw [hpad]; exact m.he)] at h2
  rw [hpad, m.rid _ (rf_V m _ _ hv.allV _ _ (by omega))] at h2
  rw [h1] at h2; exact absurd h2 (by decide)

theorem measure_dec (N h x t Y : Nat) (hb : (x + 1 + 1) * 2 ^ t ≤ 2 * N) (h1 : t = h - Nat.log2 (x + 1))
    (hL : x * 2 ^ t = Y) : 2 * N - (x + 1) * 2 ^ (h - Nat.log2 (x + 1)) < 2 * N - Y := by
  rw [← h1, ← hL]
  have hp := Nat.two_pow_pos t
  have e1 : (x + 1) * 2 ^ t = x * 2 ^ t + 2 ^ t := by ring
  have e2 : (x + 1 + 1) * 2 ^ t = x * 2 ^ t + 2 ^ t + 2 ^ t := by ring
  omega

theorem toNat_succ (x : Int) (hx : 0 ≤ x) : (x + 1).toNat = x.toNat + 1 := by omega

theorem pow_cond (r : Int) (hr : 0 ≤ r) :
    Cpp.land (r + 1) (-1 + -r) = r + 1 ↔ ∃ k, r.toNat + 1 = 2 ^ k := by
  have e : -1 + -r = -(r + 1) := by ring
  rw [e, land_neg (r + 1) (by omega), show (r + 1).toNat = r.toNat + 1 by omega]
  rw [← lowb_eq_self_iff (r.toNat + 1) (by omega)]
  omega

theorem search_right_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) {F : Type} [Cpp.Invoke1 F M Bool]
    (p : M → Bool) (cF : Nat) (f : F)
    (hF : ∀ x, ∀ {Q : PostCond Bool PS}, ⦃fun t => Q.1 (p x) (t + cF)⦄
      (Cpp.Invoke1.call (A := M) (R := Bool) f x) ⦃Q⦄)
    (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (hsmall : v.length ≤ 2 ^ 29)
    (l : Int) (h0 : 0 ≤ l) (hl : l ≤ v.length) (hpe : p m.e = true) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.search_prod_right st l f
    ⦃⇓ r c => ⌜l ≤ r.1 ∧ r.1 ≤ v.length ∧ p (rf m (fun i => v[i]!) l.toNat (r.1 - l).toNat) = true ∧
      (r.1 = v.length ∨ p (rf m (fun i => v[i]!) l.toNat (r.1 + 1 - l).toNat) = false) ∧ r.2 = st ∧
      c ≤ t0 + 4 + 2 * cE + 2 * cF + cOp + (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF)⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hht := height_le m st v hv hsmall
  set a : Nat → M := fun i => st.node[i]! with ha
  set N := st.n_node.toNat with hNdef
  set h := st.h_node.toNat with hhdef
  set S := (l + st.n_node).toNat with hSdef
  set B := t0 + 1 + 2 * cE + cF with hB
  set D := 2 + 2 * cOp + cF with hD
  set E := 1 + 2 * cOp + cF with hEc
  have hshape : N = 2 ^ h ∧ 1 ≤ st.h_node ∧ v.length ≤ N ∨ v = [] := by
    rcases hv.shape with ⟨h1, -⟩ | ⟨h1, h2, h3, -⟩
    · exact Or.inr h1
    · exact Or.inl ⟨h1, h2, h3⟩
  mvcgen [cp.SegmentTree.search_prod_right, hE, hOp, hF]
  case vc2.inv =>
    exact ⟨fun ⟨ret, l', sm⟩ c => ⌜ret = none ∧ 0 ≤ l' ∧ ∃ t k, RInv m a N p S l'.toNat sm t ∧
              k ≤ t + (if l'.toNat % 2 = 0 then 1 else 0) ∧ c ≤ B + D * k + t⌝,
           fun ⟨ret, _, _⟩ c => ⌜match ret with
              | some r => ∃ x : Nat, r = ((x : Int) - st.n_node, st) ∧ S ≤ x ∧ x < 2 * N ∧
                  p (rf m a S (x - S)) = true ∧ p (rf m a S (x + 1 - S)) = false ∧
                  c ≤ B + D * h + h + 3 + cOp + cF + h * E
              | none => p (rf m a S (2 * N - S)) = true ∧ c ≤ B + D * (h + 1) + h⌝,
           fun ⟨_, l', _⟩ => 2 * N - l'.toNat * 2 ^ (h - Nat.log2 l'.toNat)⟩
  case vc3.inv =>
    rename_i b _s1 _l1 _sm1 _c1 _h1
    exact ⟨fun l'' c => ⌜0 ≤ l'' ∧ l'' ≤ b.2.1 ∧ ∃ t k, RInv m a N p S l''.toNat b.2.2 t ∧
              l''.toNat * 2 ^ t = b.2.1.toNat * 2 ^ (h - Nat.log2 b.2.1.toNat) ∧
              (if l'' = b.2.1 then k ≤ t + (if b.2.1.toNat % 2 = 0 then 1 else 0) else k ≤ t) ∧
              c ≤ B + D * k + t + 1⌝,
           fun l'' c => ⌜0 ≤ l'' ∧ l''.toNat % 2 = 1 ∧ ∃ t k, RInv m a N p S l''.toNat b.2.2 t ∧
              l''.toNat * 2 ^ t = b.2.1.toNat * 2 ^ (h - Nat.log2 b.2.1.toNat) ∧ k ≤ t ∧
              c ≤ B + D * k + t + 2⌝,
           fun l'' => l''.toNat⟩
  case vc7.inv =>
    exact ⟨fun ⟨ld, smd⟩ c => ⌜0 ≤ ld ∧ ∃ t, DInv m a N p S ld.toNat smd t ∧ t ≤ h ∧
              c + t * E ≤ B + D * h + h + 2 + cOp + cF + h * E⌝,
           fun ⟨ld, smd⟩ c => ⌜0 ≤ ld ∧ N ≤ ld.toNat ∧ DInv m a N p S ld.toNat smd 0 ∧
              c ≤ B + D * h + h + 3 + cOp + cF + h * E⌝,
           fun ⟨ld, _⟩ => 2 * N - ld.toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹Option (ℤ × cp.SegmentTree M) × ℤ × M›).2.2 = smo at *
    generalize (‹Option (ℤ × cp.SegmentTree M) × ℤ × M›).2.1 = lo at *)
  case vc1.isTrue.isTrue.isTrue =>
    subst ‹l = st.n›
    refine ⟨le_refl _, by omega, by simp [rf]; exact hpe, Or.inl (by omega), ?_⟩
    generalize (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) = X
    omega
  case vc4.step.isTrue =>
    obtain ⟨hx0, hxle, t, hR, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    have hodd := odd_of_not_mod _ hx0 ‹_›
    refine ⟨hx0, hodd, t, hR, hL, k, ?_, by omega⟩
    split at hk
    · rename_i heq; rw [← heq] at hk; simp [hodd] at hk; exact hk
    · exact hk
  case vc5.step.isFalse =>
    obtain ⟨hx0, hxle, t, hR, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    obtain ⟨c0, c1, c2, c3⟩ := climb_int m _ _ _ hN p _ _ _ _ hx0 ‹_› hR
    refine ⟨⟨c0, by omega, t + 1, c2, by rw [c3, hL], k, ?_, by omega⟩, c1, by omega⟩
    rw [if_neg (by omega)]
    split at hk
    · rename_i heq; rw [← heq] at hk
      have := even_of_mod _ hx0 ‹_›
      simp [this] at hk; omega
    · omega
  case vc6.step.pre =>
    obtain ⟨-, hl0, t, hR, k, hk, hc⟩ := ‹_ = none ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hb := rinv_bound m _ _ p _ _ _ _ hR
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨⟨hl0, t, hR, by rw [← rinv_height m _ _ _ hN p _ _ _ _ hR]; simp, k, by simpa using hk, by omega⟩, ?_⟩
    simp [fuel]; omega
  case vc8.step.isTrue =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = ld at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DInv _ _ _ _ _ _ _ t ∧ _›
    have ht0 := dinv_exit m _ _ p _ _ _ _ hD (by omega)
    subst ht0
    exact ⟨hd0, Or.inl (by omega), hD, by omega⟩
  case vc9.step.isFalse.isTrue =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = ld at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DInv _ _ _ _ _ _ _ t ∧ _›
    obtain ⟨t', rfl, h1, -⟩ := descent_int m st.node _ hv.allV hv.tree p _ ld smd _ hd0 (by omega) hD
    refine ⟨⟨by omega, t', h1 ‹_›, by omega, ?_⟩, by omega⟩
    have : (t' + 1) * (1 + 2 * cOp + cF) = t' * (1 + 2 * cOp + cF) + (1 + 2 * cOp + cF) := by ring
    omega
  case vc10.step.isFalse.isFalse =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = ld at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DInv _ _ _ _ _ _ _ t ∧ _›
    have h1l := hD.1.1
    obtain ⟨t', rfl, -, h2⟩ := descent_int m st.node _ hv.allV hv.tree p _ ld smd _ hd0 (by omega) hD
    refine ⟨⟨by omega, t', h2 ‹_›, by omega, ?_⟩, by omega⟩
    have : (t' + 1) * (1 + 2 * cOp + cF) = t' * (1 + 2 * cOp + cF) + (1 + 2 * cOp + cF) := by ring
    omega
  case vc11.step.post.success.isTrue.pre =>
    obtain ⟨hr0, hodd, t, hR, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have ht := t_le _ _ _ _ hN hR.1 hR.2.2.1
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb := rinv_bound m _ _ p _ _ _ _ hR
    refine ⟨⟨hr0, t, ⟨hR, by rw [get_eq] at *; assumption⟩, by omega, ?_⟩, by simp [fuel]; omega⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have m2 : t * (1 + 2 * cOp + cF) ≤ st.h_node.toNat * (1 + 2 * cOp + cF) := Nat.mul_le_mul_right _ ht
    omega
  case vc12.step.post.success.isTrue.post.success =>
    obtain ⟨hd0, -, hD, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ∧ DInv _ _ _ _ _ _ _ 0 ∧ _›
    have hop := rinv_op m _ _ hv.allV hv.tree p _ _ _ _ hD.1
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hD
    simp at h2 h3 h4 h6 hop
    refine ⟨(‹ℤ × M›).1.toNat, by omega, by omega, by omega, by rw [← h6]; exact h7, by rw [← hop]; exact h8, ?_⟩
    omega
  case vc13.step.post.success.isFalse.isTrue =>
    obtain ⟨hr0, hodd, t, hR, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hpow := (pow_cond _ hr0).mp ‹_›
    have ht := t_le _ _ _ _ hN hR.1 hR.2.2.1
    rw [get_eq] at *
    obtain ⟨-, hend⟩ := rinv_end m _ _ _ hN hv.allV hv.tree p _ _ _ _ hR ‹_› hpow
    refine ⟨hend, ?_⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have : (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) = (2 + 2 * cOp + cF) * st.h_node.toNat + (2 + 2 * cOp + cF) := by ring
    omega
  case vc14.step.post.success.isFalse.isFalse =>
    obtain ⟨hr0, hodd, t, hR, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hpow : ¬ ∃ k, _ = 2 ^ k := fun h => ‹¬ _› ((pow_cond _ hr0).mpr h)
    rw [get_eq] at *
    have hR' := rinv_next m _ _ _ hN hv.allV hv.tree p _ _ _ _ hR ‹_› hpow
    rw [toNat_succ _ hr0]
    refine ⟨⟨by omega, t, hR', k + 1, by rw [if_pos (by omega)]; omega, ?_⟩, ?_⟩
    · have : (2 + 2 * cOp + cF) * (k + 1) = (2 + 2 * cOp + cF) * k + (2 + 2 * cOp + cF) := by ring
      omega
    · exact measure_dec _ _ _ _ _ hR'.2.2.1 (rinv_height m _ _ _ hN p _ _ _ _ hR') hL
  case vc15.isTrue.isTrue.isFalse.pre =>
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hS1 : st.n_node.toNat ≤ (l + st.n_node).toNat := by omega
    have hS2 : (l + st.n_node).toNat < 2 * st.n_node.toNat := by omega
    have hR := rinv_init m (fun i => st.node[i]!) _ p _ hS1 hS2 hpe
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨⟨by omega, 0, hR, 0, by simp, by omega⟩, ?_⟩
    simp [fuel]; omega
  case vc16.isTrue.isTrue.isFalse.post.success.h_1 =>
    simp only [‹_ = some _›] at *
    obtain ⟨x, hx, hS, hx2, hp1, hp2, hc⟩ := ‹∃ x : Nat, _ = _ ∧ _›
    subst hx
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hlt := pad_contra m st v hv p _ x (by omega) (by omega) hx2 hp1 hp2
    have e1 : x - (l + st.n_node).toNat = ((x : Int) - st.n_node - l).toNat := by omega
    have e2 : x + 1 - (l + st.n_node).toNat = ((x : Int) - st.n_node + 1 - l).toNat := by omega
    have eS : (l + st.n_node).toNat = st.n_node.toNat + l.toNat := by omega
    rw [e1, eS, leaves_rf m st v hv _ _ (by omega)] at hp1
    rw [e2, eS, leaves_rf m st v hv _ _ (by omega)] at hp2
    refine ⟨by omega, by omega, by simpa using hp1, Or.inr (by simpa using hp2), rfl, ?_⟩
    have : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * st.h_node.toNat + st.h_node.toNat + st.h_node.toNat * (1 + 2 * cOp + cF) +
          (4 + 4 * cOp + 2 * cF) := by ring
    omega
  case vc17.isTrue.isTrue.isFalse.post.success.h_2 =>
    simp only [‹_ = none›] at *
    obtain ⟨hp1, hc⟩ := ‹p _ = true ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hpad := rf_pad m _ st.n_node.toNat v.length (l + st.n_node).toNat hv.allV hle (by omega) (by omega) hv.pad
    rw [hpad, show st.n_node.toNat + v.length - (l + st.n_node).toNat = (st.n - l).toNat by omega,
      show (l + st.n_node).toNat = st.n_node.toNat + l.toNat by omega,
      leaves_rf m st v hv _ _ (by omega)] at hp1
    refine ⟨by omega, by omega, by simpa using hp1, Or.inl (by omega), ?_⟩
    have e : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) + (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := by ring
    have : st.h_node.toNat + 1 ≤ (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  case vc19.isFalse =>
    omega

end Proofs.Cpp.SegmentTree

namespace Proofs.Cpp.SegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath
variable {M : Type} [Inhabited M] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem linv_height (m : Mon M) (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (p : M → Bool) (R x : Nat) (sm : M)
    (t : Nat) (hI : LInv m a N p R x sm t) : t = h - Nat.log2 x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hI
  have hp := Nat.two_pow_pos t
  exact height_eq N h x t hN h1 h2 (by nlinarith)

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem climb_left_int (m : Mon M) (a : Nat → M) (N h : Nat) (hN : N = 2 ^ h) (p : M → Bool) (R : Nat) (x : Int)
    (sm : M) (t : Nat) (h1 : 1 < x) (hodd : ¬ Cpp.mod x 2 = 0) (hI : LInv m a N p R x.toNat sm t) :
    1 ≤ shr x 1 ∧ shr x 1 < x ∧ LInv m a N p R (shr x 1).toNat sm (t + 1) ∧
      ((shr x 1).toNat + 1) * 2 ^ (t + 1) = (x.toNat + 1) * 2 ^ t := by
  rw [mod_two x (by omega)] at hodd
  have := linv_climb m a N h hN p R x.toNat sm t hI (by omega) (by omega)
  rw [shr_one, show (x / 2).toNat = x.toNat / 2 by omega]
  refine ⟨by omega, by omega, this, ?_⟩
  rw [pow_succ]; have : x.toNat + 1 = 2 * (x.toNat / 2 + 1) := by omega
  rw [this]; ring

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] in
theorem descent_left_int (m : Mon M) (node : Array M) (N : Nat) (hV : AllV m (fun i => node[i]!) (2 * N))
    (hT : TInv m (fun i => node[i]!) N) (p : M → Bool) (R : Nat) (xd : Int) (smd : M) (t : Nat) (hd0 : 0 ≤ xd)
    (hlt : xd < N) (hD : DLInv m (fun i => node[i]!) N p R xd.toNat smd t) :
    ∃ t', t = t' + 1 ∧
      (p (m.op (Cpp.get node (xd * 2 + 1)) smd) = true →
        DLInv m (fun i => node[i]!) N p R (xd * 2).toNat (m.op (Cpp.get node (xd * 2 + 1)) smd) t') ∧
      (p (m.op (Cpp.get node (xd * 2 + 1)) smd) = false →
        DLInv m (fun i => node[i]!) N p R (xd * 2 + 1).toNat smd t') := by
  obtain ⟨t', ht, h1, h2⟩ := dlinv_step m (fun i => node[i]!) N hV hT p R xd.toNat smd t hD (by omega)
  refine ⟨t', ht, fun hh => ?_, fun hh => ?_⟩
  · rw [get_eq, show (xd * 2 + 1).toNat = 2 * xd.toNat + 1 by omega] at hh ⊢
    rw [show (xd * 2).toNat = 2 * xd.toNat by omega]
    exact h1 hh
  · rw [get_eq, show (xd * 2 + 1).toNat = 2 * xd.toNat + 1 by omega] at hh
    rw [show (xd * 2 + 1).toNat = 2 * xd.toNat + 1 by omega]
    exact h2 hh

theorem pow_cond_left (x : Int) (hx : 0 < x) : Cpp.land x (-x) = x ↔ ∃ k, x.toNat = 2 ^ k := by
  rw [land_neg x hx, ← lowb_eq_self_iff x.toNat (by omega)]
  omega

theorem measure_dec_left (N h x t Y : Nat) (hx : 2 ≤ x) (h1 : t = h - Nat.log2 (x - 1))
    (hL : (x + 1) * 2 ^ t = Y) : x * 2 ^ (h - Nat.log2 (x - 1)) < Y := by
  rw [← h1, ← hL]
  have hp := Nat.two_pow_pos t
  have e1 : (x + 1) * 2 ^ t = x * 2 ^ t + 2 ^ t := by ring
  omega

theorem stop_of (x : Int) (hx1 : 1 ≤ x) (h : x ≤ 1 ∨ Cpp.mod x 2 = 0) : ¬ (1 < x.toNat ∧ x.toNat % 2 = 1) := by
  rcases h with h | h
  · omega
  · rw [mod_two _ (by omega)] at h; omega

theorem three_le_of (x : Int) (hx1 : 1 ≤ x) (hpow : ¬ ∃ k, x.toNat = 2 ^ k) (hev : 1 < x → x.toNat % 2 = 0) :
    3 ≤ x.toNat ∧ x.toNat % 2 = 0 := by
  have h1 : x.toNat ≠ 1 := fun h => hpow ⟨0, by simp [h]⟩
  have h2 : x.toNat ≠ 2 := fun h => hpow ⟨1, by simp [h]⟩
  have := hev (by omega)
  omega

theorem search_left_spec (m : Mon M) (cE cOp : Nat) (hO : Ops m cE cOp) {F : Type} [Cpp.Invoke1 F M Bool]
    (p : M → Bool) (cF : Nat) (f : F)
    (hF : ∀ x, ∀ {Q : PostCond Bool PS}, ⦃fun t => Q.1 (p x) (t + cF)⦄
      (Cpp.Invoke1.call (A := M) (R := Bool) f x) ⦃Q⦄)
    (st : cp.SegmentTree M) (v : List M) (hv : Valid m st v) (hsmall : v.length ≤ 2 ^ 29)
    (r : Int) (h0 : 0 ≤ r) (hr : r ≤ v.length) (hpe : p m.e = true) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTree.search_prod_left st r f
    ⦃⇓ res c => ⌜0 ≤ res.1 ∧ res.1 ≤ r ∧ p (rf m (fun i => v[i]!) res.1.toNat (r - res.1).toNat) = true ∧
      (res.1 = 0 ∨ p (rf m (fun i => v[i]!) (res.1 - 1).toNat (r - res.1 + 1).toNat) = false) ∧ res.2 = st ∧
      c ≤ t0 + 4 + 2 * cE + 2 * cF + cOp + (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF)⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hht := height_le m st v hv hsmall
  set a : Nat → M := fun i => st.node[i]! with ha
  set N := st.n_node.toNat with hNdef
  set h := st.h_node.toNat with hhdef
  set R := (r + st.n_node).toNat with hRdef
  set B := t0 + 1 + 2 * cE + cF with hB
  set D := 2 + 2 * cOp + cF with hD
  set E := 1 + 2 * cOp + cF with hEc
  have hshape : N = 2 ^ h ∧ 1 ≤ st.h_node ∧ v.length ≤ N ∨ v = [] := by
    rcases hv.shape with ⟨h1, -⟩ | ⟨h1, h2, h3, -⟩
    · exact Or.inr h1
    · exact Or.inl ⟨h1, h2, h3⟩
  mvcgen [cp.SegmentTree.search_prod_left, hE, hOp, hF]
  case vc2.inv =>
    exact ⟨fun ⟨ret, rr, sm⟩ c => ⌜ret = none ∧ 1 ≤ rr ∧ ∃ t k, LInv m a N p R (rr.toNat - 1) sm t ∧
              k ≤ t + (if (rr.toNat - 1) % 2 = 1 ∧ 1 < rr.toNat - 1 then 1 else 0) ∧ c ≤ B + D * k + t⌝,
           fun ⟨ret, _, _⟩ c => ⌜match ret with
              | some res => ∃ x : Nat, res = ((x : Int) + 1 - st.n_node, st) ∧ N ≤ x ∧ x < R ∧
                  p (rf m a (x + 1) (R - (x + 1))) = true ∧ p (rf m a x (R - x)) = false ∧
                  c ≤ B + D * h + h + 3 + cOp + cF + h * E
              | none => p (rf m a N (R - N)) = true ∧ c ≤ B + D * (h + 1) + h⌝,
           fun ⟨_, rr, _⟩ => rr.toNat * 2 ^ (h - Nat.log2 (rr.toNat - 1))⟩
  case vc3.inv =>
    rename_i b _s1 _r1 _sm1 _c1 _h1 _rd
    exact ⟨fun x c => ⌜1 ≤ x ∧ x ≤ b.2.1 - 1 ∧ ∃ t k, LInv m a N p R x.toNat b.2.2 t ∧
              (x.toNat + 1) * 2 ^ t = b.2.1.toNat * 2 ^ (h - Nat.log2 (b.2.1.toNat - 1)) ∧
              (if x = b.2.1 - 1 then
                k ≤ t + (if (b.2.1.toNat - 1) % 2 = 1 ∧ 1 < b.2.1.toNat - 1 then 1 else 0) else k ≤ t) ∧
              c ≤ B + D * k + t + 1⌝,
           fun x c => ⌜1 ≤ x ∧ ¬ (1 < x.toNat ∧ x.toNat % 2 = 1) ∧ ∃ t k, LInv m a N p R x.toNat b.2.2 t ∧
              (x.toNat + 1) * 2 ^ t = b.2.1.toNat * 2 ^ (h - Nat.log2 (b.2.1.toNat - 1)) ∧ k ≤ t ∧
              c ≤ B + D * k + t + 2⌝,
           fun x => x.toNat⟩
  case vc7.inv =>
    exact ⟨fun ⟨xd, smd⟩ c => ⌜0 ≤ xd ∧ ∃ t, DLInv m a N p R xd.toNat smd t ∧ t ≤ h ∧
              c + t * E ≤ B + D * h + h + 2 + cOp + cF + h * E⌝,
           fun ⟨xd, smd⟩ c => ⌜0 ≤ xd ∧ N ≤ xd.toNat ∧ DLInv m a N p R xd.toNat smd 0 ∧
              c ≤ B + D * h + h + 3 + cOp + cF + h * E⌝,
           fun ⟨xd, _⟩ => 2 * N - xd.toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹Option (ℤ × cp.SegmentTree M) × ℤ × M›).2.2 = smo at *
    generalize (‹Option (ℤ × cp.SegmentTree M) × ℤ × M›).2.1 = ro at *)
  case vc1.isTrue.isTrue.isTrue =>
    subst ‹r = 0›
    simp [rf, hpe]
    generalize (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) = X
    omega
  case vc4.step.isTrue =>
    obtain ⟨hx1, hxle, t, hL, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    have hstop := stop_of _ hx1 ‹_›
    refine ⟨hx1, fun _ => by omega, t, hL, hR, k, ?_, by omega⟩
    split at hk
    · rename_i heq; rw [if_neg (by omega)] at hk; exact hk
    · exact hk
  case vc5.step.isFalse =>
    obtain ⟨hx1, hxle, t, hL, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    obtain ⟨hgt, hodd⟩ := ‹(1 : ℤ) < _ ∧ ¬ Cpp.mod _ 2 = 0›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    obtain ⟨c0, c1, c2, c3⟩ := climb_left_int m _ _ _ hN p _ _ _ _ hgt hodd hL
    refine ⟨⟨c0, by omega, t + 1, c2, by rw [c3, hR], k, ?_, by omega⟩, c1, by omega⟩
    rw [if_neg (by omega)]
    split at hk
    · split at hk <;> omega
    · omega
  case vc6.step.pre =>
    obtain ⟨-, hr1, t, hL, k, hk, hc⟩ := ‹_ = none ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hx1 := hL.1
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb := hL.2.2.2.1
    have hb2 := hL.2.2.1
    have hp := Nat.two_pow_pos t
    refine ⟨⟨by omega, t, hL, by rw [← linv_height m _ _ _ hN p _ _ _ _ hL, show ro.toNat - 1 + 1 = ro.toNat by omega],
      k, hk, hc⟩, by simp [fuel]; nlinarith⟩
  case vc8.step.isTrue =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = xd at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DLInv _ _ _ _ _ _ _ t ∧ _›
    have ht0 := dlinv_exit m _ _ p _ _ _ _ hD (by omega)
    subst ht0
    exact ⟨hd0, Or.inl (by omega), hD, by omega⟩
  case vc9.step.isFalse.isTrue =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = xd at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DLInv _ _ _ _ _ _ _ t ∧ _›
    have h1l := hD.1.1
    obtain ⟨t', rfl, h1, -⟩ := descent_left_int m st.node _ hv.allV hv.tree p _ xd smd _ hd0 (by omega) hD
    refine ⟨⟨by omega, t', h1 ‹_›, by omega, ?_⟩, by omega⟩
    have : (t' + 1) * (1 + 2 * cOp + cF) = t' * (1 + 2 * cOp + cF) + (1 + 2 * cOp + cF) := by ring
    omega
  case vc10.step.isFalse.isFalse =>
    generalize (‹ℤ × M›).2 = smd at *
    generalize (‹ℤ × M›).1 = xd at *
    obtain ⟨hd0, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ ∃ t, DLInv _ _ _ _ _ _ _ t ∧ _›
    obtain ⟨t', rfl, -, h2⟩ := descent_left_int m st.node _ hv.allV hv.tree p _ xd smd _ hd0 (by omega) hD
    refine ⟨⟨by omega, t', h2 ‹_›, by omega, ?_⟩, by omega⟩
    have : (t' + 1) * (1 + 2 * cOp + cF) = t' * (1 + 2 * cOp + cF) + (1 + 2 * cOp + cF) := by ring
    omega
  case vc11.step.post.success.isTrue.pre =>
    obtain ⟨hx1, hev, t, hL, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have ht := t_le _ _ _ _ hN hL.1 (le_trans hL.2.2.1 hL.2.2.2.1)
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb := hL.2.2.2.1
    have hb2 := hL.2.2.1
    have hp := Nat.two_pow_pos t
    refine ⟨⟨by omega, t, ⟨hL, by rw [get_eq] at *; assumption⟩, by omega, ?_⟩, by simp [fuel]; omega⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have m2 : t * (1 + 2 * cOp + cF) ≤ st.h_node.toNat * (1 + 2 * cOp + cF) := Nat.mul_le_mul_right _ ht
    omega
  case vc12.step.post.success.isTrue.post.success =>
    obtain ⟨hd0, -, hD, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ∧ DLInv _ _ _ _ _ _ _ 0 ∧ _›
    obtain ⟨-, hop⟩ := linv_pass m _ _ hv.allV hv.tree p _ _ _ _ hD.1
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hD
    simp at h2 h3 h6 hop
    refine ⟨(‹ℤ × M›).1.toNat, by omega, by omega, by omega, by rw [← h6]; exact h7, by rw [← hop]; exact h8, hc⟩
  case vc13.step.post.success.isFalse.isTrue =>
    obtain ⟨hx1, hev, t, hL, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hpow := (pow_cond_left _ (lt_of_lt_of_le zero_lt_one hx1)).mp ‹_›
    have ht := t_le _ _ _ _ hN hL.1 (le_trans hL.2.2.1 hL.2.2.2.1)
    rw [get_eq] at *
    obtain ⟨-, hend⟩ := linv_end m _ _ _ hN hv.allV hv.tree p _ _ _ _ hL ‹_› hpow
    refine ⟨hend, ?_⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have : (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) = (2 + 2 * cOp + cF) * st.h_node.toNat + (2 + 2 * cOp + cF) := by ring
    omega
  case vc14.step.post.success.isFalse.isFalse =>
    obtain ⟨hx1, hev, t, hL, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hpow : ¬ ∃ k, _ = 2 ^ k := fun h => ‹¬ _› ((pow_cond_left _ (lt_of_lt_of_le zero_lt_one hx1)).mpr h)
    have h3 := three_le_of _ hx1 hpow hev
    rw [get_eq] at *
    have hL' := linv_next m _ _ _ hN hv.allV hv.tree p _ _ _ _ hL ‹_› hpow
    refine ⟨⟨hx1, t, hL', k + 1, by rw [if_pos (by omega)]; omega, ?_⟩, ?_⟩
    · have : (2 + 2 * cOp + cF) * (k + 1) = (2 + 2 * cOp + cF) * k + (2 + 2 * cOp + cF) := by ring
      omega
    · have hh := linv_height m _ _ _ hN p _ _ _ _ hL'
      exact measure_dec_left st.n_node.toNat _ _ _ _ (by omega) hh hR
  case vc15.isTrue.isTrue.isFalse.pre =>
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hR1 : st.n_node.toNat < (r + st.n_node).toNat := by omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by omega
    have hL := linv_init m (fun i => st.node[i]!) _ p (r + st.n_node).toNat hR1 hR2 hpe
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2 ^ (st.h_node.toNat - ((r + st.n_node).toNat - 1).log2) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : (r + st.n_node).toNat * 2 ^ (st.h_node.toNat - ((r + st.n_node).toNat - 1).log2) ≤
        2 ^ 31 * 2 ^ 30 := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨⟨by omega, 0, hL, 0, by simp, by omega⟩, ?_⟩
    simp [fuel]; omega
  case vc16.isTrue.isTrue.isFalse.post.success.h_1 =>
    simp only [‹_ = some _›] at *
    obtain ⟨x, hx, hN1, hx2, hp1, hp2, hc⟩ := ‹∃ x : Nat, _ = _ ∧ _›
    subst hx
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have e1 : x + 1 = st.n_node.toNat + ((x : Int) + 1 - st.n_node).toNat := by omega
    rw [e1] at hp1
    rw [show (r + st.n_node).toNat - (st.n_node.toNat + ((x : Int) + 1 - st.n_node).toNat) =
      (r - ((x : Int) + 1 - st.n_node)).toNat by omega, leaves_rf m st v hv _ _ (by omega)] at hp1
    have hl2 := leaves_rf m st v hv (((x : Int) + 1 - st.n_node).toNat - 1)
      ((r - ((x : Int) + 1 - st.n_node) + 1).toNat) (by omega)
    rw [show st.n_node.toNat + (((x : Int) + 1 - st.n_node).toNat - 1) = x by omega,
      show (r - ((x : Int) + 1 - st.n_node) + 1).toNat = (r + st.n_node).toNat - x by omega] at hl2
    rw [hl2] at hp2
    rw [show (r + st.n_node).toNat - x = (r - ((x : Int) + 1 - st.n_node) + 1).toNat by omega] at hp2
    refine ⟨by omega, by omega, by simpa using hp1, Or.inr (by simpa using hp2), rfl, ?_⟩
    have : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * st.h_node.toNat + st.h_node.toNat + st.h_node.toNat * (1 + 2 * cOp + cF) +
          (4 + 4 * cOp + 2 * cF) := by ring
    omega
  case vc17.isTrue.isTrue.isFalse.post.success.h_2 =>
    simp only [‹_ = none›] at *
    obtain ⟨hp1, hc⟩ := ‹p _ = true ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have := leaves_rf m st v hv 0 r.toNat (by omega)
    simp only [Nat.add_zero] at this
    rw [show (r + st.n_node).toNat - st.n_node.toNat = r.toNat by omega, this] at hp1
    refine ⟨by omega, by simpa using hp1, ?_⟩
    have e : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) + (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := by ring
    have : st.h_node.toNat + 1 ≤ (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  case vc19.isFalse =>
    omega

end Proofs.Cpp.SegmentTree
