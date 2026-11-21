import Proofs.Cpp.Gen.SegmentTreeBeatsSum
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.SegmentTreeBeatsSumMath

/-! # Segment tree beats with sums: the proofs of `Proofs.Cpp.SegmentTreeBeats` on the class with the array `sum`

`view` ignores `sum`, so the proofs of library/segment_tree/segment_tree_beats.hpp carry over (retargeted to
`cp.SegmentTreeBeatsSum`). The sum array is handled in Proofs/Cpp/SegmentTreeBeatsSum.lean. -/
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The arrays of the C++ object as functions of the node index. -/
def view (st : cp.SegmentTreeBeatsSum) : BS where
  mx := fun j => st.max_v[j]!
  sx := fun j => st.smax_v[j]!
  cx := fun j => st.max_c[j]!
  mn := fun j => st.min_v[j]!
  sn := fun j => st.smin_v[j]!
  cn := fun j => st.min_c[j]!
  len := fun j => st.len[j]!
  la := fun j => st.ladd[j]!
  lv := fun j => st.lval[j]!

/-- All nine arrays have `N` entries. -/
def Sz (st : cp.SegmentTreeBeatsSum) (N : Nat) : Prop :=
  st.max_v.size = N ∧ st.smax_v.size = N ∧ st.max_c.size = N ∧ st.min_v.size = N ∧ st.smin_v.size = N ∧
    st.min_c.size = N ∧ st.len.size = N ∧ st.ladd.size = N ∧ st.lval.size = N ∧ st.sum.size = N

/-- All nine arrays have the same size. -/
def SzE (st : cp.SegmentTreeBeatsSum) : Prop := Sz st st.max_v.size

theorem getB_set' (v : Array Int) (j : Int) (x : Int) (hj0 : 0 ≤ j) (hj : j.toNat < v.size) :
    (fun i => (Cpp.set v j x)[i]!) = upF (fun i => v[i]!) j.toNat x := by
  funext i
  rw [getElemBang_set v j x i hj]; rfl

theorem cinf : cp.SegmentTreeBeatsSum_INF = INF := rfl

theorem view_mk (n n0 : Int) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Array Int) :
    view ⟨n, n0, a1, a2, a3, a4, a5, a6, a10, a7, a8, a9⟩ =
      ⟨fun j => a1[j]!, fun j => a2[j]!, fun j => a3[j]!, fun j => a4[j]!, fun j => a5[j]!, fun j => a6[j]!,
        fun j => a7[j]!, fun j => a8[j]!, fun j => a9[j]!⟩ := rfl

set_option maxHeartbeats 2000000 in
theorem unm_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_max st k x
    ⦃⇓ r c => ⌜view r = unm (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c = t0 + 1⌝⦄ := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y5 : k.toNat < st.smin_v.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  have hU : unm (view st) k.toNat x = unm (view st) k.toNat x := rfl
  by_cases c1 : st.max_v[k.toNat]! = st.min_v[k.toNat]! <;>
    by_cases c2 : st.max_v[k.toNat]! = st.smin_v[k.toNat]! <;>
    by_cases c3 : st.lval[k.toNat]! = INF <;> by_cases c4 : x < st.lval[k.toNat]! <;>
    by_cases c5 : st.smin_v[k.toNat]! = st.min_v[k.toNat]! <;>
    simp only [cp.SegmentTreeBeatsSum.update_node_max, get_eq, cinf, c1, c2, c3, c4, c5, decide_true, decide_false,
      ite_true, ite_false, Bool.and_true, Bool.true_and, Bool.false_and, Bool.and_false, ne_eq] <;>
    mvcgen <;>
    (try simp +zetaDelta only [] at *) <;>
    refine ⟨?_, by simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10], by simp, by simp, by omega⟩ <;>
    dsimp only [view_mk, unm, view, upF] <;>
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y5,
      getElemBang_set _ _ _ _ y9, c1, c2, c3, c4, c5, ite_true, ite_false, if_true, if_false, ne_eq, not_false_eq_true,
      and_self, size_set, not_true_eq_false, false_and, and_false, and_true, true_and] <;>
    rfl

set_option maxHeartbeats 2000000 in
theorem unmin_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_min st k x
    ⦃⇓ r c => ⌜view r = unmin (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c = t0 + 1⌝⦄ := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y2 : k.toNat < st.smax_v.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  by_cases c1 : st.max_v[k.toNat]! = st.min_v[k.toNat]! <;>
    by_cases c2 : st.smax_v[k.toNat]! = st.min_v[k.toNat]! <;>
    by_cases c3 : st.lval[k.toNat]! = INF <;> by_cases c4 : st.lval[k.toNat]! < x <;>
    by_cases c5 : st.max_v[k.toNat]! = st.smax_v[k.toNat]! <;>
    simp only [cp.SegmentTreeBeatsSum.update_node_min, get_eq, cinf, c1, c2, c3, c4, c5, decide_true, decide_false,
      ite_true, ite_false, Bool.and_true, Bool.true_and, Bool.false_and, Bool.and_false, ne_eq] <;>
    mvcgen <;>
    (try simp +zetaDelta only [] at *) <;>
    refine ⟨?_, by simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10], by simp, by simp, by omega⟩ <;>
    dsimp only [view_mk, unmin, view, upF] <;>
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y2,
      getElemBang_set _ _ _ _ y9, c1, c2, c3, c4, c5, ite_true, ite_false, if_true, if_false, ne_eq, not_false_eq_true,
      and_self, size_set, not_true_eq_false, false_and, and_false, and_true, true_and] <;>
    rfl

set_option maxHeartbeats 2000000 in
theorem addAll_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_all st k x
    ⦃⇓ r c => ⌜view r = addAll (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c = t0 + 1⌝⦄ := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y2 : k.toNat < st.smax_v.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y5 : k.toNat < st.smin_v.size := by omega
  have y8 : k.toNat < st.ladd.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  by_cases c1 : st.smax_v[k.toNat]! = -INF <;>
    by_cases c2 : st.smin_v[k.toNat]! = INF <;>
    by_cases c3 : st.lval[k.toNat]! = INF <;>
    simp only [cp.SegmentTreeBeatsSum.add_all, get_eq, cinf, c1, c2, c3, decide_true, decide_false,
      ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true, decide_not, Bool.not_true, Bool.not_false] <;>
    mvcgen <;>
    (try simp +zetaDelta only [] at *) <;>
    refine ⟨?_, by simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10], by simp, by simp, by omega⟩ <;>
    dsimp only [view_mk, addAll, view, upF] <;>
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y2,
      getElemBang_set _ _ _ _ y5, getElemBang_set _ _ _ _ y8,
      getElemBang_set _ _ _ _ y9, c1, c2, c3, ite_true, ite_false, if_true, if_false, ne_eq, not_false_eq_true,
      and_self, size_set, not_true_eq_false, false_and, and_false, and_true, true_and] <;>
    rfl

set_option maxHeartbeats 2000000 in
theorem updAll_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_all st k x
    ⦃⇓ r c => ⌜view r = updAll (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c = t0 + 1⌝⦄ := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y2 : k.toNat < st.smax_v.size := by omega
  have y3 : k.toNat < st.max_c.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y5 : k.toNat < st.smin_v.size := by omega
  have y6 : k.toNat < st.min_c.size := by omega
  have y8 : k.toNat < st.ladd.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  mvcgen [cp.SegmentTreeBeatsSum.update_all]
  simp +zetaDelta only [] at *
  refine ⟨?_, by simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10], by simp, by simp, by omega⟩
  dsimp only [view_mk, updAll, view, upF]
  simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y2,
    getElemBang_set _ _ _ _ y5, getElemBang_set _ _ _ _ y8, getElemBang_set _ _ _ _ y3, getElemBang_set _ _ _ _ y6,
    getElemBang_set _ _ _ _ y9, get_eq, cinf, ite_true, size_set]
  rfl

set_option maxHeartbeats 2000000 in
theorem upd_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k) (hk : 2 * k.toNat + 2 < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update st k
    ⦃⇓ r c => ⌜view r = upd (view st) k.toNat ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c = t0 + 1⌝⦄ := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y2 : k.toNat < st.smax_v.size := by omega
  have y3 : k.toNat < st.max_c.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y5 : k.toNat < st.smin_v.size := by omega
  have y6 : k.toNat < st.min_c.size := by omega
  have ea : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
  have eb : (2 * k + 2).toNat = 2 * k.toNat + 2 := by omega
  have na : 2 * k.toNat + 1 ≠ k.toNat := by omega
  have nb : 2 * k.toNat + 2 ≠ k.toNat := by omega
  by_cases c1 : st.max_v[2 * k.toNat + 1]! < st.max_v[2 * k.toNat + 2]! <;>
    by_cases c2 : st.max_v[2 * k.toNat + 1]! > st.max_v[2 * k.toNat + 2]! <;>
    by_cases c3 : st.min_v[2 * k.toNat + 1]! < st.min_v[2 * k.toNat + 2]! <;>
    by_cases c4 : st.min_v[2 * k.toNat + 1]! > st.min_v[2 * k.toNat + 2]! <;>
    simp only [cp.SegmentTreeBeatsSum.update, get_eq, ea, eb, c1, c2, c3, c4, decide_true, decide_false,
      ite_true, ite_false] <;>
    mvcgen <;>
    (try simp +zetaDelta only [] at *) <;>
    refine ⟨?_, by simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10], by simp, by simp, by omega⟩ <;>
    dsimp only [view_mk, upd, view, upF, combMax, combMin] <;>
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y2,
      getElemBang_set _ _ _ _ y5, getElemBang_set _ _ _ _ y3, getElemBang_set _ _ _ _ y6, na, nb, c1, c2, c3, c4,
      ite_true, ite_false, if_true, if_false, gt_iff_lt, size_set] <;>
    first | rfl | (exfalso; omega)

theorem st_eta (a : cp.SegmentTreeBeatsSum) :
    (⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd, a.lval⟩ : cp.SegmentTreeBeatsSum) = a := rfl

theorem view_set_ladd (a : cp.SegmentTreeBeatsSum) (k : Int) (v : Int) (hk0 : 0 ≤ k) (hk : k.toNat < a.ladd.size) :
    view ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, Cpp.set a.ladd k v, a.lval⟩ =
      setLa (view a) k.toNat v := by
  show _ = { view a with la := upF (fun j => a.ladd[j]!) k.toNat v }
  rw [← getB_set' _ _ _ hk0 hk]; rfl

theorem view_set_lval (a : cp.SegmentTreeBeatsSum) (k : Int) (v : Int) (hk0 : 0 ≤ k) (hk : k.toNat < a.lval.size) :
    view ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd, Cpp.set a.lval k v⟩ =
      setLv (view a) k.toNat v := by
  show _ = { view a with lv := upF (fun j => a.lval[j]!) k.toNat v }
  rw [← getB_set' _ _ _ hk0 hk]; rfl

theorem SzE_set_ladd (a : cp.SegmentTreeBeatsSum) (k v : Int) (h : SzE a) :
    SzE ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, Cpp.set a.ladd k v, a.lval⟩ := by
  simpa [SzE, Sz] using h

theorem SzE_set_lval (a : cp.SegmentTreeBeatsSum) (k v : Int) (h : SzE a) :
    SzE ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd, Cpp.set a.lval k v⟩ := by
  simpa [SzE, Sz] using h

theorem view_set_ladd' (a : cp.SegmentTreeBeatsSum) (k : Int) (v : Int) (hk0 : 0 ≤ k) (h : SzE a)
    (hk : k.toNat < a.max_v.size) :
    view ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, Cpp.set a.ladd k v, a.lval⟩ =
      setLa (view a) k.toNat v := view_set_ladd a k v hk0 (by obtain ⟨_, _, _, _, _, _, _, h8, _, _⟩ := h; omega)

theorem view_set_lval' (a : cp.SegmentTreeBeatsSum) (k : Int) (v : Int) (hk0 : 0 ≤ k) (h : SzE a)
    (hk : k.toNat < a.max_v.size) :
    view ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd, Cpp.set a.lval k v⟩ =
      setLv (view a) k.toNat v := view_set_lval a k v hk0 (by obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := h; omega)

@[simp] theorem setLa_mx (s : BS) (k : Nat) (v : Int) : (setLa s k v).mx = s.mx := rfl
@[simp] theorem setLa_mn (s : BS) (k : Nat) (v : Int) : (setLa s k v).mn = s.mn := rfl
@[simp] theorem setLa_lv (s : BS) (k : Nat) (v : Int) : (setLa s k v).lv = s.lv := rfl

theorem SzE_set_ladd_n (a : cp.SegmentTreeBeatsSum) (n n0 k v : Int) (h : SzE a) :
    SzE ⟨n, n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, Cpp.set a.ladd k v, a.lval⟩ := by
  simpa [SzE, Sz] using h

theorem SzE_set_lval_n (a : cp.SegmentTreeBeatsSum) (n n0 k v : Int) (h : SzE a) :
    SzE ⟨n, n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd, Cpp.set a.lval k v⟩ := by
  simpa [SzE, Sz] using h

theorem fold_mx (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.max_v[i]! = (view a).mx i := rfl
theorem fold_mn (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.min_v[i]! = (view a).mn i := rfl
theorem fold_sx (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.smax_v[i]! = (view a).sx i := rfl
theorem fold_sn (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.smin_v[i]! = (view a).sn i := rfl
theorem fold_la (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.ladd[i]! = (view a).la i := rfl
theorem fold_lv (a : cp.SegmentTreeBeatsSum) (i : Nat) : a.lval[i]! = (view a).lv i := rfl

section frame
variable (s : BS) (c j : Nat) (x : Int) (h : j ≠ c)
include h
@[simp] theorem unm_mx : (unm s c x).mx j = s.mx j := by unfold unm upF; split_ifs <;> simp [h]
@[simp] theorem unm_mn : (unm s c x).mn j = s.mn j := by unfold unm upF; split_ifs <;> simp [h]
@[simp] theorem unm_lv : (unm s c x).lv j = s.lv j := by unfold unm upF; split_ifs <;> simp [h]
@[simp] theorem unmin_mx : (unmin s c x).mx j = s.mx j := by unfold unmin upF; split_ifs <;> simp [h]
@[simp] theorem unmin_mn : (unmin s c x).mn j = s.mn j := by unfold unmin upF; split_ifs <;> simp [h]
@[simp] theorem unmin_lv : (unmin s c x).lv j = s.lv j := by unfold unmin upF; split_ifs <;> simp [h]
@[simp] theorem addAll_mx : (addAll s c x).mx j = s.mx j := by unfold addAll upF; simp [h]
@[simp] theorem addAll_mn : (addAll s c x).mn j = s.mn j := by unfold addAll upF; simp [h]
@[simp] theorem addAll_la : (addAll s c x).la j = s.la j := by unfold addAll upF; split_ifs <;> simp [h]
@[simp] theorem addAll_lv : (addAll s c x).lv j = s.lv j := by unfold addAll upF; split_ifs <;> simp [h]
@[simp] theorem updAll_lv : (updAll s c x).lv j = s.lv j := by unfold updAll upF; simp [h]
end frame
@[simp] theorem unm_la (s : BS) (c : Nat) (x : Int) (j : Nat) : (unm s c x).la j = s.la j := by
  unfold unm; split_ifs <;> rfl
@[simp] theorem unmin_la (s : BS) (c : Nat) (x : Int) (j : Nat) : (unmin s c x).la j = s.la j := by
  unfold unmin; split_ifs <;> rfl

/-- `push(k)` reading the tags from the current state, in the C++ order. -/
def pushC (s : BS) (k : Nat) : BS :=
  if s.lv k ≠ INF then
    let s1 := updAll s (2 * k + 1) (s.lv k)
    setLv (updAll s1 (2 * k + 2) (s1.lv k)) k INF
  else
    let s3 := if s.la k ≠ 0 then
      let t := addAll s (2 * k + 1) (s.la k)
      setLa (addAll t (2 * k + 2) (t.la k)) k 0 else s
    caps (caps s3 k (2 * k + 1)) k (2 * k + 2)

theorem pushC_eq (s : BS) (k : Nat) : pushC s k = push s k := by
  have na : k ≠ 2 * k + 1 := by omega
  simp only [pushC, push, updAll_lv _ _ _ _ na, addAll_la _ _ _ _ na]

attribute [local spec] unm_cpp unmin_cpp addAll_cpp updAll_cpp

set_option maxHeartbeats 4000000 in
theorem push_cpp (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < st.n0 - 1 → 2 * k.toNat + 2 < st.max_v.size) (hkN : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.push st k
    ⦃⇓ r c => ⌜(st.n0 - 1 ≤ k → r = st) ∧ (k < st.n0 - 1 → view r = push (view st) k.toNat) ∧
      (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c ≤ t0 + 9⌝⦄ := by
  have hsz0 := hsz
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz0
  have ea : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
  have eb : (2 * k + 2).toNat = 2 * k.toNat + 2 := by omega
  have na : k.toNat ≠ 2 * k.toNat + 1 := by omega
  have nb : k.toNat ≠ 2 * k.toNat + 2 := by omega
  have nab : 2 * k.toNat + 1 ≠ 2 * k.toNat + 2 := by omega
  have nba : 2 * k.toNat + 2 ≠ 2 * k.toNat + 1 := by omega
  by_cases hleaf : st.n0 - 1 ≤ k
  · have hd : decide (st.n0 - 1 ≤ k) = true := by simp [hleaf]
    simp only [cp.SegmentTreeBeatsSum.push, hd, ite_true, st_eta]
    mvcgen
    rename_i c hc
    exact ⟨fun _ => trivial, fun h => absurd h (by omega), hsz, trivial, trivial, by omega⟩
  have hk2 := hk (by omega)
  have hd : decide (st.n0 - 1 ≤ k) = false := by simp [hleaf]
  simp only [cp.SegmentTreeBeatsSum.push, hd, Bool.false_eq_true, ite_false]
  mvcgen
  all_goals try simp +zetaDelta only [st_eta, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *
  all_goals try simp only [get_eq, ea, eb, cinf, fold_mx, fold_mn, fold_la, fold_lv, ne_eq, hleaf, false_imp_iff,
    true_and] at *
  all_goals try casesm* _ ∧ _
  all_goals first
    | (show 0 ≤ _; omega)
    | (show _ < _; omega)
    | (show SzE _; first | assumption | (apply SzE_set_ladd; assumption) | (apply SzE_set_lval; assumption))
    | skip
  all_goals try simp (disch := first | assumption | omega) only [view_set_ladd', view_set_lval'] at *
  all_goals try simp only [*]
  all_goals refine ⟨fun _ => ?_, ?_⟩
  all_goals first
    | (and_intros <;> first | assumption | (apply SzE_set_lval; assumption) | omega)
    | skip
  all_goals try simp only [*] at *
  all_goals try (rw [← pushC_eq]; simp only [pushC, caps, *, ne_eq, not_false_eq_true, not_true_eq_false,
      ite_true, ite_false, setLa_mx, setLa_mn, not_not]; done)
  all_goals repeat' (first
    | (apply SzE_set_lval_n; assumption)
    | (apply SzE_set_ladd_n; assumption)
    | trivial
    | omega
    | constructor)

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-! ## Subtrees by index arithmetic -/

theorem sub_iff : ∀ h k j, SegmentTreeBeatsMath.Sub h k j ↔ ∃ d ≤ h, (j + 1) / 2 ^ d = k + 1 := by
  intro h
  induction h with
  | zero => intro k j; simp [SegmentTreeBeatsMath.Sub] <;> omega
  | succ h ih =>
    intro k j
    simp only [SegmentTreeBeatsMath.Sub, ih]
    constructor
    · rintro (rfl | ⟨d, hd, e⟩ | ⟨d, hd, e⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨d + 1, by omega, ?_⟩
        rw [pow_succ, ← Nat.div_div_eq_div_mul, e]; omega
      · refine ⟨d + 1, by omega, ?_⟩
        rw [pow_succ, ← Nat.div_div_eq_div_mul, e]; omega
    · rintro ⟨d, hd, e⟩
      rcases d with _ | d
      · left; simp at e; omega
      · right
        rw [pow_succ, ← Nat.div_div_eq_div_mul] at e
        have : (j + 1) / 2 ^ d = 2 * k + 2 ∨ (j + 1) / 2 ^ d = 2 * k + 3 := by omega
        rcases this with e2 | e2
        · left; exact ⟨d, by omega, by omega⟩
        · right; exact ⟨d, by omega, by omega⟩

theorem div_pow_mono (m d e : Nat) (hde : d ≤ e) : m / 2 ^ e = (m / 2 ^ d) / 2 ^ (e - d) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega

theorem sub_siblings (h k j : Nat) (h1 : SegmentTreeBeatsMath.Sub h (2 * k + 1) j) (h2 : SegmentTreeBeatsMath.Sub h (2 * k + 2) j) : False := by
  rw [sub_iff] at h1 h2
  obtain ⟨d, -, e1⟩ := h1
  obtain ⟨e, -, e2⟩ := h2
  rcases Nat.lt_trichotomy d e with hde | rfl | hde
  · rw [div_pow_mono _ d e hde.le, e1] at e2
    have : (2 * k + 1 + 1) / 2 ^ (e - d) ≤ (2 * k + 2) / 2 := by
      apply Nat.div_le_div_left _ (by omega)
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (e - d) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · omega
  · rw [div_pow_mono _ e d hde.le, e2] at e1
    have : (2 * k + 2 + 1) / 2 ^ (d - e) ≤ (2 * k + 3) / 2 := by
      apply Nat.div_le_div_left _ (by omega)
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (d - e) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ## The effect of a range operation on the leaf values -/

/-- Apply `f` to the values at the positions in `[a, b)`; the list starts at position `lo`. -/
def opL (f : Int → Int) (a b : Int) (lo : Nat) (L : List Int) : List Int :=
  L.mapIdx (fun i v => if a ≤ ((lo + i : Nat) : Int) ∧ ((lo + i : Nat) : Int) < b then f v else v)

theorem opL_append (f : Int → Int) (a b : Int) (lo : Nat) (A B : List Int) :
    opL f a b lo (A ++ B) = opL f a b lo A ++ opL f a b (lo + A.length) B := by
  simp only [opL, List.mapIdx_append]
  congr 1
  congr 1
  funext i v
  rw [show lo + (i + A.length) = lo + A.length + i by omega]

theorem opL_nil (f : Int → Int) (a b : Int) (lo : Nat) : opL f a b lo [] = [] := rfl

theorem opL_append' (f : Int → Int) (a b : Int) (lo m : Nat) (A B : List Int) (hAB : A.length = m ∨ B = []) :
    opL f a b lo (A ++ B) = opL f a b lo A ++ opL f a b (lo + m) B := by
  rw [opL_append]
  rcases hAB with h | rfl
  · rw [h]
  · rfl

/-! ## The recursion over a subtree -/

theorem sub_self (h k : Nat) : SegmentTreeBeatsMath.Sub h k k := by cases h <;> simp [SegmentTreeBeatsMath.Sub]

theorem agree_refl (s : BS) (j : Nat) : AgreeAt s s j := by simp [AgreeAt]

/-- Offsets that are all zero (the ancestors of a visited node have been pushed). -/
def Zs (O : List Int) : Prop := 0 ∈ O ∧ ∀ o ∈ O, o = 0

theorem zs_cons (O : List Int) (h : Zs O) : Zs (0 :: O) :=
  ⟨List.mem_cons_self, fun o ho => by rcases List.mem_cons.mp ho with rfl | ho; rfl; exact h.2 o ho⟩

/-- What a range operation `f` on `[a, b)` guarantees at node `k`, from `s` to `t`. -/
def RecPost (f : Int → Int) (a b : Int) (n : Nat) (B : Int) (h k lo : Nat) (O : List Int) (s t : BS) : Prop :=
  Inv t n h k lo ∧ Safe t n B h k lo O ∧ T t n h k lo = opL f a b lo (T s n h k lo) ∧
    ∀ j, ¬ SegmentTreeBeatsMath.Sub h k j → AgreeAt s t j

theorem push_post (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int) (h0 : 0 ∈ O)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) : PushPost s (push s k) n B h k lo O := by
  by_cases hlv : s.lv k = INF
  · exact push_add s n B hB h k lo O h0 hI hS hlv
  · exact push_set s n B hB h k lo O h0 hI hS hlv

theorem map_add_zero (O : List Int) : O.map (· + 0) = O := by simp

/-- The first child can be visited after `push(k)`. -/
theorem inner_pre1 (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat) (O : List Int) (hZ : Zs O)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O) :
    Inv (push s k) n h (2 * k + 1) lo ∧ Safe (push s k) n B h (2 * k + 1) lo (0 :: O) ∧
      Inv (push s k) n h (2 * k + 2) (lo + 2 ^ h) ∧ Safe (push s k) n B h (2 * k + 2) (lo + 2 ^ h) (0 :: O) := by
  obtain ⟨p1, p2, -, p4, p5, -⟩ := push_post s n B hB h k lo O hZ.1 hI hS
  obtain ⟨-, hS2⟩ := p2
  obtain ⟨q1, q2⟩ := hS2 p5
  rw [p4, map_add_zero] at q1 q2
  exact ⟨p1.1, q1, p1.2.1, q2⟩

/-- The second child can be visited after the first one. -/
theorem inner_pre2 (f : Int → Int) (a b : Int) (s s3 : BS) (n : Nat) (B B' : Int) (hB : B < INF) (h k lo : Nat)
    (O : List Int) (hZ : Zs O) (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo O)
    (h3 : RecPost f a b n B' h (2 * k + 1) lo (0 :: O) (push s k) s3) :
    Inv s3 n h (2 * k + 2) (lo + 2 ^ h) ∧ Safe s3 n B h (2 * k + 2) (lo + 2 ^ h) (0 :: O) := by
  obtain ⟨-, -, i2, s2⟩ := inner_pre1 s n B hB h k lo O hZ hI hS
  have hA : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt (push s k) s3 j :=
    fun j hj => h3.2.2.2 j (fun h1 => sub_siblings h k j h1 hj)
  exact ⟨inv_frame _ _ n h _ _ hA i2, safe_frame _ _ n B h _ _ _ hA s2⟩

/-- Combine the two children after `update(k)`. -/
theorem inner_post (f : Int → Int) (a b : Int) (s s3 s4 : BS) (n : Nat) (B B' : Int) (hB : B < INF)
    (hB' : B' < INF) (h k lo : Nat) (O : List Int) (hZ : Zs O) (hI : Inv s n (h + 1) k lo)
    (hS : Safe s n B (h + 1) k lo O)
    (h3 : RecPost f a b n B' h (2 * k + 1) lo (0 :: O) (push s k) s3)
    (h4 : RecPost f a b n B' h (2 * k + 2) (lo + 2 ^ h) (0 :: O) s3 s4) :
    RecPost f a b n B' (h + 1) k lo O s (upd s4 k) := by
  obtain ⟨p1, p2, p3, p4, p5, -, -, -, -, -, -, p12, p13, p14, p15⟩ := push_post s n B hB h k lo O hZ.1 hI hS
  obtain ⟨r3I, r3S, r3T, r3A⟩ := h3
  obtain ⟨r4I, r4S, r4T, r4A⟩ := h4
  set s2 := push s k
  -- agreement facts
  have nk1 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → j ≠ k := fun j hj => notsub_k h k j (Or.inl hj)
  have nk2 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → j ≠ k := fun j hj => notsub_k h k j (Or.inr hj)
  have a43 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt s3 s4 j :=
    fun j hj => r4A j (fun h2 => sub_siblings h k j hj h2)
  have a23 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt s2 s3 j :=
    fun j hj => r3A j (fun h1 => sub_siblings h k j h1 hj)
  have a5 : ∀ j, j ≠ k → AgreeAt s4 (upd s4 k) j := upd_agree s4 k
  have ak : AgreeAt s2 s4 k := agree_trans _ _ _ k (r3A k (fun h1 => nk1 k h1 rfl)) (r4A k (fun h2 => nk2 k h2 rfl))
  obtain ⟨-, -, -, -, -, -, k7, k8, k9⟩ := ak
  -- children of `s4`
  have c1I : Inv s4 n h (2 * k + 1) lo := inv_frame _ _ n h _ _ a43 r3I
  have c1S : Safe s4 n B' h (2 * k + 1) lo (0 :: O) := safe_frame _ _ n B' h _ _ _ a43 r3S
  have c1T : T s4 n h (2 * k + 1) lo = T s3 n h (2 * k + 1) lo := (T_frame _ _ n h _ _ a43).symm
  have c2T0 : T s3 n h (2 * k + 2) (lo + 2 ^ h) = T s2 n h (2 * k + 2) (lo + 2 ^ h) :=
    (T_frame _ _ n h _ _ a23).symm
  have hR1 : InR (T s4 n h (2 * k + 1) lo) :=
    inR_zero _ (safe_inR _ n B' hB' h _ _ _ c1S 0 List.mem_cons_self)
  have hR2 : InR (T s4 n h (2 * k + 2) (lo + 2 ^ h)) :=
    inR_zero _ (safe_inR _ n B' hB' h _ _ _ r4S 0 List.mem_cons_self)
  have hlen : s4.len k = 2 ^ (h + 1) := by rw [← k7]; exact inv_len _ n _ _ _ p1
  obtain ⟨uI, uT⟩ := upd_spec s4 n h k lo c1I r4I hR1 hR2 (k8 ▸ p4) (k9 ▸ p5) hlen
  refine ⟨uI, ?_, ?_, ?_⟩
  · -- safety at `k`
    refine ⟨?_, fun _ => ?_⟩
    · intro o ho v hv
      rw [hZ.2 o ho, uT] at *
      rcases List.mem_append.mp hv with hv | hv
      · exact safe_top _ n B' h _ _ _ c1S 0 List.mem_cons_self v hv
      · exact safe_top _ n B' h _ _ _ r4S 0 List.mem_cons_self v hv
    · have hla : (upd s4 k).la k = 0 := by simp only [upd]; exact k8 ▸ p4
      rw [hla, map_add_zero]
      exact ⟨safe_frame _ _ n B' h _ _ _ (fun j hj => a5 j (nk1 j hj)) c1S,
        safe_frame _ _ n B' h _ _ _ (fun j hj => a5 j (nk2 j hj)) r4S⟩
  · -- the values
    rw [uT, c1T, r3T, r4T, c2T0]
    have hsplit : T s n (h + 1) k lo = T s2 n h (2 * k + 1) lo ++ T s2 n h (2 * k + 2) (lo + 2 ^ h) := by
      rw [p14, p15]; simp only [T, List.map_append]
    rw [hsplit]
    refine (opL_append' f a b lo (2 ^ h) _ _ ?_).symm
    simp only [T_length]
    by_cases hn : 2 ^ h ≤ n - lo
    · left; omega
    · right; apply List.eq_nil_of_length_eq_zero; rw [T_length]; omega
  · -- the frame
    intro j hj
    have j0 : j ≠ k := fun e => hj (e ▸ sub_self _ _)
    have j1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j := fun e => hj (sub_child1 h k j e)
    have j2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j := fun e => hj (sub_child2 h k j e)
    exact agree_trans _ _ _ j (p13 j j0 (fun e => j1 (e ▸ sub_self _ _)) (fun e => j2 (e ▸ sub_self _ _)))
      (agree_trans _ _ _ j (r3A j j1) (agree_trans _ _ _ j (r4A j j2) (a5 j j0)))

/-! ## Leaf-value effects in the base cases -/

theorem opL_eq_map_of (f g : Int → Int) (a b : Int) (lo : Nat) (L : List Int)
    (H : ∀ i (hi : i < L.length), (if a ≤ ((lo + i : Nat) : Int) ∧ ((lo + i : Nat) : Int) < b then f L[i] else L[i]) =
      g L[i]) : opL f a b lo L = L.map g := by
  apply List.ext_getElem (by simp [opL])
  intro i h1 h2
  simp only [opL, List.getElem_mapIdx, List.getElem_map]
  exact H i (by simpa [opL] using h1)

theorem opL_disjoint (f : Int → Int) (a b : Int) (lo : Nat) (L : List Int)
    (h : b ≤ lo ∨ lo + L.length ≤ a) : opL f a b lo L = L := by
  rw [opL_eq_map_of f id a b lo L (fun i hi => by rw [if_neg (by omega)]; rfl), List.map_id]

theorem opL_fix (f : Int → Int) (a b : Int) (lo : Nat) (L : List Int) (h : ∀ v ∈ L, f v = v) :
    opL f a b lo L = L := by
  rw [opL_eq_map_of f id a b lo L (fun i hi => by split_ifs <;> simp [h _ (List.getElem_mem hi)]), List.map_id]

theorem opL_all (f : Int → Int) (a b : Int) (lo : Nat) (L : List Int) (h1 : a ≤ lo) (h2 : lo + L.length ≤ b) :
    opL f a b lo L = L.map f :=
  opL_eq_map_of f f a b lo L (fun i hi => by rw [if_pos (by omega)])

theorem safe_le (s : BS) (n : Nat) (B B' : Int) (hBB : B ≤ B') : ∀ h k lo O,
    Safe s n B h k lo O → Safe s n B' h k lo O := by
  intro h
  induction h with
  | zero => intro k lo O hS o ho v hv; exact (hS o ho v hv).trans hBB
  | succ h ih =>
    intro k lo O hS
    exact ⟨fun o ho v hv => (hS.1 o ho v hv).trans hBB,
      fun hl => ⟨ih _ _ _ (hS.2 hl).1, ih _ _ _ (hS.2 hl).2⟩⟩

theorem len_T_le (s : BS) (n h k lo : Nat) : (T s n h k lo).length ≤ 2 ^ h := by
  rw [T_length]; omega

/-- Nothing to do at node `k`. -/
theorem rec_skip (f : Int → Int) (a b : Int) (s : BS) (n : Nat) (B B' : Int) (hBB : B ≤ B') (h k lo : Nat)
    (O : List Int) (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (hT : opL f a b lo (T s n h k lo) = T s n h k lo) : RecPost f a b n B' h k lo O s s :=
  ⟨hI, safe_le s n B B' hBB h k lo O hS, hT.symm, fun j _ => agree_refl s j⟩

/-- The values of node `k` are at most its maximum. -/
theorem T_le_mx (s : BS) (n h k lo : Nat) (hI : Inv s n h k lo) : ∀ v ∈ T s n h k lo, v ≤ s.mx k := by
  intro v hv
  rw [(inv_summ s n h k lo hI).mx]; exact lmax_ge _ v hv

theorem chmin_skip (x a b : Int) (s : BS) (n : Nat) (B B' : Int) (hBB : B ≤ B') (h k lo : Nat) (O : List Int)
    (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (hc : b ≤ (lo : Int) ∨ ((lo + 2 ^ h : Nat) : Int) ≤ a ∨ s.mx k ≤ x) : RecPost (min · x) a b n B' h k lo O s s := by
  refine rec_skip _ a b s n B B' hBB h k lo O hI hS ?_
  have := len_T_le s n h k lo
  rcases hc with hc | hc | hc
  · exact opL_disjoint _ a b lo _ (Or.inl hc)
  · exact opL_disjoint _ a b lo _ (Or.inr (by omega))
  · exact opL_fix _ a b lo _ (fun v hv => by have := T_le_mx s n h k lo hI v hv; simp; omega)

theorem chmin_cover (x a b : Int) (s : BS) (n : Nat) (B B' : Int) (hB' : B' < INF) (hBB : B ≤ B') (hx : |x| ≤ B')
    (hxI : x < INF) (h k lo : Nat) (O : List Int) (hZ : Zs O) (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (ha : a ≤ (lo : Int)) (hb : ((lo + 2 ^ h : Nat) : Int) ≤ b) (h1 : s.sx k < x) (h2 : x < s.mx k) :
    RecPost (min · x) a b n B' h k lo O s (unm s k x) := by
  have hS' := safe_le s n B B' hBB h k lo O hS
  obtain ⟨uI, uT⟩ := unm_node s n B' hB' h k lo O hZ.1 hI hS' x h1 h2
  have hlen := len_T_le s n h k lo
  refine ⟨uI, ?_, by rw [uT, opL_all _ a b lo _ ha (by omega)], fun j hj => unm_agree s k x j
    (fun e => hj (e ▸ sub_self _ _))⟩
  obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := unm_fields s k x
  refine safe_change_top s _ n B' h k lo O (unm_agree s k x) f8 ?_ hS' ?_
  · rw [f9]; split_ifs with hc <;> [exact ⟨fun e => absurd e (by omega), fun e => absurd e hc.1⟩; exact Iff.rfl]
  · intro o ho v hv
    rw [hZ.2 o ho, uT] at *
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := safe_top s n B' h k lo O hS' 0 hZ.1 w hw
    simp only [add_zero] at *
    exact abs_min_le w x 0 B' (by simpa using this) (by simpa using hx) |>.trans_eq' (by simp)

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- Node `k` of height `h` covers the leaves `[lo, lo + 2 ^ h)` of a tree of height `H`. -/
def Pos (H h k lo : Nat) : Prop := (k + 1) * 2 ^ h = 2 ^ H + lo ∧ lo + 2 ^ h ≤ 2 ^ H

/-- The facts about the C++ object kept by every operation. -/
def Shape (st : cp.SegmentTreeBeatsSum) (H : Nat) : Prop :=
  SzE st ∧ st.n0 = 2 ^ H ∧ 2 * 2 ^ H ≤ st.max_v.size ∧ 0 ≤ st.n

theorem pos_inner (H h kn lo : Nat) (hP : Pos H (h + 1) kn lo) : kn + 2 ≤ 2 ^ H := by
  obtain ⟨e, le⟩ := hP
  have h2 : 2 ≤ 2 ^ (h + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e' : kn * 2 ^ (h + 1) + 2 ^ (h + 1) = 2 ^ H + lo := by rw [← e]; ring
  have : (kn + 2) * 2 ^ (h + 1) ≤ 2 * 2 ^ H := by rw [Nat.add_mul]; omega
  have : (kn + 2) * 2 ≤ (kn + 2) * 2 ^ (h + 1) := Nat.mul_le_mul_left _ h2
  omega

theorem pos_child1 (H h kn lo : Nat) (hP : Pos H (h + 1) kn lo) : Pos H h (2 * kn + 1) lo := by
  obtain ⟨e, le⟩ := hP
  refine ⟨?_, ?_⟩
  · rw [pow_succ] at e; rw [← e]; ring
  · rw [pow_succ] at le; omega

theorem pos_child2 (H h kn lo : Nat) (hP : Pos H (h + 1) kn lo) : Pos H h (2 * kn + 2) (lo + 2 ^ h) := by
  obtain ⟨e, le⟩ := hP
  rw [pow_succ] at e le
  have : (2 * kn + 2 + 1) * 2 ^ h = (kn + 1) * (2 ^ h * 2) + 2 ^ h := by ring
  refine ⟨?_, ?_⟩
  · show (2 * kn + 2 + 1) * 2 ^ h = 2 ^ H + (lo + 2 ^ h); omega
  · show lo + 2 ^ h + 2 ^ h ≤ 2 ^ H; omega

theorem pos_leaf (H kn lo : Nat) (hP : Pos H 0 kn lo) : 2 ^ H ≤ kn + 1 ∧ kn + 2 ≤ 2 * 2 ^ H := by
  obtain ⟨e, le⟩ := hP
  simp at e le; omega

theorem div_mid (l : Int) (h : Nat) (hl : 0 ≤ l) : Cpp.div (l + (l + 2 ^ (h + 1))) 2 = l + 2 ^ h := by
  unfold Cpp.div
  rw [Int.tdiv_eq_ediv_of_nonneg (by positivity), pow_succ]
  omega

theorem toNat_2k1 (k : Int) (hk : 0 ≤ k) : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
theorem toNat_2k2 (k : Int) (hk : 0 ≤ k) : (2 * k + 2).toNat = 2 * k.toNat + 2 := by omega
theorem toNat_add_pow (l : Int) (h : Nat) (hl : 0 ≤ l) : (l + 2 ^ h).toNat = l.toNat + 2 ^ h := by
  have : (0 : Int) ≤ 2 ^ h := by positivity
  have e : ((2 ^ h : Nat) : Int) = 2 ^ h := by push_cast; rfl
  omega

theorem safe_zeros (s : BS) (n : Nat) (B : Int) (h k lo : Nat) :
    Safe s n B h k lo [0] ↔ Safe s n B h k lo (0 :: [0]) :=
  ⟨safe_mono s n B h k lo _ _ (by simp), safe_mono s n B h k lo _ _ (by simp)⟩

theorem recpost_zeros (f : Int → Int) (a b : Int) (n : Nat) (B : Int) (h k lo : Nat) (s t : BS) :
    RecPost f a b n B h k lo [0] s t ↔ RecPost f a b n B h k lo (0 :: [0]) s t := by
  unfold RecPost; rw [safe_zeros]

theorem zs0 : Zs [0] := ⟨by simp, by simp⟩

theorem inner_pre1_0 (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo [0]) :
    Inv (push s k) n h (2 * k + 1) lo ∧ Safe (push s k) n B h (2 * k + 1) lo [0] := by
  obtain ⟨a1, a2, -, -⟩ := inner_pre1 s n B hB h k lo [0] zs0 hI hS
  exact ⟨a1, (safe_zeros _ _ _ _ _ _).mpr a2⟩

theorem inner_pre2_0 (f : Int → Int) (a b : Int) (s s3 : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo [0])
    (h3 : RecPost f a b n B h (2 * k + 1) lo [0] (push s k) s3) :
    Inv s3 n h (2 * k + 2) (lo + 2 ^ h) ∧ Safe s3 n B h (2 * k + 2) (lo + 2 ^ h) [0] := by
  obtain ⟨a1, a2⟩ := inner_pre2 f a b s s3 n B B hB h k lo [0] zs0 hI hS ((recpost_zeros _ _ _ _ _ _ _ _ _ _).mp h3)
  exact ⟨a1, (safe_zeros _ _ _ _ _ _).mpr a2⟩

theorem inner_post0 (f : Int → Int) (a b : Int) (s s3 s4 : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo [0])
    (h3 : RecPost f a b n B h (2 * k + 1) lo [0] (push s k) s3)
    (h4 : RecPost f a b n B h (2 * k + 2) (lo + 2 ^ h) [0] s3 s4) :
    RecPost f a b n B (h + 1) k lo [0] s (upd s4 k) :=
  inner_post f a b s s3 s4 n B B hB hB h k lo [0] zs0 hI hS ((recpost_zeros _ _ _ _ _ _ _ _ _ _).mp h3)
    ((recpost_zeros _ _ _ _ _ _ _ _ _ _).mp h4)

theorem child1_ok (st t2 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat) (k l : Int) (hk0 : 0 ≤ k)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n) :
    Inv (view t2) t2.n.toNat h (2 * k + 1).toNat l.toNat ∧ Safe (view t2) t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] := by
  rw [hv, hn, toNat_2k1 k hk0]; exact inner_pre1_0 _ _ B hB h _ _ hI hS

theorem child2_ok (f : Int → Int) (a b : Int) (st t2 t3 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost f a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3)) (hn3 : t3.n = t2.n) :
    Inv (view t3) t3.n.toNat h (2 * k + 2).toNat m.toNat ∧ Safe (view t3) t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] := by
  rw [hv, hn, toNat_2k1 k hk0] at hR3
  rw [hn3, hn, toNat_2k2 k hk0, hm]; exact inner_pre2_0 f a b _ _ _ B hB h _ _ hI hS hR3

theorem rec_finish (f : Int → Int) (a b : Int) (st t2 t3 t4 t5 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF)
    (h : Nat) (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost f a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3)) (hn3 : t3.n = t2.n)
    (hR4 : RecPost f a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4)) (hn4 : t4.n = t3.n)
    (hv5 : view t5 = upd (view t4) k.toNat) :
    RecPost f a b st.n.toNat B (h + 1) k.toNat l.toNat [0] (view st) (view t5) := by
  rw [hv, hn, toNat_2k1 k hk0] at hR3
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4
  rw [hv5]; exact inner_post0 f a b _ _ _ _ B hB h _ _ hI hS hR3 hR4

theorem pos_bound (H h kn lo : Nat) (hP : Pos H h kn lo) : kn + 1 < 2 * 2 ^ H := by
  obtain ⟨e, le⟩ := hP
  have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have : kn + 1 ≤ (kn + 1) * 2 ^ h := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem leaf_sx (s : BS) (n k lo : Nat) (hI : Inv s n 0 k lo) (hmx : -INF < s.mx k) : s.sx k = -INF := by
  obtain ⟨hS, -⟩ := hI
  have h1 := hS.mx; have h2 := hS.smx
  simp only [T] at h1 h2
  split_ifs at h1 h2 with hlo
  · rw [h2]; simp [smax, lmax, max_eq_left hmx.le]
  · simp [lmax] at h1; omega

/-- The common hypotheses of the recursion at node `k`. -/
def ChminPre (H : Nat) (B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) : Prop :=
  0 ≤ k ∧ 0 ≤ l ∧ r = l + 2 ^ h ∧ Pos H h k.toNat l.toNat ∧ Shape st H ∧
    Inv (view st) st.n.toNat h k.toNat l.toNat ∧ Safe (view st) st.n.toNat B h k.toNat l.toNat [0]

/-- The postcondition of the recursion at node `k`. -/
def ChminPost (H : Nat) (x a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost (min · x) a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1)

theorem chmin_skip_cpp (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜ChminPost H x a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hl' : l = ((l.toNat : Nat) : Int) := by omega
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (Cpp.get st.max_v k ≤ x)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_mx]; omega
  simp only [cp.SegmentTreeBeatsSum._chmin_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  refine ⟨chmin_skip x a b _ _ B B le_rfl _ _ _ [0] hI hS ?_, ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, ?_⟩
  · rw [hl', hr'] at c1; exact c1
  · have : 2 ≤ 2 ^ (h + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem chmin_cover_cpp (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx2 : x < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : ¬ (b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x))
    (c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜ChminPost H x a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hkb := pos_bound H h _ _ hP
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (Cpp.get st.max_v k ≤ x)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mx]; omega
  have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (Cpp.get st.smax_v k < x)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_sx]; omega
  simp only [cp.SegmentTreeBeatsSum._chmin_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [unm_cpp]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨hv, ⟨hsz', hse⟩, hnn, hn0', hc⟩ := hpost
    have h2 : x < (view st).mx k.toNat := by omega
    unfold ChminPost
    rw [hv]
    refine ⟨chmin_cover x a b _ _ B B hB le_rfl hx hx2 _ _ _ [0] zs0 hI hS (by omega) (by rw [← hr']; exact c2.2.1)
      c2.2.2 h2, ⟨hsz', hn0'.trans hn0, by omega, by omega⟩, hse, hnn, ?_⟩
    have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow; omega

theorem chmin_rec_spec (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜ChminPost H x a b B h st k l t0 res c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x
    · exact chmin_skip_cpp H x a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x
    · exact chmin_cover_cpp H x a b B hB hx hx2 0 f st k l r t0 hpre c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, hP, -, hI, -⟩ := hpre
    have := leaf_sx _ _ _ _ hI (by omega)
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x
    · exact chmin_skip_cpp H x a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x
    · exact chmin_cover_cpp H x a b B hB hx hx2 (h + 1) f st k l r t0 hpre c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (Cpp.get st.max_v k ≤ x)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mx]; omega
    have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (Cpp.get st.smax_v k < x)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_sx]; omega
    simp only [cp.SegmentTreeBeatsSum._chmin_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hinv1 := inner_pre1_0 _ _ B hB h _ _ hI hS
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp, upd_cpp]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold ChminPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_ok (min · x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_ok (min · x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    refine ⟨rec_finish (min · x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption), ⟨by assumption, ?_, ?_, ?_⟩,
      ?_, ?_, ?_⟩ <;> omega

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

theorem leaf_sn (s : BS) (n k lo : Nat) (hI : Inv s n 0 k lo) (hmn : s.mn k < INF) : s.sn k = INF := by
  obtain ⟨hS, -⟩ := hI
  have h1 := hS.mn; have h2 := hS.smn
  simp only [T] at h1 h2
  split_ifs at h1 h2 with hlo
  · have hm : s.mx k < INF := by simp [lmin] at h1; omega
    rw [h2]; simp [smin, lmin, min_eq_left hm.le]
  · simp [lmin] at h1; omega

theorem T_ge_mn (s : BS) (n h k lo : Nat) (hI : Inv s n h k lo) : ∀ v ∈ T s n h k lo, s.mn k ≤ v := by
  intro v hv
  rw [(inv_summ s n h k lo hI).mn]; exact lmin_le _ v hv

theorem chmax_skip (x a b : Int) (s : BS) (n : Nat) (B B' : Int) (hBB : B ≤ B') (h k lo : Nat) (O : List Int)
    (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (hc : b ≤ (lo : Int) ∨ ((lo + 2 ^ h : Nat) : Int) ≤ a ∨ x ≤ s.mn k) : RecPost (max · x) a b n B' h k lo O s s := by
  refine rec_skip _ a b s n B B' hBB h k lo O hI hS ?_
  have := len_T_le s n h k lo
  rcases hc with hc | hc | hc
  · exact opL_disjoint _ a b lo _ (Or.inl hc)
  · exact opL_disjoint _ a b lo _ (Or.inr (by omega))
  · exact opL_fix _ a b lo _ (fun v hv => by have := T_ge_mn s n h k lo hI v hv; simp; omega)

theorem chmax_cover (x a b : Int) (s : BS) (n : Nat) (B B' : Int) (hB' : B' < INF) (hBB : B ≤ B') (hx : |x| ≤ B')
    (hxI : -INF < x) (hxI' : x < INF) (h k lo : Nat) (O : List Int) (hZ : Zs O) (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (ha : a ≤ (lo : Int)) (hb : ((lo + 2 ^ h : Nat) : Int) ≤ b) (h1 : x < s.sn k) (h2 : s.mn k < x) :
    RecPost (max · x) a b n B' h k lo O s (unmin s k x) := by
  have hS' := safe_le s n B B' hBB h k lo O hS
  obtain ⟨uI, uT⟩ := unmin_node s n B' hB' h k lo O hZ.1 hI hS' x h2 h1
  have hlen := len_T_le s n h k lo
  refine ⟨uI, ?_, by rw [uT, opL_all _ a b lo _ ha (by omega)], fun j hj => unmin_agree s k x j
    (fun e => hj (e ▸ sub_self _ _))⟩
  obtain ⟨-, -, -, -, -, -, -, f8, f9⟩ := unmin_fields s k x
  refine safe_change_top s _ n B' h k lo O (unmin_agree s k x) f8 ?_ hS' ?_
  · rw [f9]; split_ifs with hc <;> [exact ⟨fun e => absurd e (by omega), fun e => absurd e hc.1⟩; exact Iff.rfl]
  · intro o ho v hv
    rw [hZ.2 o ho, uT] at *
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := safe_top s n B' h k lo O hS' 0 hZ.1 w hw
    simp only [add_zero] at *
    exact abs_max_le w x 0 B' (by simpa using this) (by simpa using hx) |>.trans_eq' (by simp)

/-- The postcondition of the recursion at node `k`. -/
def ChmaxPost (H : Nat) (x a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost (max · x) a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1)

theorem chmax_skip_cpp (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜ChmaxPost H x a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hl' : l = ((l.toNat : Nat) : Int) := by omega
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (x ≤ Cpp.get st.min_v k)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_mn]; omega
  simp only [cp.SegmentTreeBeatsSum._chmax_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  refine ⟨chmax_skip x a b _ _ B B le_rfl _ _ _ [0] hI hS ?_, ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, ?_⟩
  · rw [hl', hr'] at c1; exact c1
  · have : 2 ≤ 2 ^ (h + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem chmax_cover_cpp (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : ¬ (b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat))
    (c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜ChmaxPost H x a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hkb := pos_bound H h _ _ hP
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (x ≤ Cpp.get st.min_v k)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mn]; omega
  have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (x < Cpp.get st.smin_v k)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_sn]; omega
  simp only [cp.SegmentTreeBeatsSum._chmax_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [unmin_cpp]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨hv, ⟨hsz', hse⟩, hnn, hn0', hc⟩ := hpost
    have h2 : (view st).mn k.toNat < x := by omega
    unfold ChmaxPost
    rw [hv]
    refine ⟨chmax_cover x a b _ _ B B hB le_rfl hx hx1 hx2 _ _ _ [0] zs0 hI hS (by omega) (by rw [← hr']; exact c2.2.1)
      c2.2.2 h2, ⟨hsz', hn0'.trans hn0, by omega, by omega⟩, hse, hnn, ?_⟩
    have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow; omega

theorem chmax_rec_spec (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜ChmaxPost H x a b B h st k l t0 res c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat
    · exact chmax_skip_cpp H x a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat
    · exact chmax_cover_cpp H x a b B hB hx hx1 hx2 0 f st k l r t0 hpre c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, hP, -, hI, -⟩ := hpre
    have := leaf_sn _ _ _ _ hI (by omega)
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat
    · exact chmax_skip_cpp H x a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat
    · exact chmax_cover_cpp H x a b B hB hx hx1 hx2 (h + 1) f st k l r t0 hpre c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (x ≤ Cpp.get st.min_v k)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mn]; omega
    have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (x < Cpp.get st.smin_v k)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_sn]; omega
    simp only [cp.SegmentTreeBeatsSum._chmax_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hinv1 := inner_pre1_0 _ _ B hB h _ _ hI hS
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp, upd_cpp]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold ChmaxPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_ok (max · x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_ok (max · x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    refine ⟨rec_finish (max · x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption), ⟨by assumption, ?_, ?_, ?_⟩,
      ?_, ?_, ?_⟩ <;> omega

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The postcondition of a range operation `f` at node `k`. -/
def OpPost (H : Nat) (f : Int → Int) (a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost f a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1)

theorem updval_cover (x a b : Int) (s : BS) (n : Nat) (B : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF)
    (h k lo : Nat) (O : List Int) (hZ : Zs O) (hI : Inv s n h k lo) (hS : Safe s n B h k lo O)
    (ha : a ≤ (lo : Int)) (hb : ((lo + 2 ^ h : Nat) : Int) ≤ b) (hbn : b ≤ (n : Int)) :
    RecPost (fun _ => x) a b n B h k lo O s (updAll s k x) := by
  have hreal : lo + 2 ^ h ≤ n := by omega
  obtain ⟨uI, uT⟩ := updAll_spec s n h k lo x hI hreal ⟨hx1, hx2⟩
  have hlen := inv_real_length s n h k lo hreal
  refine ⟨uI, safe_updAll s n B h k lo O x ⟨hx1, hx2⟩ uT (fun o ho => by rw [hZ.2 o ho]; simpa using hx), ?_,
    fun j hj => updAll_agree s k x j (fun e => hj (e ▸ sub_self _ _))⟩
  rw [uT, opL_all _ a b lo _ ha (by omega), List.map_const', hlen]

theorem updval_skip_cpp (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜OpPost H (fun _ => x) a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hl' : l = ((l.toNat : Nat) : Int) := by omega
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._update_val_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_disjoint _ a b _ _ ?_), ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, ?_⟩
  · omega
  · have : 2 ≤ 2 ^ (h + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem updval_cover_cpp (H : Nat) (x a b B : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat) (hpre : ChminPre H B h st k l r) (hbn : b ≤ st.n)
    (c1 : ¬ (b ≤ l ∨ r ≤ a)) (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜OpPost H (fun _ => x) a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hkb := pos_bound H h _ _ hP
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._update_val_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [updAll_cpp]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨hv, ⟨hsz', hse⟩, hnn, hn0', hc⟩ := hpost
    unfold OpPost
    rw [hv]
    refine ⟨updval_cover x a b _ _ B hx hx1 hx2 _ _ _ [0] zs0 hI hS (by omega) (by rw [← hr']; exact c2.2)
      (by omega), ⟨hsz', hn0'.trans hn0, by omega, by omega⟩, hse, hnn, ?_⟩
    have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow; omega

theorem updval_rec_spec (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r → b ≤ st.n →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜OpPost H (fun _ => x) a b B h st k l t0 res c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hbn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact updval_skip_cpp H x a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact updval_cover_cpp H x a b B hx hx1 hx2 0 f st k l r t0 hpre hbn c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hbn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact updval_skip_cpp H x a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact updval_cover_cpp H x a b B hx hx1 hx2 (h + 1) f st k l r t0 hpre hbn c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [cp.SegmentTreeBeatsSum._update_val_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hinv1 := inner_pre1_0 _ _ B hB h _ _ hI hS
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp, upd_cpp]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold OpPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_ok (fun _ => x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_ok (fun _ => x) a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    refine ⟨rec_finish (fun _ => x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption), ⟨by assumption, ?_, ?_, ?_⟩,
      ?_, ?_, ?_⟩ <;> omega

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The hypotheses of `_add_val` at node `k`: the values stay within `B` also after adding `x`. -/
def AddPre (H : Nat) (B x : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) : Prop :=
  0 ≤ k ∧ 0 ≤ l ∧ r = l + 2 ^ h ∧ Pos H h k.toNat l.toNat ∧ Shape st H ∧
    Inv (view st) st.n.toNat h k.toNat l.toNat ∧ Safe (view st) st.n.toNat B h k.toNat l.toNat [0, x]

theorem safe_x0 (s : BS) (n : Nat) (B x : Int) (h k lo : Nat) (hS : Safe s n B h k lo [0, x]) :
    Safe s n B h k lo [0] := safe_mono s n B h k lo _ _ (by simp) hS

theorem addval_cover (x a b : Int) (s : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n h k lo) (hS : Safe s n B h k lo [0, x])
    (ha : a ≤ (lo : Int)) (hb : ((lo + 2 ^ h : Nat) : Int) ≤ b) (hbn : b ≤ (n : Int)) :
    RecPost (· + x) a b n B h k lo [0] s (addAll s k x) := by
  have hreal : lo + 2 ^ h ≤ n := by omega
  obtain ⟨uI, uT⟩ := addAll_node s n B hB h k lo [0, x] (by simp) hI hS hreal x (by simp)
  have hlen := len_T_le s n h k lo
  have hS' : Safe s n B h k lo (0 :: [0].map (· + x)) := by simpa using hS
  have hlv : 0 < h → s.lv k ≠ INF → s.lv k + x ≠ INF := by
    intro hh hl
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    exact lv_bound_of_inv s n B hB h' k lo [0, x] x (by simp) (by simp) hI hS hl
  refine ⟨uI, (safe_zeros _ _ _ _ _ _).mpr (safe_addAll s n B h k lo [0] x (by simp) hS' uT hlv), ?_,
    fun j hj => addAll_agree s k x j (fun e => hj (e ▸ sub_self _ _))⟩
  rw [uT, opL_all _ a b lo _ ha (by omega)]

theorem push_safe_x (s : BS) (n : Nat) (B x : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo [0, x]) :
    Safe (push s k) n B h (2 * k + 1) lo [0, x] ∧ Safe (push s k) n B h (2 * k + 2) (lo + 2 ^ h) [0, x] := by
  obtain ⟨-, p2, -, p4, p5, -⟩ := push_post s n B hB h k lo [0, x] (by simp) hI hS
  obtain ⟨q1, q2⟩ := p2.2 p5
  rw [p4, map_add_zero] at q1 q2
  exact ⟨safe_mono _ n B h _ _ _ _ (by simp) q1, safe_mono _ n B h _ _ _ _ (by simp) q2⟩

theorem child1_okx (st t2 : cp.SegmentTreeBeatsSum) (B x : Int) (hB : B < INF) (h : Nat) (k l : Int) (hk0 : 0 ≤ k)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0, x])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n) :
    Inv (view t2) t2.n.toNat h (2 * k + 1).toNat l.toNat ∧
      Safe (view t2) t2.n.toNat B h (2 * k + 1).toNat l.toNat [0, x] := by
  rw [hv, hn, toNat_2k1 k hk0]
  exact ⟨(inner_pre1_0 _ _ B hB h _ _ hI (safe_x0 _ _ _ _ _ _ _ hS)).1, (push_safe_x _ _ B x hB h _ _ hI hS).1⟩

theorem child2_okx (f : Int → Int) (a b : Int) (st t2 t3 : cp.SegmentTreeBeatsSum) (B x : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0, x])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost f a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3)) (hn3 : t3.n = t2.n) :
    Inv (view t3) t3.n.toNat h (2 * k + 2).toNat m.toNat ∧
      Safe (view t3) t3.n.toNat B h (2 * k + 2).toNat m.toNat [0, x] := by
  have := (child2_ok f a b st t2 t3 B hB h k l m hk0 hm hI (safe_x0 _ _ _ _ _ _ _ hS) hv hn hR3 hn3).1
  refine ⟨this, ?_⟩
  rw [hv, hn, toNat_2k1 k hk0] at hR3
  rw [hn3, hn, toNat_2k2 k hk0, hm]
  have hA : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k.toNat + 2) j → AgreeAt (push (view st) k.toNat) (view t3) j :=
    fun j hj => hR3.2.2.2 j (fun h1 => sub_siblings h _ j h1 hj)
  exact safe_frame _ _ _ B h _ _ _ hA (push_safe_x _ _ B x hB h _ _ hI hS).2

theorem addval_skip_cpp (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : AddPre H B x h st k l r) (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜OpPost H (· + x) a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._add_val_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI (safe_x0 _ _ _ _ _ _ _ hS) (opL_disjoint _ a b _ _ ?_),
    ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, ?_⟩
  · omega
  · have : 2 ≤ 2 ^ (h + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem addval_cover_cpp (H : Nat) (x a b B : Int) (hB : B < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat) (hpre : AddPre H B x h st k l r) (hbn : b ≤ st.n)
    (c1 : ¬ (b ≤ l ∨ r ≤ a)) (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜OpPost H (· + x) a b B h st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hkb := pos_bound H h _ _ hP
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._add_val_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [addAll_cpp]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨hv, ⟨hsz', hse⟩, hnn, hn0', hc⟩ := hpost
    unfold OpPost
    rw [hv]
    refine ⟨addval_cover x a b _ _ B hB _ _ _ hI hS (by omega) (by rw [← hr']; exact c2.2)
      (by omega), ⟨hsz', hn0'.trans hn0, by omega, by omega⟩, hse, hnn, ?_⟩
    have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow; omega

theorem addval_rec_spec (H : Nat) (x a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → AddPre H B x h st k l r → b ≤ st.n →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜OpPost H (· + x) a b B h st k l t0 res c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hbn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact addval_skip_cpp H x a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact addval_cover_cpp H x a b B hB 0 f st k l r t0 hpre hbn c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hbn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact addval_skip_cpp H x a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact addval_cover_cpp H x a b B hB (h + 1) f st k l r t0 hpre hbn c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [cp.SegmentTreeBeatsSum._add_val_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp, upd_cpp]
    all_goals try (show AddPre _ _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold OpPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_okx st _ B x hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_okx st _ B x hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_okx (· + x) a b st _ _ B x hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_okx (· + x) a b st _ _ B x hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    refine ⟨rec_finish (· + x) a b st _ _ _ _ B hB h k l _ hk0 hm hI (safe_x0 _ _ _ _ _ _ _ hS) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption), ⟨by assumption, ?_, ?_, ?_⟩,
      ?_, ?_, ?_⟩ <;> omega

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-! ## Range queries: the values outside `[a, b)` replaced by `d` -/

def maskL (d : Int) (a b : Int) (lo : Nat) (L : List Int) : List Int :=
  L.mapIdx (fun i v => if a ≤ ((lo + i : Nat) : Int) ∧ ((lo + i : Nat) : Int) < b then v else d)

theorem maskL_append' (d a b : Int) (lo m : Nat) (A B : List Int) (hAB : A.length = m ∨ B = []) :
    maskL d a b lo (A ++ B) = maskL d a b lo A ++ maskL d a b (lo + m) B := by
  simp only [maskL, List.mapIdx_append]
  rcases hAB with h | rfl
  · congr 1; congr 1; funext i v; rw [h, show lo + (i + m) = lo + m + i by omega]
  · simp

theorem maskL_all (d a b : Int) (lo : Nat) (L : List Int) (h1 : a ≤ lo) (h2 : lo + L.length ≤ b) :
    maskL d a b lo L = L := by
  apply List.ext_getElem (by simp [maskL])
  intro i h1' h2'
  simp only [maskL, List.getElem_mapIdx]
  rw [if_pos (by omega)]

theorem maskL_const (d a b : Int) (lo : Nat) (L : List Int) (h : b ≤ lo ∨ lo + L.length ≤ a) :
    ∀ v ∈ maskL d a b lo L, v = d := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  simp only [maskL, List.getElem_mapIdx]
  simp [maskL] at hi
  rw [if_neg (by omega)]

theorem lmax_maskL_disjoint (a b : Int) (lo : Nat) (L : List Int) (h : b ≤ lo ∨ lo + L.length ≤ a) :
    lmax (maskL (-INF) a b lo L) = -INF := by
  have := lmax_ge_ninf (maskL (-INF) a b lo L)
  have h2 := (lmax_le_iff (maskL (-INF) a b lo L) (-INF) le_rfl).mpr
    (fun v hv => le_of_eq (maskL_const _ a b lo L h v hv))
  omega

theorem lmin_maskL_disjoint (a b : Int) (lo : Nat) (L : List Int) (h : b ≤ lo ∨ lo + L.length ≤ a) :
    lmin (maskL INF a b lo L) = INF := by
  have := lmin_le_inf (maskL INF a b lo L)
  have h2 := (le_lmin_iff (maskL INF a b lo L) INF le_rfl).mpr
    (fun v hv => ge_of_eq (maskL_const _ a b lo L h v hv))
  omega

/-- The tree invariant at `k` after its children changed without changing their values. -/
theorem inv_lift (s t : BS) (n h k lo : Nat) (hI : Inv s n (h + 1) k lo) (hk : AgreeAt s t k)
    (h1 : T t n h (2 * k + 1) lo = T s n h (2 * k + 1) lo) (h2 : T t n h (2 * k + 2) (lo + 2 ^ h) = T s n h (2 * k + 2) (lo + 2 ^ h))
    (hI1 : Inv t n h (2 * k + 1) lo) (hI2 : Inv t n h (2 * k + 2) (lo + 2 ^ h)) :
    Inv t n (h + 1) k lo ∧ T t n (h + 1) k lo = T s n (h + 1) k lo := by
  obtain ⟨-, -, i3, i4, i5, i6, i7⟩ := hI
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hk
  have hT : T t n (h + 1) k lo = T s n (h + 1) k lo := by
    simp only [T, h1, h2]; congr 1; funext v; simp [tau, a1, a4, a8]
  refine ⟨⟨hI1, hI2, ?_, by rw [← a7]; exact i4, by rw [← a8, ← a9]; exact i5, ?_, ?_⟩, hT⟩
  · unfold SummK at *; rw [hT, ← a1, ← a2, ← a3, ← a4, ← a5, ← a6]; exact i3
  · rw [← a1, ← a4, ← a8, ← a9]; exact i6
  · rw [h1, h2]; unfold ChildOK; rw [← a1, ← a4, ← a8, ← a9]; exact i7

/-- A query visited both children after `push(k)`: the tree is still valid and its values are unchanged. -/
theorem query_inner (s s3 s4 : BS) (n : Nat) (B : Int) (hB : B < INF) (h k lo : Nat)
    (hI : Inv s n (h + 1) k lo) (hS : Safe s n B (h + 1) k lo [0])
    (h3 : RecPost id a b n B h (2 * k + 1) lo [0] (push s k) s3)
    (h4 : RecPost id a b n B h (2 * k + 2) (lo + 2 ^ h) [0] s3 s4) :
    RecPost id a b n B (h + 1) k lo [0] s s4 ∧
      T s n (h + 1) k lo = T (push s k) n h (2 * k + 1) lo ++ T s3 n h (2 * k + 2) (lo + 2 ^ h) := by
  obtain ⟨p1, p2, p3, p4, p5, -, -, -, -, -, -, -, p13, p14, p15⟩ := push_post s n B hB h k lo [0] (by simp) hI hS
  obtain ⟨r3I, r3S, r3T, r3A⟩ := h3
  obtain ⟨r4I, r4S, r4T, r4A⟩ := h4
  set s2 := push s k
  have nk1 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → j ≠ k := fun j hj => notsub_k h k j (Or.inl hj)
  have nk2 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → j ≠ k := fun j hj => notsub_k h k j (Or.inr hj)
  have a43 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt s3 s4 j :=
    fun j hj => r4A j (fun h2 => sub_siblings h k j hj h2)
  have a23 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt s2 s3 j :=
    fun j hj => r3A j (fun h1 => sub_siblings h k j h1 hj)
  have ak : AgreeAt s2 s4 k := agree_trans _ _ _ k (r3A k (fun h1 => nk1 k h1 rfl)) (r4A k (fun h2 => nk2 k h2 rfl))
  have hid : ∀ L : List Int, ∀ m, opL id a b m L = L := fun L m => opL_fix _ a b m L (fun _ _ => rfl)
  have c1T : T s4 n h (2 * k + 1) lo = T s2 n h (2 * k + 1) lo := by
    rw [← T_frame _ _ n h _ _ a43, r3T, hid]
  have c2T0 : T s3 n h (2 * k + 2) (lo + 2 ^ h) = T s2 n h (2 * k + 2) (lo + 2 ^ h) := (T_frame _ _ n h _ _ a23).symm
  have c2T : T s4 n h (2 * k + 2) (lo + 2 ^ h) = T s2 n h (2 * k + 2) (lo + 2 ^ h) := by rw [r4T, hid, c2T0]
  obtain ⟨uI, uT⟩ := inv_lift s2 s4 n h k lo p1 ak c1T c2T (inv_frame _ _ n h _ _ a43 r3I) r4I
  have hsplit : T s n (h + 1) k lo = T s2 n h (2 * k + 1) lo ++ T s2 n h (2 * k + 2) (lo + 2 ^ h) := by
    rw [p14, p15]; simp only [T, List.map_append]
  refine ⟨⟨uI, ?_, by rw [uT, p3, hid], ?_⟩, by rw [hsplit, c2T0]⟩
  · obtain ⟨-, -, -, -, -, -, -, k8, k9⟩ := ak
    refine ⟨fun o ho v hv => ?_, fun hl => ?_⟩
    · rw [uT] at hv; exact p2.1 o ho v hv
    · rw [← k8, p4, map_add_zero]
      exact ⟨(safe_zeros _ _ _ _ _ _).mp (safe_frame _ _ n B h _ _ _ a43 r3S), (safe_zeros _ _ _ _ _ _).mp r4S⟩
  · intro j hj
    have j0 : j ≠ k := fun e => hj (e ▸ sub_self _ _)
    have j1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j := fun e => hj (sub_child1 h k j e)
    have j2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j := fun e => hj (sub_child2 h k j e)
    exact agree_trans _ _ _ j (p13 j j0 (fun e => j1 (e ▸ sub_self _ _)) (fun e => j2 (e ▸ sub_self _ _)))
      (agree_trans _ _ _ j (r3A j j1) (r4A j j2))

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The postcondition of `_calc_max` at node `k`: the answer and an unchanged sequence. -/
def QPost (H : Nat) (a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat) (q : Int)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost id a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    q = lmax (maskL (-INF) a b l.toNat (T (view st) st.n.toNat h k.toNat l.toNat)) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1)

theorem two_le_pow (h : Nat) : 2 ≤ 2 ^ (h + 1) := by
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem qmax_skip_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_max_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)),
    (lmax_maskL_disjoint a b _ _ (by omega)).symm, ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega⟩

theorem qmax_cover_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : ¬ (b ≤ l ∨ r ≤ a)) (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_max_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)), ?_,
    ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega⟩
  rw [maskL_all _ a b _ _ (by omega) (by omega), ← (inv_summ _ _ _ _ _ hI).mx]
  rfl

theorem qmax_finish (a b : Int) (st t2 t3 t4 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (q1 q2 : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost id a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hq1 : q1 = lmax (maskL (-INF) a b l.toNat (T (view t2) t2.n.toNat h (2 * k + 1).toNat l.toNat)))
    (hn3 : t3.n = t2.n)
    (hR4 : RecPost id a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4))
    (hq2 : q2 = lmax (maskL (-INF) a b m.toNat (T (view t3) t3.n.toNat h (2 * k + 2).toNat m.toNat))) :
    RecPost id a b st.n.toNat B (h + 1) k.toNat l.toNat [0] (view st) (view t4) ∧
      max q1 q2 = lmax (maskL (-INF) a b l.toNat (T (view st) st.n.toNat (h + 1) k.toNat l.toNat)) := by
  rw [hv, hn, toNat_2k1 k hk0] at hR3 hq1
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4 hq2
  obtain ⟨hR, hsplit⟩ := query_inner _ _ _ _ B hB h _ _ hI hS hR3 hR4
  refine ⟨hR, ?_⟩
  rw [hsplit, maskL_append' _ a b _ (2 ^ h), lmax_append, hq1, hq2]
  simp only [T_length]
  by_cases hn' : 2 ^ h ≤ st.n.toNat - l.toNat
  · left; omega
  · right; apply List.eq_nil_of_length_eq_zero; rw [T_length]; omega

theorem qmax_rec_spec (H : Nat) (a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec fuel st a b k l r
      ⦃⇓ p c => ⌜QPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qmax_skip_cpp H a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qmax_cover_cpp H a b B 0 f st k l r t0 hpre c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qmax_skip_cpp H a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qmax_cover_cpp H a b B (h + 1) f st k l r t0 hpre c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_max_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold QPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_ok id a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_ok id a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    obtain ⟨hA, hQ⟩ := qmax_finish a b st _ _ _ B hB h k l _ _ _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    exact ⟨hA, hQ, ⟨by assumption, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

/-- The postcondition of `_calc_min` at node `k`: the answer and an unchanged sequence. -/
def QPostMin (H : Nat) (a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat) (q : Int)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost id a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    q = lmin (maskL INF a b l.toNat (T (view st) st.n.toNat h k.toNat l.toNat)) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1)

theorem qmin_skip_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QPostMin H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_min_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)),
    (lmin_maskL_disjoint a b _ _ (by omega)).symm, ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega⟩

theorem qmin_cover_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (c1 : ¬ (b ≤ l ∨ r ≤ a)) (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QPostMin H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_min_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)), ?_,
    ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega⟩
  rw [maskL_all _ a b _ _ (by omega) (by omega), ← (inv_summ _ _ _ _ _ hI).mn]
  rfl

theorem qmin_finish (a b : Int) (st t2 t3 t4 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (q1 q2 : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost id a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hq1 : q1 = lmin (maskL INF a b l.toNat (T (view t2) t2.n.toNat h (2 * k + 1).toNat l.toNat)))
    (hn3 : t3.n = t2.n)
    (hR4 : RecPost id a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4))
    (hq2 : q2 = lmin (maskL INF a b m.toNat (T (view t3) t3.n.toNat h (2 * k + 2).toNat m.toNat))) :
    RecPost id a b st.n.toNat B (h + 1) k.toNat l.toNat [0] (view st) (view t4) ∧
      min q1 q2 = lmin (maskL INF a b l.toNat (T (view st) st.n.toNat (h + 1) k.toNat l.toNat)) := by
  rw [hv, hn, toNat_2k1 k hk0] at hR3 hq1
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4 hq2
  obtain ⟨hR, hsplit⟩ := query_inner _ _ _ _ B hB h _ _ hI hS hR3 hR4
  refine ⟨hR, ?_⟩
  rw [hsplit, maskL_append' _ a b _ (2 ^ h), lmin_append, hq1, hq2]
  simp only [T_length]
  by_cases hn' : 2 ^ h ≤ st.n.toNat - l.toNat
  · left; omega
  · right; apply List.eq_nil_of_length_eq_zero; rw [T_length]; omega

theorem qmin_rec_spec (H : Nat) (a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec fuel st a b k l r
      ⦃⇓ p c => ⌜QPostMin H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qmin_skip_cpp H a b B 0 f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qmin_cover_cpp H a b B 0 f st k l r t0 hpre c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qmin_skip_cpp H a b B (h + 1) f st k l r t0 hpre c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qmin_cover_cpp H a b B (h + 1) f st k l r t0 hpre c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_min_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
    have hinner : k < st.n0 - 1 := by omega
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ih, push_cpp]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold QPostMin at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [hinner, forall_const, not_le.mpr hinner, false_implies] at *
    all_goals first
      | omega
      | (intro; omega)
      | assumption
      | (rw [hdiv]; omega)
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | omega)
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).1
      | exact (child1_ok st _ B hB h k l hk0 hI hS (by assumption) (by assumption)).2
      | exact (child2_ok id a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).1
      | exact (child2_ok id a b st _ _ B hB h k l _ hk0 hm hI hS (by assumption) (by assumption)
          (by assumption) (by assumption)).2
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    obtain ⟨hA, hQ⟩ := qmin_finish a b st _ _ _ B hB h k l _ _ _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    exact ⟨hA, hQ, ⟨by assumption, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-! ## Building the tree from the input -/

/-- The input values at the real leaves `[lo, lo + 2 ^ h)`. -/
def leafL (a : Array Int) (n lo h : Nat) : List Int :=
  (List.range (min (2 ^ h) (n - lo))).map (fun i => a[lo + i]!)

theorem leafL_succ (a : Array Int) (n lo h : Nat) :
    leafL a n lo (h + 1) = leafL a n lo h ++ leafL a n (lo + 2 ^ h) h := by
  unfold leafL
  by_cases hn : 2 ^ h ≤ n - lo
  · have e : min (2 ^ (h + 1)) (n - lo) = 2 ^ h + min (2 ^ h) (n - (lo + 2 ^ h)) := by rw [pow_succ]; omega
    rw [e, List.range_add, List.map_append, List.map_map, min_eq_left hn]
    congr 1
    apply List.map_congr_left; intro i _; simp [Nat.add_assoc]
  · have e1 : min (2 ^ (h + 1)) (n - lo) = n - lo := by rw [pow_succ]; omega
    have e2 : min (2 ^ h) (n - (lo + 2 ^ h)) = 0 := by omega
    rw [e1, e2, min_eq_right (by omega)]; simp

def Bnd (a : Array Int) (n : Nat) (B : Int) : Prop := ∀ i < n, |a[i]!| ≤ B

theorem leafL_bound (a : Array Int) (n lo h : Nat) (B : Int) (hA : Bnd a n B) : ∀ v ∈ leafL a n lo h, |v| ≤ B := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  simp at hi
  exact hA _ (by omega)

/-- The children are built and `update(k)` combines them. -/
theorem build_inner (a : Array Int) (n : Nat) (B : Int) (hB : B < INF) (hA : Bnd a n B) (h k lo : Nat)
    (s t1 t2 : BS) (hla : s.la k = 0) (hlv : s.lv k = INF) (hlen : s.len k = 2 ^ (h + 1))
    (h1 : Inv t1 n h (2 * k + 1) lo ∧ Safe t1 n B h (2 * k + 1) lo [0] ∧ T t1 n h (2 * k + 1) lo = leafL a n lo h ∧
      ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt s t1 j)
    (h2 : Inv t2 n h (2 * k + 2) (lo + 2 ^ h) ∧ Safe t2 n B h (2 * k + 2) (lo + 2 ^ h) [0] ∧
      T t2 n h (2 * k + 2) (lo + 2 ^ h) = leafL a n (lo + 2 ^ h) h ∧ ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j → AgreeAt t1 t2 j) :
    Inv (upd t2 k) n (h + 1) k lo ∧ Safe (upd t2 k) n B (h + 1) k lo [0] ∧
      T (upd t2 k) n (h + 1) k lo = leafL a n lo (h + 1) ∧ ∀ j, ¬ SegmentTreeBeatsMath.Sub (h + 1) k j → AgreeAt s (upd t2 k) j := by
  obtain ⟨r1I, r1S, r1T, r1A⟩ := h1
  obtain ⟨r2I, r2S, r2T, r2A⟩ := h2
  have nk1 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → j ≠ k := fun j hj => notsub_k h k j (Or.inl hj)
  have nk2 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 2) j → j ≠ k := fun j hj => notsub_k h k j (Or.inr hj)
  have a21 : ∀ j, SegmentTreeBeatsMath.Sub h (2 * k + 1) j → AgreeAt t1 t2 j := fun j hj => r2A j (fun h2 => sub_siblings h k j hj h2)
  have a5 : ∀ j, j ≠ k → AgreeAt t2 (upd t2 k) j := upd_agree t2 k
  have ak : AgreeAt s t2 k := agree_trans _ _ _ k (r1A k (fun h1 => nk1 k h1 rfl)) (r2A k (fun h2 => nk2 k h2 rfl))
  obtain ⟨-, -, -, -, -, -, k7, k8, k9⟩ := ak
  have c1I : Inv t2 n h (2 * k + 1) lo := inv_frame _ _ n h _ _ a21 r1I
  have c1S : Safe t2 n B h (2 * k + 1) lo [0] := safe_frame _ _ n B h _ _ _ a21 r1S
  have c1T : T t2 n h (2 * k + 1) lo = T t1 n h (2 * k + 1) lo := (T_frame _ _ n h _ _ a21).symm
  have hR1 : InR (T t2 n h (2 * k + 1) lo) := inR_zero _ (safe_inR _ n B hB h _ _ _ c1S 0 (by simp))
  have hR2 : InR (T t2 n h (2 * k + 2) (lo + 2 ^ h)) := inR_zero _ (safe_inR _ n B hB h _ _ _ r2S 0 (by simp))
  obtain ⟨uI, uT⟩ := upd_spec t2 n h k lo c1I r2I hR1 hR2 (k8 ▸ hla) (k9 ▸ hlv) (k7 ▸ hlen)
  refine ⟨uI, ?_, by rw [uT, c1T, r1T, r2T, leafL_succ], ?_⟩
  · refine ⟨fun o ho v hv => ?_, fun _ => ?_⟩
    · simp at ho; subst ho
      rw [uT, c1T, r1T, r2T, ← leafL_succ] at hv
      simpa using leafL_bound a n lo (h + 1) B hA v hv
    · have hla' : (upd t2 k).la k = 0 := by simp only [upd]; exact k8 ▸ hla
      rw [hla', map_add_zero]
      exact ⟨(safe_zeros _ _ _ _ _ _).mp (safe_frame _ _ n B h _ _ _ (fun j hj => a5 j (nk1 j hj)) c1S),
        (safe_zeros _ _ _ _ _ _).mp (safe_frame _ _ n B h _ _ _ (fun j hj => a5 j (nk2 j hj)) r2S)⟩
  · intro j hj
    have j0 : j ≠ k := fun e => hj (e ▸ sub_self _ _)
    have j1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j := fun e => hj (sub_child1 h k j e)
    have j2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j := fun e => hj (sub_child2 h k j e)
    exact agree_trans _ _ _ j (r1A j j1) (agree_trans _ _ _ j (r2A j j2) (a5 j j0))

/-- The fields a leaf gets in `_build`. -/
def leafSet (s : BS) (k : Nat) (v : Int) (real : Prop) [Decidable real] : BS :=
  { s with mx := upF s.mx k (if real then v else -INF), sx := upF s.sx k (-INF),
           cx := upF s.cx k (if real then 1 else 0), mn := upF s.mn k (if real then v else INF),
           sn := upF s.sn k INF, cn := upF s.cn k (if real then 1 else 0), len := upF s.len k 1,
           la := upF s.la k 0, lv := upF s.lv k INF }

theorem leafSet_agree (s : BS) (k : Nat) (v : Int) (real : Prop) [Decidable real] :
    ∀ j, j ≠ k → AgreeAt s (leafSet s k v real) j := by
  intro j hj; simp [AgreeAt, leafSet, upF, hj]

theorem leaf_post (a : Array Int) (n : Nat) (B : Int) (hB : B < INF) (hA : Bnd a n B) (k lo : Nat) (s : BS) :
    Inv (leafSet s k a[lo]! (lo < n)) n 0 k lo ∧ Safe (leafSet s k a[lo]! (lo < n)) n B 0 k lo [0] ∧
      T (leafSet s k a[lo]! (lo < n)) n 0 k lo = leafL a n lo 0 ∧
      ∀ j, ¬ SegmentTreeBeatsMath.Sub 0 k j → AgreeAt s (leafSet s k a[lo]! (lo < n)) j := by
  refine ⟨?_, ?_, ?_, fun j hj => leafSet_agree s k _ _ j (fun e => hj (by simp [SegmentTreeBeatsMath.Sub, e]))⟩
  · refine ⟨?_, by simp [leafSet, upF]⟩
    unfold SummK
    simp only [T, leafSet, upF, if_true]
    by_cases hl : lo < n
    · have hb := hA lo hl
      have hx : -INF < a[lo]! ∧ a[lo]! < INF := by
        constructor <;> [have := neg_abs_le a[lo]!; have := le_abs_self a[lo]!] <;> omega
      simpa [hl] using summ_replicate 1 a[lo]! le_rfl hx
    · simpa [hl] using summ_nil
  · intro o ho v hv
    simp at ho; subst ho
    simp only [T, leafSet, upF, if_true] at hv
    split_ifs at hv with hl
    · simp at hv; subst hv; simpa using hA lo hl
    · simp at hv
  · simp only [T, leafSet, upF, if_true, leafL]
    by_cases hl : lo < n
    · simp [hl, show min 1 (n - lo) = 1 by omega]
    · simp [hl, show n - lo = 0 by omega]

def BuildPre (H : Nat) (B : Int) (a : Array Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) : Prop :=
  0 ≤ k ∧ 0 ≤ l ∧ r = l + 2 ^ h ∧ Pos H h k.toNat l.toNat ∧ Shape st H ∧ Bnd a st.n.toNat B

def BuildPost (H : Nat) (B : Int) (a : Array Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  Inv (view res) st.n.toNat h k.toNat l.toNat ∧ Safe (view res) st.n.toNat B h k.toNat l.toNat [0] ∧
    T (view res) st.n.toNat h k.toNat l.toNat = leafL a st.n.toNat l.toNat h ∧
    (∀ j, ¬ SegmentTreeBeatsMath.Sub h k.toNat j → AgreeAt (view st) (view res) j) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 2 ≤ t0 + 2 * 2 ^ (h + 1)

set_option maxHeartbeats 2000000 in
theorem build_leaf_cpp (H : Nat) (B : Int) (hB : B < INF) (a : Array Int) (f : Nat) (st : cp.SegmentTreeBeatsSum)
    (k l r : Int) (t0 : Nat) (hpre : BuildPre H B a 0 st k l r) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build_rec (f + 1) st a k l r
    ⦃⇓ res c => ⌜BuildPost H B a 0 st k l t0 res c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hA⟩ := hpre
  have hkb := pos_bound H 0 _ _ hP
  have hd : decide (r - l = 1) = true := by simp [hr]
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y1 : k.toNat < st.max_v.size := by omega
  have y2 : k.toNat < st.smax_v.size := by omega
  have y3 : k.toNat < st.max_c.size := by omega
  have y4 : k.toNat < st.min_v.size := by omega
  have y5 : k.toNat < st.smin_v.size := by omega
  have y6 : k.toNat < st.min_c.size := by omega
  have y7 : k.toNat < st.len.size := by omega
  have y8 : k.toNat < st.ladd.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  have y10 : k.toNat < st.sum.size := by omega
  have hrl : r - l = 1 := by simp [hr]
  have hv : ∀ res : cp.SegmentTreeBeatsSum, view res = leafSet (view st) k.toNat a[l.toNat]! (l.toNat < st.n.toNat) →
      SzE res → res.max_v.size = st.max_v.size → res.n = st.n → res.n0 = st.n0 →
      ∀ c, c = t0 + 1 → BuildPost H B a 0 st k l t0 res c := by
    intro res hvr hs hse hnn hn0' c hc
    unfold BuildPost
    simp only [zero_add, pow_one]
    obtain ⟨p1, p2, p3, p4⟩ := leaf_post a st.n.toNat B hB hA k.toNat l.toNat (view st)
    rw [hvr]
    exact ⟨p1, p2, p3, p4, ⟨hs, by omega, by omega, by omega⟩, hse, hnn, by omega⟩
  by_cases hl : l < st.n
  · have hd2 : decide (l < st.n) = true := by simp [hl]
    simp only [cp.SegmentTreeBeatsSum._build_rec, hd, hd2, ite_true]
    mvcgen
    rename_i c hc
    have hl' : l.toNat < st.n.toNat := by omega
    apply hv
    rotate_left
    · simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10]
    · simp
    · rfl
    · rfl
    · omega
    dsimp only [view_mk, leafSet, view, upF]
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y2, getElemBang_set _ _ _ _ y3,
      getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y5, getElemBang_set _ _ _ _ y6,
      getElemBang_set _ _ _ _ y7, getElemBang_set _ _ _ _ y8, getElemBang_set _ _ _ _ y9, getElemBang_set _ _ _ _ y10, get_eq, cinf, hrl,
      size_set, if_true, hl', ite_true]
    rfl
  · have hd2 : decide (l < st.n) = false := by simp [hl]
    simp only [cp.SegmentTreeBeatsSum._build_rec, hd, hd2, ite_true, Bool.false_eq_true, ite_false]
    mvcgen
    rename_i c hc
    have hl' : ¬ l.toNat < st.n.toNat := by omega
    apply hv
    rotate_left
    · simp [SzE, Sz, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10]
    · simp
    · rfl
    · rfl
    · omega
    dsimp only [view_mk, leafSet, view, upF]
    simp only [getElemBang_set _ _ _ _ y1, getElemBang_set _ _ _ _ y2, getElemBang_set _ _ _ _ y3,
      getElemBang_set _ _ _ _ y4, getElemBang_set _ _ _ _ y5, getElemBang_set _ _ _ _ y6,
      getElemBang_set _ _ _ _ y7, getElemBang_set _ _ _ _ y8, getElemBang_set _ _ _ _ y9, getElemBang_set _ _ _ _ y10, get_eq, cinf, hrl,
      size_set, if_true, hl', ite_true, ite_false]
    rfl

/-- The object after `_build` wrote the tags and the length of node `k`. -/
def preBuild (st : cp.SegmentTreeBeatsSum) (k l r : Int) : cp.SegmentTreeBeatsSum :=
  ⟨st.n, st.n0, st.max_v, st.smax_v, st.max_c, st.min_v, st.smin_v, st.min_c, st.sum, Cpp.set st.len k (r - l),
    Cpp.set st.ladd k 0, Cpp.set st.lval k cp.SegmentTreeBeatsSum_INF⟩

theorem preBuild_n (st : cp.SegmentTreeBeatsSum) (k l r : Int) : (preBuild st k l r).n = st.n := rfl
theorem preBuild_n0 (st : cp.SegmentTreeBeatsSum) (k l r : Int) : (preBuild st k l r).n0 = st.n0 := rfl
theorem preBuild_size (st : cp.SegmentTreeBeatsSum) (k l r : Int) :
    (preBuild st k l r).max_v.size = st.max_v.size := rfl

theorem preBuild_facts (st : cp.SegmentTreeBeatsSum) (k l r : Int) (hk0 : 0 ≤ k) (hsz : SzE st)
    (hk : k.toNat < st.max_v.size) :
    (view (preBuild st k l r)).la k.toNat = 0 ∧ (view (preBuild st k l r)).lv k.toNat = INF ∧
      (view (preBuild st k l r)).len k.toNat = r - l ∧
      ∀ j, j ≠ k.toNat → AgreeAt (view st) (view (preBuild st k l r)) j := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
  have y7 : k.toNat < st.len.size := by omega
  have y8 : k.toNat < st.ladd.size := by omega
  have y9 : k.toNat < st.lval.size := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [view, preBuild, getElemBang_set _ _ _ _ y8]
  · simp [view, preBuild, getElemBang_set _ _ _ _ y9, cinf]
  · simp [view, preBuild, getElemBang_set _ _ _ _ y7]
  · intro j hj
    simp [AgreeAt, view, preBuild, getElemBang_set _ _ _ _ y7, getElemBang_set _ _ _ _ y8,
      getElemBang_set _ _ _ _ y9, hj]

theorem build_finish (a : Array Int) (B : Int) (hB : B < INF) (h : Nat) (st t1 t2 t3 : cp.SegmentTreeBeatsSum)
    (k l r m : Int) (hk0 : 0 ≤ k) (hr : r - l = 2 ^ (h + 1)) (hm : m.toNat = l.toNat + 2 ^ h) (hsz : SzE st)
    (hk : k.toNat < st.max_v.size) (hA : Bnd a st.n.toNat B)
    (h1I : Inv (view t1) st.n.toNat h (2 * k + 1).toNat l.toNat)
    (h1S : Safe (view t1) st.n.toNat B h (2 * k + 1).toNat l.toNat [0])
    (h1T : T (view t1) st.n.toNat h (2 * k + 1).toNat l.toNat = leafL a st.n.toNat l.toNat h)
    (h1A : ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1).toNat j → AgreeAt (view (preBuild st k l r)) (view t1) j)
    (hn1 : t1.n = st.n)
    (h2I : Inv (view t2) t1.n.toNat h (2 * k + 2).toNat m.toNat)
    (h2S : Safe (view t2) t1.n.toNat B h (2 * k + 2).toNat m.toNat [0])
    (h2T : T (view t2) t1.n.toNat h (2 * k + 2).toNat m.toNat = leafL a t1.n.toNat m.toNat h)
    (h2A : ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2).toNat j → AgreeAt (view t1) (view t2) j)
    (hv3 : view t3 = upd (view t2) k.toNat) :
    Inv (view t3) st.n.toNat (h + 1) k.toNat l.toNat ∧ Safe (view t3) st.n.toNat B (h + 1) k.toNat l.toNat [0] ∧
      T (view t3) st.n.toNat (h + 1) k.toNat l.toNat = leafL a st.n.toNat l.toNat (h + 1) ∧
      ∀ j, ¬ SegmentTreeBeatsMath.Sub (h + 1) k.toNat j → AgreeAt (view st) (view t3) j := by
  rw [toNat_2k1 k hk0] at h1I h1S h1T h1A
  rw [toNat_2k2 k hk0, hm, hn1] at h2I h2S h2T
  rw [toNat_2k2 k hk0] at h2A
  obtain ⟨f1, f2, f3, f4⟩ := preBuild_facts st k l r hk0 hsz hk
  obtain ⟨b1, b2, b3, b4⟩ := build_inner a st.n.toNat B hB hA h k.toNat l.toNat _ _ _ f1 f2 (by rw [f3, hr])
    ⟨h1I, h1S, h1T, h1A⟩ ⟨h2I, h2S, h2T, h2A⟩
  rw [hv3]
  exact ⟨b1, b2, b3, fun j hj => agree_trans _ _ _ j (f4 j (fun e => hj (e ▸ sub_self _ _))) (b4 j hj)⟩

theorem build_rec_spec (H : Nat) (B : Int) (hB : B < INF) (a : Array Int) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → BuildPre H B a h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build_rec fuel st a k l r
      ⦃⇓ res c => ⌜BuildPost H B a h st k l t0 res c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact build_leaf_cpp H B hB a f st k l r t0 hpre
  | succ h ih =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hA⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have hpow : (2 : Int) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ h := by positivity
    have hd : decide (r - l = 1) = false := by simp; omega
    simp only [cp.SegmentTreeBeatsSum._build_rec, hd, Bool.false_eq_true, ite_false]
    have hdiv : Cpp.div (l + r) 2 = l + 2 ^ h := by rw [hr]; exact div_mid l h hl0
    have p1 := pos_child1 H h _ _ hP
    have p2 := pos_child2 H h _ _ hP
    rw [← toNat_2k1 k hk0] at p1
    rw [← toNat_2k2 k hk0, ← toNat_add_pow l h hl0, ← hdiv] at p2
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    have hrl : r - l = 2 ^ (h + 1) := by omega
    have hkb : k.toNat < st.max_v.size := by omega
    have hszP : SzE (preBuild st k l r) := by
      obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hsz
      simp [SzE, Sz, preBuild, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10]
    have hfold : (⟨st.n, st.n0, st.max_v, st.smax_v, st.max_c, st.min_v, st.smin_v, st.min_c, st.sum, Cpp.set st.len k (r - l),
        Cpp.set st.ladd k 0, Cpp.set st.lval k cp.SegmentTreeBeatsSum_INF⟩ : cp.SegmentTreeBeatsSum) = preBuild st k l r := rfl
    mvcgen [ih, upd_cpp]
    all_goals try simp only [hfold] at *
    all_goals try (show BuildPre _ _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold BuildPost at *
    all_goals try unfold Shape at *
    all_goals try casesm* _ ∧ _
    all_goals try simp only [preBuild_n, preBuild_n0, preBuild_size, st_eta] at *
    all_goals first
      | omega
      | assumption
      | (rw [hdiv]; omega)
      | exact hszP
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | assumption | exact hszP | (simp [preBuild]; omega) | omega)
      | (simp only [preBuild]; exact hA)
      | (unfold Bnd at *; intro i hi; exact hA i (by omega))
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    obtain ⟨b1, b2, b3, b4⟩ := build_finish a B hB h st _ _ _ k l r _ hk0 hrl hm hsz hkb hA (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
    exact ⟨b1, b2, b3, b4, ⟨by assumption, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The object holds the values `vals` (and every value with any pending add stays within `B`). -/
def Valid (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) : Prop :=
  ∃ H, Shape st H ∧ st.n.toNat = vals.length ∧ 1 ≤ vals.length ∧ 2 ^ H < 2 * vals.length ∧ H < Cpp.fuel ∧ B < INF ∧
    Inv (view st) st.n.toNat H 0 0 ∧ Safe (view st) st.n.toNat B H 0 0 [0] ∧ T (view st) st.n.toNat H 0 0 = vals

theorem build_spec (B : Int) (hB : B < INF) (a : Array Int) (st : cp.SegmentTreeBeatsSum) (r : Int) (t0 : Nat)
    (hH : r.toNat.log2 < Cpp.fuel) (hpre : BuildPre r.toNat.log2 B a r.toNat.log2 st 0 0 r) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build st a 0 0 r
    ⦃⇓ res c => ⌜BuildPost r.toNat.log2 B a r.toNat.log2 st 0 0 t0 res c⌝⦄ :=
  build_rec_spec _ B hB a _ _ st 0 0 r t0 hH hpre

theorem leafL_root (a : Array Int) (H : Nat) (hn : a.size ≤ 2 ^ H) : leafL a a.size 0 H = a.toList := by
  apply List.ext_getElem (by simp [leafL]; omega)
  intro i h1 h2
  have : i < a.size := by simpa using h2
  simp [leafL, getElem!_pos a i this]

theorem toNat_two_pow (r : Int) (j : Nat) (h : r = 2 ^ j) : r.toNat = 2 ^ j ∧ r.toNat.log2 = j := by
  have : r.toNat = 2 ^ j := by
    rw [h, show (2 : Int) ^ j = ((2 ^ j : Nat) : Int) by push_cast; ring, Int.toNat_natCast]
  exact ⟨this, by rw [this, Nat.log2_two_pow]⟩

theorem pow_lt_of_pred (j n : Nat) (hj : 0 < j → 2 ^ (j - 1) < n) (hn : 1 ≤ n) : 2 ^ j < 2 * n ∨ j = 0 := by
  rcases j with _ | j
  · right; rfl
  · left; have := hj (by omega); rw [pow_succ]; simp at this; omega

theorem j_facts (j n : Nat) (hj : 0 < j → (2 : Int) ^ (j - 1) < n) (hn1 : 1 ≤ n) :
    j ≤ n ∧ 2 * 2 ^ j ≤ 4 * n ∧ 2 ^ j < 2 * n := by
  rcases j with _ | j
  · simp; omega
  · have h := hj (by omega)
    simp only [Nat.add_sub_cancel] at h
    have e : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; ring
    have h' : 2 ^ j < n := by omega
    have : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]; omega

theorem init_spec (a : Array Int) (B : Int) (hB : B < INF) (hA : Bnd a a.size B) (h1 : 1 ≤ a.size)
    (h2 : a.size ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.init a
    ⦃⇓ r c => ⌜Valid r a.toList B ∧ c ≤ t0 + 50 * a.size + 10⌝⦄ := by
  have bs := build_spec B hB a
  mvcgen [cp.SegmentTreeBeatsSum.init, bs]
  case inv =>
    exact { cont := fun b => fun c => ⌜∃ j : Nat, b = 2 ^ j ∧ (0 < j → (2 : Int) ^ (j - 1) < a.size) ∧
              c = t0 + 1 + 40 * a.size + j⌝,
            done := fun b => fun c => ⌜∃ j : Nat, b = 2 ^ j ∧ (a.size : Int) ≤ 2 ^ j ∧
              (0 < j → (2 : Int) ^ (j - 1) < a.size) ∧ c = t0 + 1 + 40 * a.size + j + 1⌝,
            measure := fun b => (a.size - b).toNat }
  have e4 : (4 * (a.size : Int)).toNat = 4 * a.size := by omega
  case vc2.step.isTrue =>
    rename_i b c hc hb
    simp +zetaDelta [Cpp.size] at hc hb ⊢
    obtain ⟨j, hj, hj1, hcj⟩ := hc
    exact ⟨j, hj, by omega, hj1, by omega⟩
  case vc3.step.isFalse =>
    rename_i b c hc hb n0
    simp +zetaDelta [Cpp.size, Cpp.shl] at hc hb ⊢
    obtain ⟨j, hj, hj1, hcj⟩ := hc
    have hpos : (0 : Int) < 2 ^ j := by positivity
    refine ⟨⟨j + 1, by rw [hj, pow_succ], fun _ => by simpa [hj] using hb, by omega⟩, by omega⟩
  case vc4.pre =>
    rename_i c hc
    simp +zetaDelta [Cpp.size, Cpp.replicate, Cpp.fuel]
    refine ⟨⟨0, by simp, by simp, by omega⟩, by omega⟩
  case vc5.hH =>
    rename_i r c hc
    simp +zetaDelta [Cpp.size] at hc
    obtain ⟨j, hj, -, hj1, -⟩ := hc
    rw [(toNat_two_pow r j hj).2]
    have := (j_facts j a.size hj1 h1).1
    simp [Cpp.fuel]; omega
  case vc6.hpre =>
    rename_i r c hc
    simp +zetaDelta [Cpp.size] at hc
    obtain ⟨j, hj, hn, hj1, -⟩ := hc
    rw [(toNat_two_pow r j hj).2]
    obtain ⟨-, h4, -⟩ := j_facts j a.size hj1 h1
    refine ⟨le_rfl, le_rfl, by simp [hj], ⟨by simp, by simp⟩, ⟨?_, hj, ?_, ?_⟩, ?_⟩
    · simp [SzE, Sz]
    · have h4' : (2 : Int) * 2 ^ j ≤ 4 * (a.size : Int) := by exact_mod_cast h4
      simp +zetaDelta [Cpp.replicate, Cpp.size]; push_cast at *; omega
    · simp +zetaDelta [Cpp.size]
    · simpa +zetaDelta [Cpp.size] using hA
  case vc7.post.success.post.success =>
    rename_i r c hc res _ _ _ _ _ _ _ _ _ _ _ _ c2 hpost
    simp +zetaDelta [Cpp.size] at hc
    obtain ⟨j, hj, hn, hj1, hcj⟩ := hc
    obtain ⟨hjn, h4, h5⟩ := j_facts j a.size hj1 h1
    rw [(toNat_two_pow r j hj).2] at hpost
    obtain ⟨pI, pS, pT, -, pSh, -, pn, pc⟩ := hpost
    simp +zetaDelta only [st_eta]
    try simp +zetaDelta only [Int.toNat_zero, Cpp.size, Int.toNat_natCast] at pI pS pT pn
    have hle : a.size ≤ 2 ^ j := by
      have : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; ring
      omega
    have hn' : res.n.toNat = a.size := by rw [pn]; simp
    refine ⟨⟨j, pSh, by rw [hn']; simp, by simpa using h1, by simpa using h5, by simp [Cpp.fuel]; have := Nat.lt_two_pow_self (n := j); omega,
      hB, ?_, ?_, ?_⟩, ?_⟩
    · rw [hn']; exact pI
    · rw [hn']; exact pS
    · rw [hn', pT, leafL_root a j hle]
    · rw [pow_succ] at pc; omega

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

theorem valid_root (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) :
    ∃ H, H < Cpp.fuel ∧ B < INF ∧ st.n.toNat = vals.length ∧ ChminPre H B H st 0 0 st.n0 ∧
      T (view st) st.n.toNat H 0 0 = vals ∧ (st.n0 : Int) = 2 ^ H ∧ 1 ≤ vals.length ∧ 2 ^ H < 2 * vals.length := by
  obtain ⟨H, hSh, hn, h1, h2, hH, hB, hI, hS, hT⟩ := hv
  refine ⟨H, hH, hB, hn, ⟨le_rfl, le_rfl, by simp [hSh.2.1], ⟨by simp, by simp⟩, hSh, hI, hS⟩, hT, hSh.2.1, h1, h2⟩

theorem valid_le (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B B' : Int) (hv : Valid st vals B)
    (hBB : B ≤ B') (hB' : B' < INF) : Valid st vals B' := by
  obtain ⟨H, hSh, hn, h1, h2, hH, hB, hI, hS, hT⟩ := hv
  exact ⟨H, hSh, hn, h1, h2, hH, hB', hI, safe_le _ _ B B' hBB H 0 0 [0] hS, hT⟩

theorem valid_of_post (f : Int → Int) (a b : Int) (st res : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int)
    (H : Nat) (hH : H < Cpp.fuel) (hB : B < INF) (hn : st.n.toNat = vals.length) (h1 : 1 ≤ vals.length)
    (h2 : 2 ^ H < 2 * vals.length)
    (hT : T (view st) st.n.toNat H 0 0 = vals)
    (hR : RecPost f a b st.n.toNat B H 0 0 [0] (view st) (view res)) (hSh : Shape res H) (hnn : res.n = st.n) :
    Valid res (opL f a b 0 vals) B := by
  obtain ⟨rI, rS, rT, -⟩ := hR
  refine ⟨H, hSh, by rw [hnn, hn]; simp [opL], by simpa [opL] using h1, by simpa [opL] using h2, hH, hB, ?_, ?_, ?_⟩
  · rw [hnn]; exact rI
  · rw [hnn]; exact rS
  · rw [hnn, rT, hT]

/-- `chmin(a, b, x)`: every value at a position in `[a, b)` becomes `min(value, x)`, in `O(n)` steps. -/
theorem chmin_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmin st a b x
    ⦃⇓ r c => ⌜Valid r (opL (min · x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => chmin_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre
  simp only [cp.SegmentTreeBeatsSum.chmin, cp.SegmentTreeBeatsSum._chmin, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hSh, -, hnn, hc2⟩ := hpost
  refine ⟨valid_of_post _ a b st res vals B H hH hB hn h1 h2 hT hR hSh hnn, ?_⟩
  rw [pow_succ] at hc2; omega

/-- `chmax(a, b, x)`: every value at a position in `[a, b)` becomes `max(value, x)`, in `O(n)` steps. -/
theorem chmax_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmax st a b x
    ⦃⇓ r c => ⌜Valid r (opL (max · x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => chmax_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre
  simp only [cp.SegmentTreeBeatsSum.chmax, cp.SegmentTreeBeatsSum._chmax, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hSh, -, hnn, hc2⟩ := hpost
  refine ⟨valid_of_post _ a b st res vals B H hH hB hn h1 h2 hT hR hSh hnn, ?_⟩
  rw [pow_succ] at hc2; omega

/-- `update_val(a, b, x)`: every value at a position in `[a, b)` becomes `x` (`b ≤ n`), in `O(n)` steps. -/
theorem update_val_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b x : Int) (hb : b ≤ vals.length) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_val st a b x
    ⦃⇓ r c => ⌜Valid r (opL (fun _ => x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => updval_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre (by omega)
  simp only [cp.SegmentTreeBeatsSum.update_val, cp.SegmentTreeBeatsSum._update_val, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hSh, -, hnn, hc2⟩ := hpost
  refine ⟨valid_of_post _ a b st res vals B H hH hB hn h1 h2 hT hR hSh hnn, ?_⟩
  rw [pow_succ] at hc2; omega

theorem safe_shift (s : BS) (n : Nat) (B x : Int) : ∀ h k lo O, Safe s n B h k lo O →
    Safe s n (B + |x|) h k lo (O ++ O.map (· + x)) := by
  have top : ∀ (L : List Int) (O : List Int), (∀ o ∈ O, ∀ v ∈ L, |v + o| ≤ B) →
      ∀ o ∈ O ++ O.map (· + x), ∀ v ∈ L, |v + o| ≤ B + |x| := by
    intro L O hL o ho v hv
    rcases List.mem_append.mp ho with ho | ho
    · have := hL o ho v hv; have := abs_nonneg x; omega
    · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
      have := hL o' ho' v hv
      calc |v + (o' + x)| = |(v + o') + x| := by ring_nf
        _ ≤ |v + o'| + |x| := abs_add_le _ _
        _ ≤ B + |x| := by omega
  intro h
  induction h with
  | zero => intro k lo O hS; exact top _ O hS
  | succ h ih =>
    intro k lo O hS
    refine ⟨top _ O hS.1, fun hl => ?_⟩
    obtain ⟨s1, s2⟩ := hS.2 hl
    have hm : ∀ o ∈ 0 :: (O ++ O.map (· + x)).map (· + s.la k),
        o ∈ (0 :: O.map (· + s.la k)) ++ (0 :: O.map (· + s.la k)).map (· + x) := by
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact List.mem_append_left _ List.mem_cons_self
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ho
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hw))
      · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_right _ (List.mem_map.mpr ⟨w' + s.la k,
          List.mem_cons_of_mem _ (List.mem_map_of_mem hw'), by ring⟩)
    exact ⟨safe_mono _ n _ h _ _ _ _ hm (ih _ _ _ s1), safe_mono _ n _ h _ _ _ _ hm (ih _ _ _ s2)⟩

/-- `add_val(a, b, x)`: every value at a position in `[a, b)` gets `x` added (`b ≤ n`); the bound
on the stored values grows by `|x|`. `O(n)` steps. -/
theorem add_val_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b x : Int) (hb : b ≤ vals.length) (hBx : B + |x| < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_val st a b x
    ⦃⇓ r c => ⌜Valid r (opL (· + x) a b 0 vals) (B + |x|) ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, ⟨p1, p2, p3, p4, p5, p6, p7⟩, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have hS' : Safe (view st) st.n.toNat (B + |x|) H (0 : Int).toNat (0 : Int).toNat [0, x] :=
    safe_mono _ _ _ H _ _ _ _ (by simp) (safe_shift _ _ B x H _ _ [0] p7)
  have sp := fun t0 => addval_rec_spec H x a b (B + |x|) hBx H Cpp.fuel st 0 0 st.n0 t0 hH
    ⟨p1, p2, p3, p4, p5, p6, hS'⟩ (by omega)
  simp only [cp.SegmentTreeBeatsSum.add_val, cp.SegmentTreeBeatsSum._add_val, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hSh, -, hnn, hc2⟩ := hpost
  refine ⟨valid_of_post _ a b st res vals _ H hH hBx hn h1 h2 hT hR hSh hnn, ?_⟩
  rw [pow_succ] at hc2; omega

theorem opL_id (a b : Int) (lo : Nat) (L : List Int) : opL id a b lo L = L := opL_fix _ a b lo L (fun _ _ => rfl)

/-- `calc_max(a, b)`: the largest value at a position in `[a, b)` (`-INF` if there is none), in `O(n)` steps. -/
theorem calc_max_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_max st a b
    ⦃⇓ r c => ⌜r.1 = lmax (maskL (-INF) a b 0 vals) ∧ Valid r.2 vals B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => qmax_rec_spec H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre
  simp only [cp.SegmentTreeBeatsSum.calc_max, cp.SegmentTreeBeatsSum._calc_max, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hq, hSh, -, hnn, hc2⟩ := hpost
  have := valid_of_post _ a b st res.2 vals B H hH hB hn h1 h2 hT hR hSh hnn
  rw [opL_id] at this
  simp only [Int.toNat_zero] at hq
  refine ⟨by rw [hq, hT], this, ?_⟩
  rw [pow_succ] at hc2; omega

/-- `calc_min(a, b)`: the smallest value at a position in `[a, b)` (`INF` if there is none), in `O(n)` steps. -/
theorem calc_min_spec (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_min st a b
    ⦃⇓ r c => ⌜r.1 = lmin (maskL INF a b 0 vals) ∧ Valid r.2 vals B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => qmin_rec_spec H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre
  simp only [cp.SegmentTreeBeatsSum.calc_min, cp.SegmentTreeBeatsSum._calc_min, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hq, hSh, -, hnn, hc2⟩ := hpost
  have := valid_of_post _ a b st res.2 vals B H hH hB hn h1 h2 hT hR hSh hnn
  rw [opL_id] at this
  simp only [Int.toNat_zero] at hq
  refine ⟨by rw [hq, hT], this, ?_⟩
  rw [pow_succ] at hc2; omega

end Proofs.Cpp.SegmentTreeBeatsSum
