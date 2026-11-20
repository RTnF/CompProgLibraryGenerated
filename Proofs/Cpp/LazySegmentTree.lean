import Proofs.Cpp.Gen.LazySegmentTree
import Proofs.Cpp.Lib.LazySegmentTreeMath
import Proofs.Cpp.SegmentTree

/-! # The lazy segment tree (`library/segment_tree/lazy_segment_tree.hpp`)

Every public function of the translated model meets its specification for an action `A : Act M F` whose operations are
the instances of the template parameters (`Ops`), with step counts of the stated orders: construction `O(n)`, the point
and range operations and the searches `O(log n)` calls of the operations, `product_all` `O(1)`. The values are the
pushed-down tree `virt` (`LValid`); range operations first push the tags on the boundary paths, then work on the
canonical nodes and recompute the boundary ancestors (`docs/lazy_segment_tree.md`). -/
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

namespace Proofs.Cpp.LazySegmentTree

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

/-- The instances of the C++ operations compute the action `A` with constant step counts. -/
structure Ops (A : Act M F) (cE cOp cI cC cA : Nat) : Prop where
  e : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄ (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄
  op : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
    (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄
  id : ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 A.id (t + cI)⦄ (Cpp.StaticCall.call (name := "id") (T := F) (R := F)) ⦃Q⦄
  comp : ∀ f g, ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 (A.comp f g) (t + cC)⦄
    (Cpp.AdlCall2.call (name := "compose") (A := F) (B := F) (R := F) f g) ⦃Q⦄
  ap : ∀ f x, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.ap f x) (t + cA)⦄
    (Cpp.Method1.call (name := "apply") (A := M) (R := M) f x) ⦃Q⦄

/-- The state after `all_apply(k, f)`. -/
def allApplyS (A : Act M F) (st : cp.LazySegmentTree M F) (k : Int) (f : F) : cp.LazySegmentTree M F :=
  { st with node := Cpp.set st.node k (A.ap f (Cpp.get st.node k)),
            lazy := if k < st.n_node then Cpp.set st.lazy k (A.comp f (Cpp.get st.lazy k)) else st.lazy }

/-- The cost of `all_apply(k, f)`. -/
def allApplyC (st : cp.LazySegmentTree M F) (k : Int) (cC cA : Nat) : Nat :=
  1 + cA + (if k < st.n_node then cC else 0)

theorem all_apply_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (k : Int) (f : F) {Q : PostCond (cp.LazySegmentTree M F) PS} :
    ⦃fun c => Q.1 (allApplyS A st k f) (c + allApplyC st k cC cA)⦄ cp.LazySegmentTree.all_apply st k f ⦃Q⦄ := by
  have hC : ∀ f g, ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 (A.comp f g) (t + cC)⦄
      (Cpp.AdlCall2.call (name := "compose") (A := F) (B := F) (R := F) f g) ⦃Q⦄ := hO.comp
  have hA : ∀ f x, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.ap f x) (t + cA)⦄
      (Cpp.Method1.call (name := "apply") (A := M) (R := M) f x) ⦃Q⦄ := hO.ap
  mvcgen [cp.LazySegmentTree.all_apply, hC, hA]
  all_goals simp +zetaDelta [allApplyS, allApplyC] at *
  · have h := ‹(Q.1 _ _).down›
    simp only [if_pos ‹k < st.n_node›] at h; simpa [Nat.add_assoc] using h
  · have h := ‹(Q.1 _ _).down›
    simp only [if_neg (show ¬ k < st.n_node by omega)] at h; simpa [Nat.add_assoc] using h

/-- The cost of `push(k)`. -/
def pushC (A : Act M F) (st : cp.LazySegmentTree M F) (k : Int) (cI cC cA : Nat) : Nat :=
  1 + allApplyC st (2 * k) cC cA + allApplyC (allApplyS A st (2 * k) (Cpp.get st.lazy k)) (2 * k + 1) cC cA + cI

/-- The state after `push(k)`. -/
def pushS (A : Act M F) (st : cp.LazySegmentTree M F) (k : Int) : cp.LazySegmentTree M F :=
  let s1 := allApplyS A st (2 * k) (Cpp.get st.lazy k)
  let s2 := allApplyS A s1 (2 * k + 1) (Cpp.get s1.lazy k)
  { s2 with lazy := Cpp.set s2.lazy k A.id }

theorem push_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (k : Int) {Q : PostCond (cp.LazySegmentTree M F) PS} :
    ⦃fun c => Q.1 (pushS A st k) (c + pushC A st k cI cC cA)⦄ cp.LazySegmentTree.push st k ⦃Q⦄ := by
  have hI : ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 A.id (t + cI)⦄
      (Cpp.StaticCall.call (name := "id") (T := F) (R := F)) ⦃Q⦄ := hO.id
  have hAA : ∀ (st : cp.LazySegmentTree M F) (k : Int) (f : F) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 (allApplyS A st k f) (c + allApplyC st k cC cA)⦄ cp.LazySegmentTree.all_apply st k f ⦃Q⦄ :=
    fun st k f => all_apply_spec A cE cOp cI cC cA hO st k f
  mvcgen [cp.LazySegmentTree.push, hI, hAA]
  simp +zetaDelta only at *
  have h := ‹(Q.1 _ _).down›
  simp only [pushS, pushC] at h
  convert h using 2
  simp only [allApplyC, allApplyS]
  by_cases h1 : 2 * k < st.n_node <;> by_cases h2 : 2 * k + 1 < st.n_node <;> simp [h1, h2] <;> omega

theorem getB_set {α : Type} [Inhabited α] (v : Array α) (j : Int) (x : α) (i : Nat) :
    (Cpp.set v j x)[i]! = if i = j.toNat ∧ j.toNat < v.size then x else v[i]! := by
  by_cases h : j.toNat < v.size
  · rw [getElemBang_set _ _ _ _ h]; by_cases e : i = j.toNat <;> simp [e, h]
  · simp only [h, and_false, ite_false, Cpp.set]
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_neg h]

theorem size_ite_set {α : Type} (c : Prop) [Decidable c] (v : Array α) (j : Int) (x : α) :
    (if c then Cpp.set v j x else v).size = v.size := by split <;> simp

theorem push_fun_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (k : Int) (hk : 1 ≤ k) (hkN : k < st.n_node)
    (hsz : st.node.size = 2 * st.n_node.toNat) (hlz : st.lazy.size = st.n_node.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
    ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
      (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
      st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
      st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
      c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ := by
  have hI : ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 A.id (t + cI)⦄
      (Cpp.StaticCall.call (name := "id") (T := F) (R := F)) ⦃Q⦄ := hO.id
  have hC : ∀ f g, ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 (A.comp f g) (t + cC)⦄
      (Cpp.AdlCall2.call (name := "compose") (A := F) (B := F) (R := F) f g) ⦃Q⦄ := hO.comp
  have hA : ∀ f x, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.ap f x) (t + cA)⦄
      (Cpp.Method1.call (name := "apply") (A := M) (R := M) f x) ⦃Q⦄ := hO.ap
  have h2k : (2 * k).toNat = 2 * k.toNat := by omega
  have h2k1 : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
  have f1 : k.toNat ≠ 2 * k.toNat := by omega
  have f2 : k.toNat ≠ 2 * k.toNat + 1 := by omega
  have f3 : 2 * k.toNat ≠ 2 * k.toNat + 1 := by omega
  have hmax : max k 0 = k := by omega
  have hc : 2 * k.toNat + 1 < 2 * st.n_node.toNat := by omega
  have i1 : (2 * k + 1 < st.n_node) ↔ (2 * k.toNat + 1 < st.n_node.toNat) := by omega
  have i2 : (2 * k < st.n_node) ↔ (2 * k.toNat < st.n_node.toNat) := by omega
  mvcgen [cp.LazySegmentTree.push, cp.LazySegmentTree.all_apply, hI, hC, hA]
  all_goals simp +zetaDelta only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *
  all_goals refine ⟨?_, ?_, by simp, by simp, trivial, trivial, trivial, by omega⟩
  all_goals funext i
  all_goals simp only [getB_set, get_eq, size_set, hsz, hlz, h2k, h2k1, pushA, pushZ]
  all_goals by_cases e0 : i = k.toNat <;> by_cases e1 : i = 2 * k.toNat + 1 <;> by_cases e2 : i = 2 * k.toNat
  all_goals try (exfalso; omega)
  all_goals simp only [e0, e1, e2, if_true, if_false, ite_true, ite_false, true_and, false_and, and_true,
    or_true, true_or, or_false, false_or, f1, f2, f3, Ne.symm f1, Ne.symm f2, Ne.symm f3, hmax, i1, i2, hkN, hc,
    show 2 * k.toNat < 2 * st.n_node.toNat by omega, show k.toNat < st.n_node.toNat by omega, ne_eq,
    not_false_eq_true]
  all_goals (split <;> first | rfl | omega)

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

/-- The node values and the tags as functions. -/
def nodeF (st : cp.LazySegmentTree M F) : Nat → M := fun i => st.node[i]!
def lazyF (st : cp.LazySegmentTree M F) : Nat → F := fun i => st.lazy[i]!

/-- `st` is the lazy segment tree of the values `v`: the leaves of the pushed-down tree are `v` and `e`. -/
structure LValid (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) : Prop where
  n : st.n = v.length
  nn : 0 ≤ st.n_node
  hn : 0 ≤ st.h_node
  shape : (v = [] ∧ st.n_node = 0 ∧ st.h_node = 0) ∨
    (st.n_node.toNat = 2 ^ st.h_node.toNat ∧ 1 ≤ st.h_node ∧ v.length ≤ st.n_node.toNat ∧
      (st.h_node = 1 ∨ 2 ^ (st.h_node.toNat - 1) < v.length))
  size : st.node.size = 2 * st.n_node.toNat
  lsize : st.lazy.size = st.n_node.toNat
  state : LState A (nodeF st) (lazyF st) st.n_node.toNat
  leaf : ∀ i, i < v.length → virt A (nodeF st) (lazyF st) (st.n_node.toNat + i) = v[i]!
  pad : ∀ j, v.length ≤ j → j < st.n_node.toNat → virt A (nodeF st) (lazyF st) (st.n_node.toNat + j) = A.m.e

theorem lheight_le (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v)
    (hsmall : v.length ≤ 2 ^ 29) : st.h_node.toNat ≤ 30 := by
  rcases hv.shape with ⟨-, -, h0⟩ | ⟨-, h1, -, h2 | h2⟩
  · simp [h0]
  · omega
  · by_contra hc
    have : 2 ^ 30 ≤ 2 ^ (st.h_node.toNat - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- After pushing the ancestors of `p` at the levels `s > i` (from the root down). -/
def PathPushed (A : Act M F) (z : Nat → F) (p h i : Nat) : Prop :=
  ∀ s, i < s → s ≤ h → IdTag A (z (p / 2 ^ s))

theorem pushZ_below (A : Act M F) (z : Nat → F) (N k j : Nat) (hj : j < k) : pushZ A z N k j = z j :=
  pushZ_other A z N k j (by omega) (by omega) (by omega)

theorem path_bounds (N h p c : Nat) (hN : N = 2 ^ h) (hp1 : N ≤ p) (hp2 : p < 2 * N) (hc1 : 1 ≤ c) (hc2 : c ≤ h) :
    1 ≤ p / 2 ^ c ∧ p / 2 ^ c < N := by
  have hpos := Nat.two_pow_pos c
  have e : N = 2 ^ c * 2 ^ (h - c) := by rw [← pow_add, show c + (h - c) = h by omega, hN]
  refine ⟨(Nat.le_div_iff_mul_le hpos).mpr ?_, (Nat.div_lt_iff_lt_mul hpos).mpr ?_⟩
  · have : 2 ^ c ≤ N := by rw [e]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  · have : 2 * N ≤ N * 2 ^ c := by
      have : 2 ≤ 2 ^ c := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc1
      nlinarith
    omega

theorem shr_div (x i : Int) : shr x i = x / ((2 ^ i.toNat : Nat) : Int) := by
  simp [shr, Int.shiftRight_eq_div_pow]

theorem shr_nat (x i : Int) (hx : 0 ≤ x) : shr x i = ((x.toNat / 2 ^ i.toNat : Nat) : Int) := by
  rw [shr_div]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp

theorem rangeDown_cursor {a b cur : Int} {pref suff : List Int} (h : rangeDown a b = pref ++ cur :: suff) :
    cur = b - pref.length ∧ pref.length < (b - a + 1).toNat := by
  have hl : pref.length < (rangeDown a b).length := by rw [h]; simp
  have e := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl pref.length), Nat.sub_self, List.getElem?_cons_zero] at e
  simp only [rangeDown, List.length_map, List.length_range] at e hl
  rw [List.getElem?_map, List.getElem?_range hl] at e
  simp at e
  exact ⟨by omega, hl⟩

theorem level_cursor {h cur : Int} {pref suff : List Int} (H : rangeDown 1 h = pref ++ cur :: suff) :
    cur = h - pref.length ∧ 1 ≤ cur ∧ cur ≤ h ∧ pref.length < h.toNat := by
  obtain ⟨e, hl⟩ := rangeDown_cursor H
  refine ⟨e, by omega, by omega, by omega⟩

theorem path_k {h cur : Int} {pref suff : List Int} (H : rangeDown 1 h = pref ++ cur :: suff) (x : Int) (N : Nat)
    (hN : N = 2 ^ h.toNat) (hx0 : 0 ≤ x) (hx1 : N ≤ x.toNat) (hx2 : x.toNat < 2 * N) :
    1 ≤ shr x cur ∧ shr x cur < N ∧ (shr x cur).toNat = x.toNat / 2 ^ cur.toNat ∧ cur = h - pref.length ∧
      1 ≤ cur ∧ cur ≤ h ∧ pref.length < h.toNat := by
  obtain ⟨e, c1, c2, cl⟩ := level_cursor H
  have hb := path_bounds N h.toNat x.toNat cur.toNat hN hx1 hx2 (by omega) (by omega)
  rw [shr_nat x cur hx0]
  exact ⟨by omega, by omega, Int.toNat_natCast _, e, c1, c2, cl⟩

/-- The invariant of a loop that pushes the ancestors of the leaf `p` from the root down. -/
def GInv (A : Act M F) (st0 : cp.LazySegmentTree M F) (p h m : Nat) (st : cp.LazySegmentTree M F) : Prop :=
  st.n = st0.n ∧ st.n_node = st0.n_node ∧ st.h_node = st0.h_node ∧ st.node.size = st0.node.size ∧
    st.lazy.size = st0.lazy.size ∧ LState A (nodeF st) (lazyF st) st0.n_node.toNat ∧
    (∀ j, j < 2 * st0.n_node.toNat → virt A (nodeF st) (lazyF st) j = virt A (nodeF st0) (lazyF st0) j) ∧
    PathPushed A (lazyF st) p h (h - m)

theorem ginv_step (A : Act M F) (st0 st r : cp.LazySegmentTree M F) (p h m k : Nat)
    (hI : GInv A st0 p h m st) (hk : k = p / 2 ^ (h - m)) (hk1 : 1 ≤ k) (hkN : k < st0.n_node.toNat) (hm : m < h)
    (hn : (fun i => r.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k)
    (hz : (fun i => r.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k)
    (h1 : r.node.size = st.node.size) (h2 : r.lazy.size = st.lazy.size) (h3 : r.n = st.n)
    (h4 : r.n_node = st.n_node) (h5 : r.h_node = st.h_node) :
    GInv A st0 p h (m + 1) ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  have hnn : st.n_node.toNat = st0.n_node.toNat := by rw [g2]
  obtain ⟨hS', hV'⟩ := push_state A (nodeF st) (lazyF st) st0.n_node.toNat k gS hk1 hkN
  have en : nodeF ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ = pushA A (nodeF st) (lazyF st) k := hn
  have ez : lazyF ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ = pushZ A (lazyF st) st0.n_node.toNat k := by
    rw [← hnn]; exact hz
  refine ⟨by simp [h3, g1], by simp [h4, g2], by simp [h5, g3], by simp [h1, g4], by simp [h2, g5], ?_, ?_, ?_⟩
  · rw [en, ez]; exact hS'
  · intro j hj; rw [en, ez, hV' j hj]; exact gV j hj
  · intro s hs1 hs2
    rw [ez]
    by_cases e : s = h - m
    · subst e; rw [← hk, pushZ_self]; exact idTag_id A
    · have hlt : p / 2 ^ s < k := by
        rw [hk]
        have : p / 2 ^ s ≤ p / 2 ^ (h - m + 1) := Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.two_pow_pos _)
        rw [pow_succ, ← Nat.div_div_eq_div_mul] at this
        omega
      rw [pushZ_below A _ _ _ _ hlt]
      exact gP s (by omega) hs2

theorem ginv_valid (A : Act M F) (st0 st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st0 v) (p h m : Nat)
    (hI : GInv A st0 p h m st) : LValid A st v := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  refine ⟨by rw [g1]; exact hv.n, by rw [g2]; exact hv.nn, by rw [g3]; exact hv.hn, by rw [g2, g3]; exact hv.shape,
    by rw [g4, g2]; exact hv.size, by rw [g5, g2]; exact hv.lsize, by rw [g2]; exact gS, ?_, ?_⟩
  · intro i hi
    have hb : st0.n_node.toNat + i < 2 * st0.n_node.toNat := by
      rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
      · simp [h1] at hi
      · omega
    rw [g2, gV _ hb]; exact hv.leaf i hi
  · intro j h1 h2
    rw [g2] at h2 ⊢
    rw [gV _ (by omega)]; exact hv.pad j h1 h2

theorem ginv_read (A : Act M F) (st0 st : cp.LazySegmentTree M F) (p h : Nat) (hN : st0.n_node.toNat = 2 ^ h)
    (hp1 : st0.n_node.toNat ≤ p) (hp2 : p < 2 * st0.n_node.toNat) (hI : GInv A st0 p h h st) :
    st.node[p]! = virt A (nodeF st0) (lazyF st0) p := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  rw [← gV p hp2]
  simp only [virt]
  rw [P_of_idTag A _ p _ (gS.1 p hp2)]
  · rfl
  · intro j hj ⟨t, ht, e⟩
    subst e
    have hth : t ≤ h := by
      by_contra hc
      have : 2 ^ (h + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : p / 2 ^ t = 0 := Nat.div_eq_of_lt (by rw [pow_succ] at this; omega)
      omega
    exact gP t (by omega) hth

theorem get_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (idx : Int) (h0 : 0 ≤ idx)
    (hi : idx < v.length) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.get_ st idx
    ⦃⇓ r c => ⌜r.1 = v[idx.toNat]! ∧ LValid A r.2 v ∧
      c ≤ t0 + 2 + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  rcases hv.shape with ⟨hnil, -⟩ | ⟨hN, hh, hle, -⟩
  · simp [hnil] at hi; omega
  have hp1 : st.n_node.toNat ≤ (idx + st.n_node).toNat := by omega
  have hp2 : (idx + st.n_node).toNat < 2 * st.n_node.toNat := by omega
  mvcgen [cp.LazySegmentTree.get_, hP]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', node', lazy'⟩ c =>
      ⌜GInv A st (idx + st.n_node).toNat st.h_node.toNat xs.prefix.length ⟨n', nn', hh', node', lazy'⟩ ∧
        c ≤ t0 + 1 + xs.prefix.length * (4 + 2 * cA + 2 * cC + cI)⌝
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  case vc1.a =>
    exact (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).1
  case vc2.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    have := (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).2.1
    simp at g2; omega
  case vc3.a =>
    obtain ⟨⟨g1, g2, g3, g4, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g4; rw [g4, g2]; exact hsz
  case vc4.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g5; rw [g5, g2]; exact hlz
  case vc5.step.post.success =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, rc⟩ := ‹(fun i => _) = _ ∧ _›
    obtain ⟨k1, kN, kt, ec, c1, c2, cl⟩ := path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega)
      (by omega) (by omega)
    have gnn := gI.2.1
    simp at gnn
    refine ⟨ginv_step A st _ _ _ _ _ _ gI (by rw [kt, ec]; congr 2; omega) (by omega) (by omega) cl r1 r2 r3 r4 r5 r6 r7,
      ?_⟩
    rw [Nat.add_one_mul]; omega
  case vc6.inr.isTrue.pre =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun j _ => rfl, fun s h1 h2 => by omega⟩, by omega⟩
  case vc7.inr.isTrue.post.success =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp [rangeDown] at gI gc
    refine ⟨?_, ginv_valid A st _ v hv _ _ _ gI, ?_⟩
    · rw [get_eq, ginv_read A st _ _ _ hN (by omega) (by omega) gI,
        show (idx + st.n_node).toNat = st.n_node.toNat + idx.toNat by omega]
      simpa using hv.leaf idx.toNat (by omega)
    · have : st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) = (st.h_node - 1 + 1).toNat * (4 + 2 * cA + 2 * cC + cI) := by
        congr 1; omega
      omega
  case vc9.inr.isFalse => omega

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

/-- The recompute loop of `set`: the leaf `p` holds the new value, the nodes off the path from `p / 2^i` satisfy the
lazy invariant. -/
def RInvL (A : Act M F) (st1 : cp.LazySegmentTree M F) (p : Nat) (x : M) (N h : Nat) (node : Array M) (i : Int) :
    Prop :=
  node.size = 2 * N ∧ 1 ≤ i ∧ i ≤ h + 1 ∧ LSInv A (fun j => node[j]!) (lazyF st1) N (p / 2 ^ i.toNat) ∧
    AllV A.m (fun j => node[j]!) (2 * N) ∧ ∀ j, N ≤ j → node[j]! = upd (nodeF st1) p x j

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem rinvl_init (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p h : Nat) (x : M) (hx : A.m.V x)
    (hI : GInv A st p h h st1) (hp1 : st.n_node.toNat ≤ p) (hp2 : p < 2 * st.n_node.toNat) (P : Int)
    (hP : P.toNat = p) (hsz : st.node.size = 2 * st.n_node.toNat) :
    RInvL A st1 p x st.n_node.toNat h (Cpp.set st1.node P x) 1 := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  have hsz1 : st1.node.size = 2 * st.n_node.toNat := by rw [g4, hsz]
  have hF : ∀ j, (Cpp.set st1.node P x)[j]! = upd (nodeF st1) p x j := by
    intro j; rw [getB_set, hP]; simp only [upd, nodeF]; by_cases e : j = p <;> simp [e, hsz1] <;> omega
  refine ⟨by simp [hsz1], le_refl _, by omega, ?_, ?_, fun j _ => hF j⟩
  · have := lsinv_init A (nodeF st1) (lazyF st1) _ p x gS.2.2 hp1
    intro j h1 h2 hna
    simp only [hF]; exact this j h1 h2 (by simpa using hna)
  · intro j hj; simp only [hF, upd]; split
    · exact hx
    · exact gS.1 j hj

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem rinvl_step (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p h : Nat) (x : M)
    (hI : GInv A st p h h st1) (hN : st.n_node.toNat = 2 ^ h) (hp1 : st.n_node.toNat ≤ p)
    (hp2 : p < 2 * st.n_node.toNat) (node : Array M) (i : Int) (P : Int) (hP : P = (p : Int))
    (hR : RInvL A st1 p x st.n_node.toNat h node i) (hih : i ≤ h) :
    RInvL A st1 p x st.n_node.toNat h
      (Cpp.set node (shr P i) (A.m.op (Cpp.get node (shr P i * 2)) (Cpp.get node (shr P i * 2 + 1)))) (i + 1) := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  obtain ⟨hsz, h1, h2, hS, hV, hL⟩ := hR
  have hk := path_bounds _ _ _ i.toNat hN hp1 hp2 (by omega) (by omega)
  have hj : shr P i = ((p / 2 ^ i.toNat : Nat) : Int) := by rw [shr_nat _ _ (by omega), hP]; simp
  set j := p / 2 ^ i.toNat with hjdef
  rw [hj]
  simp only [get_eq, show (((j : Nat) : Int) * 2).toNat = 2 * j by omega,
    show (((j : Nat) : Int) * 2 + 1).toNat = 2 * j + 1 by omega]
  have hF : ∀ q, (Cpp.set node (j : Int) (A.m.op node[2 * j]! node[2 * j + 1]!))[q]! =
      upd (fun q => node[q]!) j (A.m.op node[2 * j]! node[2 * j + 1]!) q := by
    intro q; rw [getB_set]; simp only [upd, Int.toNat_natCast]; by_cases e : q = j <;> simp [e, hsz] <;> omega
  refine ⟨by simp [hsz], by omega, by omega, ?_, ?_, ?_⟩
  · have hid := gP i.toNat (by omega) (by omega)
    have := lsinv_step A (fun q => node[q]!) (lazyF st1) _ j hS hk.1 hk.2 hid
      (A.m.closed _ _ (hV _ (by omega)) (hV _ (by omega)))
    intro q q1 q2 hna
    simp only [hF]
    apply this q q1 q2
    rwa [show (i + 1).toNat = i.toNat + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul] at hna
  · intro q hq; simp only [hF, upd]; split
    · exact A.m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
    · exact hV q hq
  · intro q hq; simp only [hF, upd, if_neg (show q ≠ j by omega)]; exact hL q hq

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem pushed_P (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p h : Nat) (hN : st.n_node.toNat = 2 ^ h)
    (hp2 : p < 2 * st.n_node.toNat) (hI : GInv A st p h h st1) (y : M) (hy : A.m.V y) :
    P A (lazyF st1) p y = y := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  apply P_of_idTag A _ p y hy
  intro j hj ⟨t, ht, e⟩
  subst e
  have hth : t ≤ h := by
    by_contra hc
    have : 2 ^ (h + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : p / 2 ^ t = 0 := Nat.div_eq_of_lt (by rw [pow_succ] at this; omega)
    omega
  exact gP t (by omega) hth

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem rinvl_done (A : Act M F) (st st1 : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (h : Nat)
    (hN : st.n_node.toNat = 2 ^ h) (hh : st.h_node.toNat = h) (idx : Int) (h0 : 0 ≤ idx) (hi : idx < v.length)
    (x : M) (hx : A.m.V x)
    (hI : GInv A st (idx + st.n_node).toNat h h st1) (node : Array M) (i : Int)
    (hR : RInvL A st1 (idx + st.n_node).toNat x st.n_node.toNat h node i) (hih : ¬ i ≤ h) :
    LValid A ⟨st.n, st.n_node, st.h_node, node, st1.lazy⟩ (v.set idx.toNat x) := by
  have hI' := hI
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  obtain ⟨hsz, h1, h2, hS, hV, hL⟩ := hR
  have hn := hv.n
  have hnn := hv.nn
  have hlen : v.length ≤ st.n_node.toNat := by
    rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, -⟩
    · simp [h1] at hi; omega
    · exact h3
  have hi' : i.toNat = h + 1 := by omega
  have hzero : (idx + st.n_node).toNat / 2 ^ i.toNat = 0 := by
    rw [hi', pow_succ, ← hN]; exact Nat.div_eq_of_lt (by omega)
  rw [hzero] at hS
  have hvirt : ∀ q, st.n_node.toNat ≤ q → q < 2 * st.n_node.toNat →
      virt A (fun j => node[j]!) (lazyF st1) q =
        if q = (idx + st.n_node).toNat then x else virt A (nodeF st) (lazyF st) q := by
    intro q hq1 hq2
    simp only [virt, hL q hq1, upd]
    split
    · rename_i e; subst e; exact pushed_P A st st1 _ h hN hq2 hI' x hx
    · simpa [virt] using gV q hq2
  refine ⟨by simpa using hn, hnn, hv.hn, ?_, hsz, by rw [g5]; exact hv.lsize, ⟨hV, gS.2.1, lsinv_zero A _ _ _ hS⟩,
    ?_, ?_⟩
  · rcases hv.shape with ⟨h1, _⟩ | ⟨h1, h2, h3, h4⟩
    · simp [h1] at hi; omega
    · right; exact ⟨h1, h2, by simpa using h3, by simpa using h4⟩
  · intro j hj
    simp only [List.length_set] at hj
    have := hvirt (st.n_node.toNat + j) (by omega) (by omega)
    show virt A (fun j => node[j]!) (lazyF st1) (st.n_node.toNat + j) = _
    rw [this]
    by_cases e : j = idx.toNat
    · subst e; simp [show st.n_node.toNat + idx.toNat = (idx + st.n_node).toNat by omega, hj]
    · rw [if_neg (by omega), hv.leaf j hj]
      simp [Ne.symm e]
  · intro j h1 h2
    simp only [List.length_set] at h1
    change j < st.n_node.toNat at h2
    have := hvirt (st.n_node.toNat + j) (by omega) (by omega)
    show virt A (fun j => node[j]!) (lazyF st1) (st.n_node.toNat + j) = _
    rw [this, if_neg (by omega)]
    exact hv.pad j h1 h2

theorem set_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29) (idx : Int)
    (h0 : 0 ≤ idx) (hi : idx < v.length) (val : M) (hval : A.m.V val) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.set_ st idx val
    ⦃⇓ r c => ⌜LValid A r (v.set idx.toNat val) ∧
      c ≤ t0 + 2 + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (st.h_node.toNat + 1) * (2 + cOp)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hU : ∀ (st : cp.LazySegmentTree M F) (i : Int) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (A.m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.LazySegmentTree.update_int st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.LazySegmentTree.update_int, hOp]
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  rcases hv.shape with ⟨hnil, -⟩ | ⟨hN, hh, hle, -⟩
  · simp [hnil] at hi; omega
  have hp1 : st.n_node.toNat ≤ (idx + st.n_node).toNat := by omega
  have hp2 : (idx + st.n_node).toNat < 2 * st.n_node.toNat := by omega
  mvcgen [cp.LazySegmentTree.set_, hP, hU]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', node', lazy'⟩ c =>
      ⌜GInv A st (idx + st.n_node).toNat st.h_node.toNat xs.prefix.length ⟨n', nn', hh', node', lazy'⟩ ∧
        c ≤ t0 + 1 + xs.prefix.length * (4 + 2 * cA + 2 * cC + cI)⌝
  case vc7.inv =>
    exact ⟨fun ⟨n', nn', hh', node', lazy', i⟩ c => ⌜∃ st1, GInv A st (idx + st.n_node).toNat st.h_node.toNat
              st.h_node.toNat st1 ∧ n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧ lazy' = st1.lazy ∧
              RInvL A st1 (idx + st.n_node).toNat val st.n_node.toNat st.h_node.toNat node' i ∧
              c ≤ t0 + 2 + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (i.toNat - 1) * (2 + cOp)⌝,
           fun ⟨n', nn', hh', node', lazy', _⟩ c => ⌜LValid A ⟨n', nn', hh', node', lazy'⟩ (v.set idx.toNat val) ∧
              c ≤ t0 + 2 + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (st.h_node.toNat + 1) * (2 + cOp)⌝,
           fun ⟨_, _, hh', _, _, i⟩ => (hh' + 1 - i).toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.2 = i' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.1 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).1 = n' at *)
  case vc1.a =>
    exact (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).1
  case vc2.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    have := (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).2.1
    simp at g2; omega
  case vc3.a =>
    obtain ⟨⟨g1, g2, g3, g4, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g4; rw [g4, g2]; exact hsz
  case vc4.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g5; rw [g5, g2]; exact hlz
  case vc5.step.post.success =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, rc⟩ := ‹(fun i => _) = _ ∧ _›
    obtain ⟨k1, kN, kt, ec, c1, c2, cl⟩ := path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega)
      (by omega) (by omega)
    have gnn := gI.2.1
    simp at gnn
    refine ⟨ginv_step A st _ _ _ _ _ _ gI (by rw [kt, ec]; congr 2; omega) (by omega) (by omega) cl r1 r2 r3 r4 r5 r6 r7,
      ?_⟩
    rw [Nat.add_one_mul]; omega
  case vc6.inr.isTrue.pre =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun j _ => rfl, fun s h1 h2 => by omega⟩, by omega⟩
  case vc8.step.isTrue =>
    obtain ⟨st1, gI, e1, e2, e3, e4, hR, hc⟩ := ‹∃ st1, GInv _ _ _ _ _ st1 ∧ _›
    subst e1 e2 e3 e4
    refine ⟨rinvl_done A st st1 v hv _ hN rfl idx h0 hi val hval gI _ _ hR (by omega), ?_⟩
    have : i'.toNat - 1 = st.h_node.toNat := by have := hR.2.2.1; omega
    rw [this] at hc
    have e1 : (st.h_node.toNat + 1) * (2 + cOp) = st.h_node.toNat * (2 + cOp) + (2 + cOp) := by ring
    have e2 : st.h_node.toNat * (4 + (1 * cA + cA) + 2 * cC + cI) = st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) := by
      ring
    omega
  case vc9.step.isFalse =>
    obtain ⟨st1, gI, e1, e2, e3, e4, hR, hc⟩ := ‹∃ st1, GInv _ _ _ _ _ st1 ∧ _›
    have hi1 := hR.2.1
    refine ⟨⟨st1, gI, e1, e2, e3, e4, rinvl_step A st st1 _ _ val gI hN (by omega) (by omega) nd' i' _ (by omega)
      hR (by omega), ?_⟩, by omega⟩
    have : (i' + 1).toNat - 1 = (i'.toNat - 1) + 1 := by omega
    rw [this]
    have e1 : (i'.toNat - 1 + 1) * (2 + cOp) = (i'.toNat - 1) * (2 + cOp) + (2 + cOp) := by ring
    have e2 : st.h_node.toNat * (4 + (1 * cA + cA) + 2 * cC + cI) = st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) := by
      ring
    omega
  case vc10.inr.isTrue.post.success.pre =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    have hl : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hl] at gI gc
    have g1 := gI.1
    have g2 := gI.2.1
    have g3 := gI.2.2.1
    simp only at g1 g2 g3
    refine ⟨⟨⟨n', nn', hh', nd', lz'⟩, gI, g1, g2, g3, rfl,
      rinvl_init A st _ _ _ val hval gI (by omega) (by omega) _ rfl hsz, by omega⟩, by simp [fuel]; omega⟩
  case vc11.inr.isTrue.post.success.post.success => exact ‹LValid _ _ _ ∧ _›
  case vc13.inr.isFalse => omega

theorem update_point_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29) (idx : Int)
    (h0 : 0 ≤ idx) (hi : idx < v.length) (f : F) (hf : A.VF f) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.update_int_F st idx f
    ⦃⇓ r c => ⌜LValid A r (v.set idx.toNat (A.ap f v[idx.toNat]!)) ∧
      c ≤ t0 + 2 + cA + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (st.h_node.toNat + 1) * (2 + cOp)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hU : ∀ (st : cp.LazySegmentTree M F) (i : Int) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (A.m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.LazySegmentTree.update_int st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.LazySegmentTree.update_int, hOp]
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  rcases hv.shape with ⟨hnil, -⟩ | ⟨hN, hh, hle, -⟩
  · simp [hnil] at hi; omega
  have hp1 : st.n_node.toNat ≤ (idx + st.n_node).toNat := by omega
  have hp2 : (idx + st.n_node).toNat < 2 * st.n_node.toNat := by omega
  have hAp : ∀ f x, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.ap f x) (t + cA)⦄
      (Cpp.Method1.call (name := "apply") (A := M) (R := M) f x) ⦃Q⦄ := hO.ap
  mvcgen [cp.LazySegmentTree.update_int_F, hP, hU, hAp]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', node', lazy'⟩ c =>
      ⌜GInv A st (idx + st.n_node).toNat st.h_node.toNat xs.prefix.length ⟨n', nn', hh', node', lazy'⟩ ∧
        c ≤ t0 + 1 + xs.prefix.length * (4 + 2 * cA + 2 * cC + cI)⌝
  case vc7.inv =>
    exact ⟨fun ⟨n', nn', hh', node', lazy', i⟩ c => ⌜∃ st1, GInv A st (idx + st.n_node).toNat st.h_node.toNat
              st.h_node.toNat st1 ∧ n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧ lazy' = st1.lazy ∧
              RInvL A st1 (idx + st.n_node).toNat (A.ap f st1.node[(idx + st.n_node).toNat]!) st.n_node.toNat st.h_node.toNat node' i ∧
              c ≤ t0 + 2 + cA + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (i.toNat - 1) * (2 + cOp)⌝,
           fun ⟨n', nn', hh', node', lazy', _⟩ c => ⌜LValid A ⟨n', nn', hh', node', lazy'⟩ (v.set idx.toNat (A.ap f v[idx.toNat]!)) ∧
              c ≤ t0 + 2 + cA + st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) + (st.h_node.toNat + 1) * (2 + cOp)⌝,
           fun ⟨_, _, hh', _, _, i⟩ => (hh' + 1 - i).toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.2 = i' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.1 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).1 = n' at *)
  case vc1.a =>
    exact (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).1
  case vc2.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    have := (path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega) (by omega) (by omega)).2.1
    simp at g2; omega
  case vc3.a =>
    obtain ⟨⟨g1, g2, g3, g4, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g4; rw [g4, g2]; exact hsz
  case vc4.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    simp at g2 g5; rw [g5, g2]; exact hlz
  case vc5.step.post.success =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, rc⟩ := ‹(fun i => _) = _ ∧ _›
    obtain ⟨k1, kN, kt, ec, c1, c2, cl⟩ := path_k ‹rangeDown _ _ = _ ++ _ :: _› (idx + st.n_node) _ hN (by omega)
      (by omega) (by omega)
    have gnn := gI.2.1
    simp at gnn
    refine ⟨ginv_step A st _ _ _ _ _ _ gI (by rw [kt, ec]; congr 2; omega) (by omega) (by omega) cl r1 r2 r3 r4 r5 r6 r7,
      ?_⟩
    rw [Nat.add_one_mul]; omega
  case vc6.inr.isTrue.pre =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun j _ => rfl, fun s h1 h2 => by omega⟩, by omega⟩
  case vc8.step.isTrue =>
    obtain ⟨st1, gI, e1, e2, e3, e4, hR, hc⟩ := ‹∃ st1, GInv _ _ _ _ _ st1 ∧ _›
    subst e1 e2 e3 e4
    have hx1 : st1.node[(idx + st.n_node).toNat]! = v[idx.toNat]! := by
      rw [ginv_read A st _ _ _ hN (by omega) (by omega) gI,
        show (idx + st.n_node).toNat = st.n_node.toNat + idx.toNat by omega]
      exact hv.leaf idx.toNat (by omega)
    have hxv : A.m.V (A.ap f st1.node[(idx + st.n_node).toNat]!) := A.ap_V _ _ hf (gI.2.2.2.2.2.1.1 _ (by omega))
    have hd := rinvl_done A st st1 v hv _ hN rfl idx h0 hi _ hxv gI _ _ hR (by omega)
    rw [hx1] at hd
    refine ⟨by simpa using hd, ?_⟩
    have : i'.toNat - 1 = st.h_node.toNat := by have := hR.2.2.1; omega
    rw [this] at hc
    have e1 : (st.h_node.toNat + 1) * (2 + cOp) = st.h_node.toNat * (2 + cOp) + (2 + cOp) := by ring
    have e2 : st.h_node.toNat * (4 + (1 * cA + cA) + 2 * cC + cI) = st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) := by
      ring
    omega
  case vc9.step.isFalse =>
    obtain ⟨st1, gI, e1, e2, e3, e4, hR, hc⟩ := ‹∃ st1, GInv _ _ _ _ _ st1 ∧ _›
    have hi1 := hR.2.1
    refine ⟨⟨st1, gI, e1, e2, e3, e4, rinvl_step A st st1 _ _ _ gI hN (by omega) (by omega) nd' i' _ (by omega)
      hR (by omega), ?_⟩, by omega⟩
    have : (i' + 1).toNat - 1 = (i'.toNat - 1) + 1 := by omega
    rw [this]
    have e1 : (i'.toNat - 1 + 1) * (2 + cOp) = (i'.toNat - 1) * (2 + cOp) + (2 + cOp) := by ring
    have e2 : st.h_node.toNat * (4 + (1 * cA + cA) + 2 * cC + cI) = st.h_node.toNat * (4 + 2 * cA + 2 * cC + cI) := by
      ring
    omega
  case vc10.inr.isTrue.post.success.pre =>
    obtain ⟨gI, gc⟩ := ‹GInv _ _ _ _ _ _ ∧ _›
    have hl : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hl] at gI gc
    have g1 := gI.1
    have g2 := gI.2.1
    have g3 := gI.2.2.1
    simp only at g1 g2 g3
    have hR0 := rinvl_init A st ⟨n', nn', hh', nd', lz'⟩ _ _ (A.ap f nd'[(idx + st.n_node).toNat]!)
      (A.ap_V _ _ hf (gI.2.2.2.2.2.1.1 _ (by omega))) gI (by omega) (by omega) (idx + st.n_node) rfl hsz
    refine ⟨⟨⟨n', nn', hh', nd', lz'⟩, gI, g1, g2, g3, rfl, by rw [get_eq]; exact hR0, by omega⟩,
      by simp [fuel]; omega⟩
  case vc11.inr.isTrue.post.success.post.success => exact ‹LValid _ _ _ ∧ _›
  case vc13.inr.isFalse => omega


end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

/-- The nodes pushed before a range operation, at the levels above `h - m`: the ancestors that cut through the left
boundary `L` or the right boundary `R` (leaf positions). -/
def Cut (L R h m j : Nat) : Prop :=
  ∃ s, h - m < s ∧ s ≤ h ∧ ((L % 2 ^ s ≠ 0 ∧ j = L / 2 ^ s) ∨ (R % 2 ^ s ≠ 0 ∧ j = (R - 1) / 2 ^ s))

/-- A tree with the same contents as `st0` whose nodes in `S` carry trivial tags. -/
def PInvS (A : Act M F) (st0 : cp.LazySegmentTree M F) (S : Nat → Prop) (st : cp.LazySegmentTree M F) : Prop :=
  st.n = st0.n ∧ st.n_node = st0.n_node ∧ st.h_node = st0.h_node ∧ st.node.size = st0.node.size ∧
    st.lazy.size = st0.lazy.size ∧ LState A (nodeF st) (lazyF st) st0.n_node.toNat ∧
    (∀ j, j < 2 * st0.n_node.toNat → virt A (nodeF st) (lazyF st) j = virt A (nodeF st0) (lazyF st0) j) ∧
    ∀ j, S j → IdTag A (lazyF st j)

theorem pinvs_push (A : Act M F) (st0 st r : cp.LazySegmentTree M F) (S : Nat → Prop) (k : Nat)
    (hI : PInvS A st0 S st) (hk1 : 1 ≤ k) (hkN : k < st0.n_node.toNat) (hS : ∀ j, S j → j ≠ 2 * k ∧ j ≠ 2 * k + 1)
    (hn : (fun i => r.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k)
    (hz : (fun i => r.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k)
    (h1 : r.node.size = st.node.size) (h2 : r.lazy.size = st.lazy.size) (h3 : r.n = st.n)
    (h4 : r.n_node = st.n_node) (h5 : r.h_node = st.h_node) :
    PInvS A st0 (fun j => S j ∨ j = k) ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  have hnn : st.n_node.toNat = st0.n_node.toNat := by rw [g2]
  obtain ⟨hS', hV'⟩ := push_state A (nodeF st) (lazyF st) st0.n_node.toNat k gS hk1 hkN
  have en : nodeF ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ = pushA A (nodeF st) (lazyF st) k := hn
  have ez : lazyF ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ = pushZ A (lazyF st) st0.n_node.toNat k := by
    rw [← hnn]; exact hz
  refine ⟨by simp [h3, g1], by simp [h4, g2], by simp [h5, g3], by simp [h1, g4], by simp [h2, g5], ?_, ?_, ?_⟩
  · rw [en, ez]; exact hS'
  · intro j hj; rw [en, ez, hV' j hj]; exact gV j hj
  · intro j hj
    rw [ez]
    rcases hj with hj | rfl
    · by_cases e : j = k
      · subst e; rw [pushZ_self]; exact idTag_id A
      · obtain ⟨n1, n2⟩ := hS j hj
        rw [pushZ_other A _ _ _ _ e n1 n2]; exact gP j hj
    · rw [pushZ_self]; exact idTag_id A

theorem pinvs_mono (A : Act M F) (st0 st : cp.LazySegmentTree M F) (S T : Nat → Prop) (hI : PInvS A st0 S st)
    (h : ∀ j, T j → S j) : PInvS A st0 T st := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  exact ⟨g1, g2, g3, g4, g5, gS, gV, fun j hj => gP j (h j hj)⟩

theorem level_lt (N h x s c : Nat) (hN : N = 2 ^ h) (hx : x < 2 * N) (hsc : c < s) (hs : s ≤ h + 1) (y : Nat)
    (hy : N ≤ y) (hc : c ≤ h) : x / 2 ^ s < y / 2 ^ c := by
  have h1 : x / 2 ^ s < 2 ^ (h + 1 - s) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h + 1 - s + s = h + 1 by omega, pow_succ]; omega
  have h2 : 2 ^ (h - c) ≤ y / 2 ^ c := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h - c + c = h by omega]; omega
  have : 2 ^ (h + 1 - s) ≤ 2 ^ (h - c) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem shr_one (x : Int) : shr x 1 = x / 2 := by simp [shr, Int.shiftRight_eq_div_pow]

theorem land_one (x : Int) (hx : 0 ≤ x) : land x 1 = x % 2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp [land]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- One iteration of the product loop that reads the nodes of `node`, which agree with the tree `V` where read. -/
theorem lprod_step (m : Mon M) (node : Array M) (V : Nat → M) (N : Nat) (T : M)
    (hV : AllV m V (2 * N)) (hTr : TInv m V N) (x y : Int) (lo ro : M) (hx : 0 ≤ x) (hxy : x < y)
    (hP : PInv m V N T x.toNat y.toNat lo ro)
    (hrx : x.toNat % 2 = 1 → node[x.toNat]! = V x.toNat) (hry : y.toNat % 2 = 1 → node[y.toNat - 1]! = V (y.toNat - 1)) :
    0 ≤ shr (if land x 1 ≠ 0 then x + 1 else x) 1 ∧ 0 ≤ shr (if land y 1 ≠ 0 then y - 1 else y) 1 ∧
    PInv m V N T (shr (if land x 1 ≠ 0 then x + 1 else x) 1).toNat
      (shr (if land y 1 ≠ 0 then y - 1 else y) 1).toNat
      (if land x 1 ≠ 0 then m.op lo (get node x) else lo)
      (if land y 1 ≠ 0 then m.op (get node (y - 1)) ro else ro) ∧
    shr (if land y 1 ≠ 0 then y - 1 else y) 1 - shr (if land x 1 ≠ 0 then x + 1 else x) 1 < y - x := by
  have key := prod_step m V N T hV hTr x.toNat y.toNat lo ro hP (by omega)
  rw [land_one x hx, land_one y (by omega)]
  simp only [shr_one, get_eq]
  have hxm : x % 2 = (x.toNat % 2 : Nat) := by omega
  have hym : y % 2 = (y.toNat % 2 : Nat) := by omega
  have hy1 : (y - 1).toNat = y.toNat - 1 := by omega
  unfold pl1 pr1 pleft pright at key
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with h2 | h2 <;>
    simp only [h1, h2] at key <;>
    simp only [hxm, hym, h1, h2] <;> norm_num <;> simp at key
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rwa [show (x / 2).toNat = x.toNat / 2 by omega, show (y / 2).toNat = y.toNat / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rw [hry h2]
    rwa [show (x / 2).toNat = x.toNat / 2 by omega, show ((y - 1) / 2).toNat = (y.toNat - 1) / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rw [hrx h1]
    rwa [show ((x + 1) / 2).toNat = (x.toNat + 1) / 2 by omega, show (y / 2).toNat = y.toNat / 2 by omega]
  · refine ⟨by omega, by omega, ?_, by omega⟩
    rw [hrx h1, hry h2]
    rwa [show ((x + 1) / 2).toNat = (x.toNat + 1) / 2 by omega,
      show ((y - 1) / 2).toNat = (y.toNat - 1) / 2 by omega]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem anc_level (N h j x u : Nat) (hN : N = 2 ^ h) (hx : x < 2 * N) (hj : 1 ≤ j) (e : j = x / 2 ^ u) (t : Nat)
    (hxt : x * 2 ^ t < 2 * N) : t + u ≤ h := by
  by_contra hc
  have h1 : x < 2 ^ u := by
    have : 2 * N ≤ 2 ^ t * 2 ^ u := by rw [← pow_add, hN, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp := Nat.two_pow_pos t
    by_contra h2; push_neg at h2
    have : 2 ^ t * 2 ^ u ≤ x * 2 ^ t := by rw [Nat.mul_comm (2 ^ t)]; exact Nat.mul_le_mul_right _ h2
    omega
  have : x / 2 ^ u = 0 := Nat.div_eq_of_lt h1
  omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem read_eq_left (A : Act M F) (st0 st : cp.LazySegmentTree M F) (L R h : Nat)
    (hI : PInvS A st0 (Cut L R h h) st) (hN : st0.n_node.toNat = 2 ^ h) (hL : L < 2 * st0.n_node.toNat)
    (t x : Nat) (hx : x = (L + 2 ^ t - 1) / 2 ^ t) (hodd : x % 2 = 1) (hx2 : x * 2 ^ t < 2 * st0.n_node.toNat) :
    st.node[x]! = virt A (nodeF st) (lazyF st) x := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  have hxl : x < 2 * st0.n_node.toNat := by have := Nat.two_pow_pos t; nlinarith
  simp only [virt]
  rw [P_of_idTag A _ x _ (gS.1 x hxl)]
  · rfl
  · intro j hj ⟨u, hu, e⟩
    obtain ⟨r1, r2⟩ := read_left L t x u hx hodd hu
    have hle := anc_level _ h j x u hN hxl hj e.symm t hx2
    exact gP j ⟨t + u, by omega, hle, Or.inl ⟨r2, by rw [← e, r1]⟩⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem read_eq_right (A : Act M F) (st0 st : cp.LazySegmentTree M F) (L R h : Nat)
    (hI : PInvS A st0 (Cut L R h h) st) (hN : st0.n_node.toNat = 2 ^ h) (hR : R ≤ 2 * st0.n_node.toNat)
    (t y : Nat) (hy : y = R / 2 ^ t) (hodd : y % 2 = 1) :
    st.node[y - 1]! = virt A (nodeF st) (lazyF st) (y - 1) := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  have hp := Nat.two_pow_pos t
  have hyR : y * 2 ^ t ≤ R := by rw [hy]; exact Nat.div_mul_le_self R _
  have hyl : y - 1 < 2 * st0.n_node.toNat := by
    have : y ≤ y * 2 ^ t := Nat.le_mul_of_pos_right _ hp
    omega
  simp only [virt]
  rw [P_of_idTag A _ (y - 1) _ (gS.1 _ hyl)]
  · rfl
  · intro j hj ⟨u, hu, e⟩
    obtain ⟨r1, r2⟩ := read_right R t y u hy hodd hu
    have hle := anc_level _ h j (y - 1) u hN hyl hj e.symm t (by
      have : (y - 1) * 2 ^ t < y * 2 ^ t := Nat.mul_lt_mul_of_pos_right (by omega) hp
      omega)
    exact gP j ⟨t + u, by omega, hle, Or.inr ⟨r2, by rw [← e, r1]⟩⟩

theorem cond_iff (x : Int) (i : Int) (hx : 0 ≤ x) :
    (shl (shr x i) i ≠ x) ↔ (x.toNat % 2 ^ i.toNat ≠ 0) := by
  rw [shr_nat x i hx]
  simp only [shl]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp only [Int.toNat_natCast]
  have key : ((n / 2 ^ i.toNat : Nat) : Int) * (2 : Int) ^ i.toNat = ((n / 2 ^ i.toNat * 2 ^ i.toNat : Nat) : Int) := by
    push_cast; ring
  rw [key, ne_eq, ne_eq, Nat.cast_inj]
  constructor
  · intro h hm; exact h (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm))
  · intro h he; apply h; exact Nat.mod_eq_zero_of_dvd ⟨n / 2 ^ i.toNat, by rw [Nat.mul_comm]; exact he.symm⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem lvl_bounds (N h x s : Nat) (hN : N = 2 ^ h) (hx1 : N ≤ x) (hx2 : x < 2 * N) (hs : s ≤ h) :
    2 ^ (h - s) ≤ x / 2 ^ s ∧ x / 2 ^ s < 2 ^ (h + 1 - s) := by
  constructor
  · apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h - s + s = h by omega]; omega
  · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h + 1 - s + s = h + 1 by omega, pow_succ]; omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem cut_lt (N h L R m j : Nat) (hN : N = 2 ^ h) (hL : N ≤ L) (hLR : L < R) (hR : R ≤ 2 * N)
    (hc : Cut L R h m j) : j < 2 ^ m := by
  obtain ⟨s, hs1, hs2, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hc
  · have := (lvl_bounds N h L s hN hL (by omega) hs2).2
    have : 2 ^ (h + 1 - s) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have := (lvl_bounds N h (R - 1) s hN (by omega) (by omega) hs2).2
    have : 2 ^ (h + 1 - s) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem cut_succ (L R h m j : Nat) (hm : m < h) (hc : Cut L R h (m + 1) j) :
    Cut L R h m j ∨ (L % 2 ^ (h - m) ≠ 0 ∧ j = L / 2 ^ (h - m)) ∨
      (R % 2 ^ (h - m) ≠ 0 ∧ j = (R - 1) / 2 ^ (h - m)) := by
  obtain ⟨s, hs1, hs2, hor⟩ := hc
  by_cases e : s = h - m
  · subst e; rcases hor with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · exact Or.inl ⟨s, by omega, hs2, hor⟩

/-- Pushing the node of level `h - m` above `x` keeps the invariant when the trivial-tag set lies above it. -/
theorem pinvs_push_lvl (A : Act M F) (st0 st r : cp.LazySegmentTree M F) (S : Nat → Prop) (h m x : Nat)
    (hN : st0.n_node.toNat = 2 ^ h) (hx1 : st0.n_node.toNat ≤ x) (hx2 : x < 2 * st0.n_node.toNat) (hm : m < h)
    (hI : PInvS A st0 S st) (hS : ∀ j, S j → j < 2 ^ (m + 1))
    (hn : (fun i => r.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) (x / 2 ^ (h - m)))
    (hz : (fun i => r.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat (x / 2 ^ (h - m)))
    (h1 : r.node.size = st.node.size) (h2 : r.lazy.size = st.lazy.size) (h3 : r.n = st.n)
    (h4 : r.n_node = st.n_node) (h5 : r.h_node = st.h_node) :
    PInvS A st0 (fun j => S j ∨ j = x / 2 ^ (h - m)) ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ := by
  have hb := lvl_bounds _ h x (h - m) hN hx1 hx2 (by omega)
  rw [show h - (h - m) = m by omega, show h + 1 - (h - m) = m + 1 by omega] at hb
  have hm1 : 2 ^ (m + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine pinvs_push A st0 st r S _ hI (by have := Nat.one_le_two_pow (n := m); omega) (by omega) ?_ hn hz h1 h2 h3 h4 h5
  intro j hj
  have := hS j hj
  rw [pow_succ] at this
  omega

theorem pinvs_close (A : Act M F) (st0 st : cp.LazySegmentTree M F) (S : Nat → Prop) (L R H m : Nat) (hm : m < H)
    (hI : PInvS A st0 S st) (h0 : ∀ j, Cut L R H m j → S j) (h1 : L % 2 ^ (H - m) ≠ 0 → S (L / 2 ^ (H - m)))
    (h2 : R % 2 ^ (H - m) ≠ 0 → S ((R - 1) / 2 ^ (H - m))) : PInvS A st0 (Cut L R H (m + 1)) st := by
  apply pinvs_mono A st0 st S _ hI
  intro j hj
  rcases cut_succ L R H m j hm hj with hc | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact h0 j hc
  · exact h1 c
  · exact h2 c

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem pinvs_init (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (L R H : Nat) :
    PInvS A st (Cut L R H 0) ⟨st.n, st.n_node, st.h_node, st.node, st.lazy⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun _ _ => rfl, fun j ⟨s, h1, h2, _⟩ => by omega⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem pinvs_valid (A : Act M F) (st0 st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st0 v)
    (S : Nat → Prop) (hI : PInvS A st0 S st) : LValid A st v := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  refine ⟨by rw [g1]; exact hv.n, by rw [g2]; exact hv.nn, by rw [g3]; exact hv.hn, by rw [g2, g3]; exact hv.shape,
    by rw [g4, g2]; exact hv.size, by rw [g5, g2]; exact hv.lsize, by rw [g2]; exact gS, ?_, ?_⟩
  · intro i hi
    have hb : st0.n_node.toNat + i < 2 * st0.n_node.toNat := by
      rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
      · simp [h1] at hi
      · omega
    rw [g2, gV _ hb]; exact hv.leaf i hi
  · intro j h1 h2
    rw [g2] at h2 ⊢
    rw [gV _ (by omega)]; exact hv.pad j h1 h2

theorem cond_eq_iff (x : Int) (i : Int) (hx : 0 ≤ x) :
    (shl (shr x i) i = x) ↔ (x.toNat % 2 ^ i.toNat = 0) := by
  have := cond_iff x i hx
  constructor
  · intro h; by_contra c; exact this.mpr c h
  · intro h; by_contra c; exact this.mp c h

/-- The facts at the level `cur` of the two-sided push loop over the boundaries `x` and `y`. -/
theorem two_level {h cur : Int} {pref suff : List Int} (Hr : rangeDown 1 h = pref ++ cur :: suff) (x y : Int)
    (N : Nat) (hN : N = 2 ^ h.toNat) (hx0 : 0 ≤ x) (hx1 : N ≤ x.toNat) (hxy : x < y) (hy : y.toNat ≤ 2 * N) :
    ∃ m, pref.length = m ∧ m < h.toNat ∧
      shr x cur = ((x.toNat / 2 ^ (h.toNat - m) : Nat) : Int) ∧
      shr (y - 1) cur = (((y.toNat - 1) / 2 ^ (h.toNat - m) : Nat) : Int) ∧
      ((¬ shl (shr x cur) cur = x) ↔ x.toNat % 2 ^ (h.toNat - m) ≠ 0) ∧
      ((shl (shr x cur) cur = x) ↔ x.toNat % 2 ^ (h.toNat - m) = 0) ∧
      ((¬ shl (shr y cur) cur = y) ↔ y.toNat % 2 ^ (h.toNat - m) ≠ 0) ∧
      ((shl (shr y cur) cur = y) ↔ y.toNat % 2 ^ (h.toNat - m) = 0) := by
  obtain ⟨e, c1, c2, cl⟩ := level_cursor Hr
  have hc : cur.toNat = h.toNat - pref.length := by omega
  refine ⟨pref.length, rfl, cl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shr_nat x cur hx0, hc]
  · rw [shr_nat (y - 1) cur (by omega), hc, show (y - 1).toNat = y.toNat - 1 by omega]
  · rw [← hc]; exact cond_iff x cur hx0
  · rw [← hc]; exact cond_eq_iff x cur hx0
  · rw [← hc]; exact cond_iff y cur (by omega)
  · rw [← hc]; exact cond_eq_iff y cur (by omega)

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem lrf_leaves (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (l k : Nat)
    (hk : l + k ≤ v.length) :
    rf A.m (virt A (nodeF st) (lazyF st)) (st.n_node.toNat + l) k = rf A.m (fun i => v[i]!) l k := by
  rw [rf_shift]
  apply rf_congr
  intro j _ hj
  exact hv.leaf j (by omega)

theorem cursor_arith (x y : Int) (R N t : Nat) (h0 : 0 ≤ x) (hxy : x < y) (hyR : y.toNat * 2 ^ t ≤ R)
    (hR : R ≤ 2 * N) :
    x.toNat < 2 * N ∧ x.toNat * 2 ^ t < 2 * N ∧ y.toNat - 1 < 2 * N ∧ x.toNat < y.toNat := by
  have hpt := Nat.two_pow_pos t
  have hyle : y.toNat ≤ y.toNat * 2 ^ t := Nat.le_mul_of_pos_right _ hpt
  have hxy' : x.toNat < y.toNat := by omega
  have hxt : x.toNat * 2 ^ t < y.toNat * 2 ^ t := Nat.mul_lt_mul_of_pos_right hxy' hpt
  have hxle : x.toNat ≤ x.toNat * 2 ^ t := Nat.le_mul_of_pos_right _ hpt
  exact ⟨by omega, by omega, by omega, hxy'⟩

theorem pl1_half (x : Int) (h0 : 0 ≤ x) :
    (x % 2 ≠ 0 → ((x + 1) / 2).toNat = pl1 x.toNat / 2) ∧ (x % 2 = 0 → (x / 2).toNat = pl1 x.toNat / 2) := by
  unfold pl1; constructor <;> intro c <;> split <;> omega

theorem pr1_half (y : Int) (h0 : 0 ≤ y) :
    (y % 2 ≠ 0 → ((y - 1) / 2).toNat = pr1 y.toNat / 2) ∧ (y % 2 = 0 → (y / 2).toNat = pr1 y.toNat / 2) := by
  unfold pr1; constructor <;> intro c <;> split <;> omega

set_option maxHeartbeats 1000000 in
theorem lproduct_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29) (l r : Int)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ v.length) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.product st l r
    ⦃⇓ res c => ⌜res.1 = rf A.m (fun i => v[i]!) l.toNat (r - l).toNat ∧ LValid A res.2 v ∧
      c ≤ t0 + 2 + 2 * cE + cOp + st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) +
        (st.h_node.toNat + 1) * (1 + 2 * cOp)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  have hshape : l < r → st.n_node.toNat = 2 ^ st.h_node.toNat ∧ 1 ≤ st.h_node ∧ v.length ≤ st.n_node.toNat := by
    intro hlt
    rcases hv.shape with ⟨h1, _⟩ | ⟨h1, h2, h3, -⟩
    · simp [h1] at hr; omega
    · exact ⟨h1, h2, h3⟩
  set V0 := virt A (nodeF st) (lazyF st) with hV0
  set N := st.n_node.toNat with hNd
  set L := (l + st.n_node).toNat with hL
  set R := (r + st.n_node).toNat with hR
  set T := rf A.m V0 L (r - l).toNat with hT
  set H := st.h_node.toNat with hH
  mvcgen [cp.LazySegmentTree.product, hP, hE, hOp]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', node', lazy'⟩ c =>
      ⌜PInvS A st (Cut L R H xs.prefix.length) ⟨n', nn', hh', node', lazy'⟩ ∧
        c ≤ t0 + 1 + xs.prefix.length * (7 + 4 * cA + 4 * cC + 2 * cI)⌝
  case vc19.inv =>
    exact ⟨fun ⟨l', r', lo, ro⟩ c => ⌜∃ t, l'.toNat = (L + 2 ^ t - 1) / 2 ^ t ∧ r'.toNat = R / 2 ^ t ∧
              0 ≤ l' ∧ 0 ≤ r' ∧ PInv A.m V0 N T l'.toNat r'.toNat lo ro ∧ t ≤ H + 1 ∧
              c ≤ t0 + 1 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + 2 * cE + t * (1 + 2 * cOp)⌝,
           fun ⟨_, _, lo, ro⟩ c => ⌜A.m.op lo ro = T ∧
              c ≤ t0 + 2 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + 2 * cE + (H + 1) * (1 + 2 * cOp)⌝,
           fun ⟨l', r', _, _⟩ => (r' - l').toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹ℤ × ℤ × M × M›).2.2.2 = ro at *
    generalize (‹ℤ × ℤ × M × M›).2.2.1 = lo at *
    generalize (‹ℤ × ℤ × M × M›).2.1 = y at *
    generalize (‹ℤ × ℤ × M × M›).1 = x at *)
  case vc18.isTrue.isFalse.pre => exact ⟨pinvs_init A st v hv _ _ _, by omega⟩
  case vc2.a | vc3.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node) _ hN (by omega) (by omega) (by omega)
    simp at g2; omega
  case vc12.a | vc13.a | vc6.a | vc7.a =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (r + st.n_node - 1) _ hN (by omega) (by omega) (by omega)
    first
      | omega
      | (obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›; simp at g2; omega)
      | (obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
         obtain ⟨-, -, -, -, -, e2, -⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
         simp at g2; omega)
  case vc4.a | vc5.a | vc14.a | vc15.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc8.a | vc9.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨-, -, e1, e2, -, e4, -⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [e1, e4, g4, g2]; exact hsz) | (rw [e2, e4, g5, g2]; exact hlz)
  case vc10.step.isTrue.post.success.isTrue.post.success =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, bc⟩ :=
      ‹(fun i => _) = pushA A (fun i => (_ : cp.LazySegmentTree M F).node[i]!) _ _ ∧ _›
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ (l + st.n_node).toNat hN (by omega) (by omega) hm hI hS0 a1 a2 a3 a4 a5
      a6 a7
    have P2 := pinvs_push_lvl A st _ _ _ _ _ ((r + st.n_node).toNat - 1) hN (by omega) (by omega) hm P1
      (fun j hj => by rcases hj with hj | rfl; exacts [hS0 j hj, hk1]) b1 b2 b3 b4 b5 b6 b7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P2 (fun j hj => Or.inl (Or.inl hj)) (fun _ => Or.inl (Or.inr rfl))
      (fun _ => Or.inr rfl), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc11.step.isTrue.post.success.isFalse =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ (l + st.n_node).toNat hN (by omega) (by omega) hm hI hS0 a1 a2 a3 a4 a5
      a6 a7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P1 (fun j hj => Or.inl hj) (fun _ => Or.inr rfl)
      (fun c => absurd ‹_ % _ = 0› c), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc16.step.isFalse.isTrue.post.success =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, bc⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    have P2 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ ((r + st.n_node).toNat - 1) hN (by omega) (by omega) hm hI hS0 b1 b2 b3 b4 b5
      b6 b7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P2 (fun j hj => Or.inl hj) (fun c => absurd ‹_ % _ = 0› c)
      (fun _ => Or.inr rfl), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc17.step.isFalse.isFalse =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm hI (fun j hj => hj)
      (fun c => absurd ‹(l + st.n_node).toNat % _ = 0› c) (fun c => absurd ‹(r + st.n_node).toNat % _ = 0› c), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc21.step.isFalse.isTrue.isTrue | vc22.step.isFalse.isTrue.isFalse | vc23.step.isFalse.isFalse.isTrue |
      vc24.step.isFalse.isFalse.isFalse =>
    rename_i hby hbx hlt' hex
    obtain ⟨t, hx, hy, h0, h1, hPI, ht, hc⟩ := hex
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hyR : y.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by rw [hy]; exact Nat.div_mul_le_self _ _
    have hx1 := hPI.1
    have hRN : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hLN : (l + st.n_node).toNat < 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hxy' : x < y := hlt'
    obtain ⟨hxN, hxN2, hyN, hxyN⟩ := cursor_arith x y _ _ t h0 hxy' hyR hRN
    obtain ⟨hI, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    have hlen : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hlen] at hI
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    have gV := hI.2.2.2.2.2.2.1
    have hrx : x.toNat % 2 = 1 → nd'[x.toNat]! = virt A (nodeF st) (lazyF st) x.toNat := fun hodd =>
      (read_eq_left A st ⟨n', nn', hh', nd', lz'⟩ (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat hI hN
        hLN t x.toNat hx hodd hxN2).trans (gV x.toNat hxN)
    have hry : y.toNat % 2 = 1 → nd'[y.toNat - 1]! = virt A (nodeF st) (lazyF st) (y.toNat - 1) := by
      intro hodd
      have e1 := read_eq_right A st ⟨n', nn', hh', nd', lz'⟩ (l + st.n_node).toNat (r + st.n_node).toNat
        st.h_node.toNat hI hN hRN t y.toNat hy hodd
      have e2 := gV (y.toNat - 1) hyN
      exact e1.trans e2
    have key := lprod_step A.m nd' _ _ _ hVV hTr x y lo ro h0 hxy' hPI hrx hry
    clear hrx hry gV
    clear hI hVV hTr hst
    have hlx := land_one x h0
    have hly := land_one y h1
    have cl := cursor_left _ t _ hx
    have cr := cursor_right _ t _ hy
    have htH : t ≤ st.h_node.toNat := by
      have h2 : 2 * 2 ^ t ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hN]
        calc 2 * 2 ^ t ≤ y.toNat * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := le_trans hyR hRN
      have : 2 ^ t ≤ 2 ^ st.h_node.toNat := by omega
      exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp this
    have gl1 : x % 2 ≠ 0 → (shr (x + 1) 1).toNat = ((l + st.n_node).toNat + 2 ^ (t + 1) - 1) / 2 ^ (t + 1) := by
      intro c; rw [shr_one, (pl1_half x h0).1 c, cl]
    have gl0 : x % 2 = 0 → (shr x 1).toNat = ((l + st.n_node).toNat + 2 ^ (t + 1) - 1) / 2 ^ (t + 1) := by
      intro c; rw [shr_one, (pl1_half x h0).2 c, cl]
    have gr1 : y % 2 ≠ 0 → (shr (y - 1) 1).toNat = (r + st.n_node).toNat / 2 ^ (t + 1) := by
      intro c; rw [shr_one, (pr1_half y h1).1 c, cr]
    have gr0 : y % 2 = 0 → (shr y 1).toNat = (r + st.n_node).toNat / 2 ^ (t + 1) := by
      intro c; rw [shr_one, (pr1_half y h1).2 c, cr]
    have hcost : (t + 1) * (1 + 2 * cOp) = t * (1 + 2 * cOp) + (1 + 2 * cOp) := by ring
    clear cl cr
    rw [hlx] at hbx
    rw [hly] at hby
    simp only [hlx, hly, hbx, hby, ne_eq, not_false_eq_true, ite_true, ite_false, not_true_eq_false] at key
    obtain ⟨k1, k2, k3, k4⟩ := key
    refine ⟨⟨t + 1, ?_, ?_, k1, k2, k3, by omega, ?_⟩, k4, hxy'⟩
    · first | exact gl1 hbx | exact gl0 hbx
    · first | exact gr1 hby | exact gr0 hby
    · clear k3 hPI; omega
  case vc20.step.isTrue =>
    obtain ⟨t, hx, hy, h0, h1, hPI, ht, hc⟩ := ‹∃ t, _›
    refine ⟨PInv_exit A.m _ _ _ _ _ _ _ hPI (by omega), ?_⟩
    have : t * (1 + 2 * cOp) ≤ (st.h_node.toNat + 1) * (1 + 2 * cOp) := Nat.mul_le_mul_right _ ht
    omega
  case vc25.isTrue.isFalse.post.success.pre =>
    obtain ⟨-, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    have hlen : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hlen] at hc
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hb : (l + st.n_node).toNat + (r - l).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hRL : (r + st.n_node).toNat - (l + st.n_node).toNat = (r - l).toNat := by clear * - hlt hl hnn; omega
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hrV := rf_V A.m _ _ hVV (r - l).toNat (l + st.n_node).toNat hb
    clear hVV hst
    have hN1 : 1 ≤ st.n_node.toNat := by rw [hN]; exact Nat.one_le_two_pow
    have p1 : 1 ≤ (l + st.n_node).toNat := by clear * - hN1 hl hnn; omega
    have p2 : (l + st.n_node).toNat ≤ (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have p3 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have p4 : 0 ≤ l + st.n_node := by clear * - hl hnn; omega
    have p5 : 0 ≤ r + st.n_node := by clear * - hlt hl hnn; omega
    have p6 : (r - l).toNat < fuel := by
      have : (r - l).toNat < 2 ^ 30 := by clear * - hlt hl hr hsmall; omega
      exact lt_trans this (by unfold fuel; norm_num)
    refine ⟨⟨0, by simp, by simp, p4, p5, ⟨p1, p2, p3, A.m.he, A.m.he, ?_⟩, Nat.zero_le _,
      by clear * - hc; omega⟩, p6⟩
    rw [hRL, A.m.lid _ hrV, A.m.rid _ hrV]
  case vc26.isTrue.isFalse.post.success.post.success =>
    obtain ⟨hI, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨e, hc⟩ := ‹A.m.op _ _ = _ ∧ _›
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    refine ⟨?_, pinvs_valid A st _ v hv _ hI, by omega⟩
    rw [e, show (l + st.n_node).toNat = st.n_node.toNat + l.toNat by omega]
    simpa using lrf_leaves A st v hv l.toNat (r - l).toNat (by clear * - hl hlr hr; omega)
  case vc1.isTrue.isTrue =>
    refine ⟨?_, hv, by omega⟩
    rw [show (r - l).toNat = 0 by omega]; rfl
  case vc28.isFalse => omega

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

section
variable {M F : Type}

open Classical in
/-- The invariant of the loop applying `f` to the canonical nodes: outside the boundary ancestors `Cut L R H H` the
tree invariant holds, those carry trivial tags, and the leaves in `[L, lo)` and `[hi, R)` have received `f`. -/
def UInv (A : Act M F) (a : Nat → M) (z : Nat → F) (N H L R : Nat) (V0 : Nat → M) (f : F) (lo hi : Nat) : Prop :=
  AllV A.m a (2 * N) ∧ AllVF A z N ∧ RTInv A a z N (Cut L R H H) ∧ (∀ j, Cut L R H H j → IdTag A (z j)) ∧
    ∀ p, N ≤ p → p < 2 * N → virt A a z p = if (L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R) then A.ap f (V0 p) else V0 p

open Classical in
theorem uinv_apply (A : Act M F) (a : Nat → M) (z : Nat → F) (N H L R : Nat) (V0 : Nat → M) (f : F) (hf : A.VF f)
    (lo hi c t lo' hi' : Nat) (hN : N = 2 ^ H) (hU : UInv A a z N H L R V0 f lo hi) (ht : t ≤ H)
    (hc1 : 2 ^ (H - t) ≤ c) (hc2 : c < 2 ^ (H + 1 - t)) (hcB : ¬ Cut L R H H c)
    (hanc : ∀ j, 1 ≤ j → SAnc j c → Cut L R H H j)
    (hnew : ∀ p, N ≤ p → p < 2 * N → p / 2 ^ t = c → ¬ ((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R)))
    (hcond : ∀ p, N ≤ p → p < 2 * N →
      (((L ≤ p ∧ p < lo') ∨ (hi' ≤ p ∧ p < R)) ↔ (((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R)) ∨ p / 2 ^ t = c))) :
    UInv A (applyA A a c f) (applyZ A z N c f) N H L R V0 f lo' hi' := by
  obtain ⟨hV, hz, hT, hB, hL⟩ := hU
  have hc0 : 1 ≤ c := le_trans Nat.one_le_two_pow hc1
  have hcN : c < 2 * N := by
    have : 2 ^ (H + 1 - t) ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases e : k = c
    · subst e; simp only [applyA, ite_true]; exact A.ap_V _ _ hf (hV k hk)
    · simp only [applyA, e, ite_false]; exact hV k hk
  · intro k h1 h2
    by_cases e : k = c ∧ c < N
    · simp only [applyZ, e, and_self, ite_true]; exact A.hcomp _ _ hf (hz c (by omega) e.2)
    · simp only [applyZ, e, ite_false]; exact hz k h1 h2
  · intro k h1 h2 hk
    have hch : 2 * k ≠ c ∧ 2 * k + 1 ≠ c := by
      constructor <;> intro e <;> exact hk (hanc k h1 ⟨1, le_refl _, by simp; omega⟩)
    have ha1 : applyA A a c f (2 * k) = a (2 * k) := by simp [applyA, hch.1]
    have ha2 : applyA A a c f (2 * k + 1) = a (2 * k + 1) := by simp [applyA, hch.2]
    rw [ha1, ha2]
    by_cases e : k = c
    · subst e
      have hx : A.m.V (A.m.op (a (2 * k)) (a (2 * k + 1))) := A.m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
      simp only [applyA, applyZ, h2, and_self, ite_true]
      rw [hT k h1 h2 hk, A.ap_comp _ _ _ hf (hz k h1 h2) hx]
    · simp only [applyA, applyZ, e, false_and, ite_false]
      exact hT k h1 h2 hk
  · intro j hj
    have : j ≠ c := fun e => hcB (e ▸ hj)
    simp only [applyZ, this, false_and, ite_false]
    exact hB j hj
  · intro p hp1 hp2
    rw [virt_apply_leaf A a z N c f hf hV hz hc0 hcN (fun j h1 h2 => hB j (hanc j h1 h2)) p hp1 hp2]
    have hb := below_iff N H t c p hN ht hc1 hc2 hp1 hp2
    by_cases e : p / 2 ^ t = c
    · have h1 := hnew p hp1 hp2 e
      have h2 : (L ≤ p ∧ p < lo') ∨ (hi' ≤ p ∧ p < R) := (hcond p hp1 hp2).mpr (Or.inr e)
      rw [if_pos (hb.mpr e), hL p hp1 hp2, if_neg h1, if_pos h2]
    · rw [if_neg (fun h => e (hb.mp h)), hL p hp1 hp2]
      have : ((L ≤ p ∧ p < lo') ∨ (hi' ≤ p ∧ p < R)) ↔ ((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R)) := by
        rw [hcond p hp1 hp2]; simp [e]
      simp only [this]

/-- The values after `update(k)`. -/
def updA (A : Act M F) (a : Nat → M) (k : Nat) : Nat → M := fun j =>
  if j = k then A.m.op (a (2 * k)) (a (2 * k + 1)) else a j

theorem rtinv_recompute (A : Act M F) (a : Nat → M) (z : Nat → F) (N k : Nat) (S S' : Nat → Prop)
    (hV : AllV A.m a (2 * N)) (hR : RTInv A a z N S) (hk1 : 1 ≤ k) (hkN : k < N) (hid : IdTag A (z k))
    (hS : ∀ j, S j → S' j ∨ j = k) (hpar : k = 1 ∨ S' (k / 2)) :
    RTInv A (updA A a k) z N S' ∧ AllV A.m (updA A a k) (2 * N) ∧
      ∀ p, N ≤ p → virt A (updA A a k) z p = virt A a z p := by
  refine ⟨?_, ?_, ?_⟩
  · intro j h1 h2 hj
    by_cases e : j = k
    · subst e
      have hx : A.m.V (A.m.op (a (2 * j)) (a (2 * j + 1))) := A.m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
      simp only [updA, ite_true, show 2 * j ≠ j by omega, show 2 * j + 1 ≠ j by omega, ite_false]
      exact (hid _ hx).symm
    · have hnS : ¬ S j := fun h => (hS j h).elim hj e
      have hc : 2 * j ≠ k ∧ 2 * j + 1 ≠ k := by
        constructor <;> intro e' <;> rcases hpar with hp | hp
        · omega
        · exact hj (by rwa [show k / 2 = j by omega] at hp)
        · omega
        · exact hj (by rwa [show k / 2 = j by omega] at hp)
      simp only [updA, e, hc.1, hc.2, ite_false]
      exact hR j h1 h2 hnS
  · intro j hj
    by_cases e : j = k
    · subst e; simp only [updA, ite_true]; exact A.m.closed _ _ (hV _ (by omega)) (hV _ (by omega))
    · simp only [updA, e, ite_false]; exact hV j hj
  · intro p hp
    simp only [virt, updA, show p ≠ k by omega, ite_false]

theorem div_iff (p x d : Nat) (hd : 0 < d) : p / d = x ↔ x * d ≤ p ∧ p < (x + 1) * d := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self _ _, by
      have := Nat.div_add_mod p d; have := Nat.mod_lt p hd; rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega⟩
  · rintro ⟨h1, h2⟩
    have a1 : x ≤ p / d := (Nat.le_div_iff_mul_le hd).mpr h1
    have a2 : p / d < x + 1 := (Nat.div_lt_iff_lt_mul hd).mpr h2
    omega

theorem ceil_facts (L d : Nat) (hd : 0 < d) :
    L ≤ (L + d - 1) / d * d ∧ L / d ≤ (L + d - 1) / d ∧ (L % d ≠ 0 → (L + d - 1) / d = L / d + 1) := by
  have h1 := Nat.div_add_mod (L + d - 1) d
  have h2 := Nat.mod_lt (L + d - 1) hd
  have h3 := Nat.div_add_mod L d
  have h4 := Nat.mod_lt L hd
  refine ⟨by rw [Nat.mul_comm]; omega, Nat.div_le_div_right (by omega), fun h => ?_⟩
  have : (L + d - 1) / d = L / d + 1 := by
    rw [div_iff _ _ _ hd]
    constructor
    · rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.add_mul, one_mul, Nat.mul_comm]; omega
  exact this

theorem floor_pred (R d : Nat) (hd : 0 < d) (h : R % d ≠ 0) : (R - 1) / d = R / d := by
  rw [div_iff _ _ _ hd]
  have h3 := Nat.div_add_mod R d
  have h4 := Nat.mod_lt R hd
  constructor
  · rw [Nat.mul_comm]; omega
  · rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega

/-- The level of a node: the nodes `x / 2 ^ s` above the leaves have level `s`. -/
theorem cut_level (N H L R s j : Nat) (hN : N = 2 ^ H) (hL : N ≤ L) (hLR : L < R) (hR : R ≤ 2 * N) (hs : s ≤ H)
    (h : (L % 2 ^ s ≠ 0 ∧ j = L / 2 ^ s) ∨ (R % 2 ^ s ≠ 0 ∧ j = (R - 1) / 2 ^ s)) :
    2 ^ (H - s) ≤ j ∧ j < 2 ^ (H - s + 1) := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · have := lvl_bounds' N H L s hN hL (by omega) hs
    rw [show H - s + 1 = H + 1 - s by omega]; exact this
  · have := lvl_bounds' N H (R - 1) s hN (by omega) (by omega) hs
    rw [show H - s + 1 = H + 1 - s by omega]; exact this

theorem not_cut_of (N H L R t c : Nat) (hN : N = 2 ^ H) (hL : N ≤ L) (hLR : L < R) (hR : R ≤ 2 * N) (ht : t ≤ H)
    (hc1 : 2 ^ (H - t) ≤ c) (hc2 : c < 2 ^ (H - t + 1))
    (hl : L % 2 ^ t ≠ 0 → c ≠ L / 2 ^ t) (hr : R % 2 ^ t ≠ 0 → c ≠ (R - 1) / 2 ^ t) : ¬ Cut L R H H c := by
  rintro ⟨s, hs1, hs2, h⟩
  have hb := cut_level N H L R s c hN hL hLR hR hs2 h
  have e : H - s = H - t := dyadic_unique _ _ c hb.1 hb.2 hc1 hc2
  have : s = t := by omega
  subst this
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hl h1 h2
  · exact hr h1 h2

theorem left_cover (N H L R t x y lo hi : Nat) (hN : N = 2 ^ H) (hL : N ≤ L) (hLR : L < R) (hR : R ≤ 2 * N)
    (hx : x = (L + 2 ^ t - 1) / 2 ^ t) (hy : y = R / 2 ^ t) (hxy : x < y) (hodd : x % 2 = 1)
    (hlo : lo = x * 2 ^ t) (hhi1 : (x + 1) * 2 ^ t ≤ hi) (hhi2 : hi ≤ R) :
    t ≤ H ∧ 2 ^ (H - t) ≤ x ∧ x < 2 ^ (H + 1 - t) ∧ ¬ Cut L R H H x ∧
      (∀ j, 1 ≤ j → SAnc j x → Cut L R H H j) ∧
      (∀ p, N ≤ p → p < 2 * N → p / 2 ^ t = x → ¬ ((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R))) ∧
      (∀ p, N ≤ p → p < 2 * N → (((L ≤ p ∧ p < (x + 1) * 2 ^ t) ∨ (hi ≤ p ∧ p < R)) ↔
        (((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R)) ∨ p / 2 ^ t = x))) := by
  have hpt := Nat.two_pow_pos t
  obtain ⟨c1, c2, c3⟩ := ceil_facts L (2 ^ t) hpt
  rw [← hx] at c1 c2 c3
  have hyR : y * 2 ^ t ≤ R := by rw [hy]; exact Nat.div_mul_le_self _ _
  have hx1 : 1 ≤ x := by
    have : 1 ≤ L := by have := Nat.one_le_two_pow (n := H); omega
    by_contra h0; have : x = 0 := by omega
    rw [this] at c1; omega
  have hxt : x * 2 ^ t < y * 2 ^ t := Nat.mul_lt_mul_of_pos_right hxy hpt
  have hxle : x ≤ x * 2 ^ t := Nat.le_mul_of_pos_right _ hpt
  have e1 : (x + 1) * 2 ^ t = x * 2 ^ t + 2 ^ t := by ring
  have ht : t ≤ H := by
    have : 2 * 2 ^ t ≤ 2 * 2 ^ H := by
      calc 2 * 2 ^ t ≤ y * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * 2 ^ H := by omega
    exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
  have hb := lvl_bounds' N H L t hN hL (by omega) ht
  have hyb : y < 2 ^ (H + 1 - t) + 1 := by
    have := lvl_bounds' N H (R - 1) t hN (by omega) (by omega) ht
    have : y ≤ (R - 1) / 2 ^ t + 1 := by
      rw [hy]
      have := Nat.div_add_mod R (2 ^ t); have := Nat.div_add_mod (R - 1) (2 ^ t)
      have := Nat.mod_lt R hpt; have := Nat.mod_lt (R - 1) hpt
      by_contra hc
      have : (R - 1) / 2 ^ t + 2 ≤ R / 2 ^ t := by omega
      have : ((R - 1) / 2 ^ t + 2) * 2 ^ t ≤ R / 2 ^ t * 2 ^ t := Nat.mul_le_mul_right _ this
      rw [Nat.add_mul, Nat.mul_comm (R / 2 ^ t)] at this
      rw [Nat.mul_comm ((R - 1) / 2 ^ t)] at this
      omega
    omega
  refine ⟨ht, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · apply not_cut_of N H L R t x hN hL hLR hR ht (by omega) (by rw [show H - t + 1 = H + 1 - t by omega]; omega)
    · intro h e; have := c3 h; omega
    · intro h e; rw [floor_pred R _ hpt h, ← hy] at e; omega
  · rintro j hj ⟨u, hu, e⟩
    obtain ⟨r1, r2⟩ := read_left L t x u hx hodd hu
    have hle := anc_level N H j x u hN (by omega) hj e.symm t (by omega)
    exact ⟨t + u, by omega, hle, Or.inl ⟨r2, by rw [← e, r1]⟩⟩
  · intro p _ _ e
    rw [div_iff _ _ _ hpt] at e
    omega
  · intro p _ _
    rw [div_iff _ _ _ hpt]
    omega

theorem right_cover (N H L R t x y lo : Nat) (hN : N = 2 ^ H) (hL : N ≤ L) (hLR : L < R) (hR : R ≤ 2 * N)
    (hx : x = (L + 2 ^ t - 1) / 2 ^ t) (hy : y = R / 2 ^ t) (hxy : x ≤ y - 1) (hodd : y % 2 = 1)
    (hlo1 : L ≤ lo) (hlo2 : lo ≤ (y - 1) * 2 ^ t) :
    t ≤ H ∧ 2 ^ (H - t) ≤ y - 1 ∧ y - 1 < 2 ^ (H + 1 - t) ∧ ¬ Cut L R H H (y - 1) ∧
      (∀ j, 1 ≤ j → SAnc j (y - 1) → Cut L R H H j) ∧
      (∀ p, N ≤ p → p < 2 * N → p / 2 ^ t = y - 1 → ¬ ((L ≤ p ∧ p < lo) ∨ (y * 2 ^ t ≤ p ∧ p < R))) ∧
      (∀ p, N ≤ p → p < 2 * N → (((L ≤ p ∧ p < lo) ∨ ((y - 1) * 2 ^ t ≤ p ∧ p < R)) ↔
        (((L ≤ p ∧ p < lo) ∨ (y * 2 ^ t ≤ p ∧ p < R)) ∨ p / 2 ^ t = y - 1))) := by
  have hpt := Nat.two_pow_pos t
  obtain ⟨c1, c2, c3⟩ := ceil_facts L (2 ^ t) hpt
  rw [← hx] at c1 c2 c3
  have hyR : y * 2 ^ t ≤ R := by rw [hy]; exact Nat.div_mul_le_self _ _
  have hx1 : 1 ≤ x := by
    have : 1 ≤ L := by have := Nat.one_le_two_pow (n := H); omega
    by_contra h0; have : x = 0 := by omega
    rw [this] at c1; omega
  have hy1 : (y - 1) * 2 ^ t < y * 2 ^ t := Nat.mul_lt_mul_of_pos_right (by omega) hpt
  have hyle : y - 1 ≤ (y - 1) * 2 ^ t := Nat.le_mul_of_pos_right _ hpt
  have ht : t ≤ H := by
    have : 2 * 2 ^ t ≤ 2 * 2 ^ H := by
      calc 2 * 2 ^ t ≤ y * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * 2 ^ H := by omega
    exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
  have hb := lvl_bounds' N H L t hN hL (by omega) ht
  have hyb : y ≤ 2 ^ (H + 1 - t) := by
    have : y * 2 ^ t ≤ 2 ^ (H + 1 - t) * 2 ^ t := by
      rw [← pow_add, show H + 1 - t + t = H + 1 by omega, pow_succ]; omega
    exact Nat.le_of_mul_le_mul_right this hpt
  refine ⟨ht, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · apply not_cut_of N H L R t (y - 1) hN hL hLR hR ht (by omega) (by rw [show H - t + 1 = H + 1 - t by omega]; omega)
    · intro h e; have := c3 h; omega
    · intro h e; rw [floor_pred R _ hpt h, ← hy] at e; omega
  · rintro j hj ⟨u, hu, e⟩
    obtain ⟨r1, r2⟩ := read_right R t y u hy hodd hu
    have hle := anc_level N H j (y - 1) u hN (by omega) hj e.symm t (by omega)
    exact ⟨t + u, by omega, hle, Or.inr ⟨r2, by rw [← e, r1]⟩⟩
  · intro p _ _ e
    rw [div_iff _ _ _ hpt, show y - 1 + 1 = y by omega] at e
    omega
  · intro p _ _
    rw [div_iff _ _ _ hpt, show y - 1 + 1 = y by omega]
    omega

open Classical in
theorem uinv_mono (A : Act M F) (a : Nat → M) (z : Nat → F) (N H L R : Nat) (V0 : Nat → M) (f : F)
    (lo hi lo' hi' : Nat) (hU : UInv A a z N H L R V0 f lo hi)
    (h : ∀ p, N ≤ p → p < 2 * N →
      (((L ≤ p ∧ p < lo) ∨ (hi ≤ p ∧ p < R)) ↔ ((L ≤ p ∧ p < lo') ∨ (hi' ≤ p ∧ p < R)))) :
    UInv A a z N H L R V0 f lo' hi' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hU
  refine ⟨h1, h2, h3, h4, fun p hp1 hp2 => ?_⟩
  rw [h5 p hp1 hp2]
  simp only [h p hp1 hp2]

theorem rtinv_mono (A : Act M F) (a : Nat → M) (z : Nat → F) (N : Nat) (S S' : Nat → Prop)
    (hR : RTInv A a z N S) (h : ∀ j, S j → S' j) : RTInv A a z N S' :=
  fun k h1 h2 hk => hR k h1 h2 (fun hs => hk (h k hs))

/-- The boundary ancestors at the levels `≥ i` after recomputing the left one at level `i`. -/
def CutR (L R H i : Nat) (j : Nat) : Prop := Cut L R H (H - i) j ∨ (R % 2 ^ i ≠ 0 ∧ j = (R - 1) / 2 ^ i)

theorem mod_succ_ne (L i : Nat) (h : L % 2 ^ i ≠ 0) : L % 2 ^ (i + 1) ≠ 0 := by
  intro h2
  apply h
  have : 2 ^ i ∣ L := Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ i)) (Nat.dvd_of_mod_eq_zero h2)
  exact Nat.mod_eq_zero_of_dvd this

theorem level_left (A : Act M F) (a : Nat → M) (z : Nat → F) (N H L R i : Nat) (hN : N = 2 ^ H) (hL : N ≤ L)
    (hLR : L < R) (hR : R ≤ 2 * N) (hi1 : 1 ≤ i) (hiH : i ≤ H) (hV : AllV A.m a (2 * N))
    (hT : RTInv A a z N (Cut L R H (H + 1 - i))) (hB : ∀ j, Cut L R H H j → IdTag A (z j)) :
    (L % 2 ^ i ≠ 0 → RTInv A (updA A a (L / 2 ^ i)) z N (CutR L R H i) ∧ AllV A.m (updA A a (L / 2 ^ i)) (2 * N) ∧
      ∀ p, N ≤ p → virt A (updA A a (L / 2 ^ i)) z p = virt A a z p) ∧
    (L % 2 ^ i = 0 → RTInv A a z N (CutR L R H i)) := by
  have hb := lvl_bounds' N H L i hN hL (by omega) hiH
  have hm : H + 1 - i = (H - i) + 1 := by omega
  rw [hm] at hT
  constructor
  · intro hc
    have hk1 : 1 ≤ L / 2 ^ i := le_trans Nat.one_le_two_pow hb.1
    have hkN : L / 2 ^ i < N := by
      have : 2 ^ (H + 1 - i) ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply rtinv_recompute A a z N _ _ _ hV hT hk1 hkN (hB _ ⟨i, by omega, hiH, Or.inl ⟨hc, rfl⟩⟩)
    · intro j hj
      rcases cut_succ L R H (H - i) j (by omega) hj with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inl h)
      · right; rw [h2, show H - (H - i) = i by omega]
      · rw [show H - (H - i) = i by omega] at h1 h2; exact Or.inl (Or.inr ⟨h1, h2⟩)
    · by_cases hiH' : i = H
      · left; subst hiH'
        have := lvl_bounds' N i L i hN hL (by omega) (le_refl _)
        simp at this; omega
      · right; left
        refine ⟨i + 1, by omega, by omega, Or.inl ⟨mod_succ_ne L i hc, ?_⟩⟩
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
  · intro hc
    apply rtinv_mono A a z N _ _ hT
    intro j hj
    rcases cut_succ L R H (H - i) j (by omega) hj with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · rw [show H - (H - i) = i by omega] at h1; exact absurd hc h1
    · rw [show H - (H - i) = i by omega] at h1 h2; exact Or.inr ⟨h1, h2⟩

theorem level_right (A : Act M F) (a : Nat → M) (z : Nat → F) (N H L R i : Nat) (hN : N = 2 ^ H) (hL : N ≤ L)
    (hLR : L < R) (hR : R ≤ 2 * N) (hi1 : 1 ≤ i) (hiH : i ≤ H) (hV : AllV A.m a (2 * N))
    (hT : RTInv A a z N (CutR L R H i)) (hB : ∀ j, Cut L R H H j → IdTag A (z j)) :
    (R % 2 ^ i ≠ 0 → RTInv A (updA A a ((R - 1) / 2 ^ i)) z N (Cut L R H (H - i)) ∧
      AllV A.m (updA A a ((R - 1) / 2 ^ i)) (2 * N) ∧
      ∀ p, N ≤ p → virt A (updA A a ((R - 1) / 2 ^ i)) z p = virt A a z p) ∧
    (R % 2 ^ i = 0 → RTInv A a z N (Cut L R H (H - i))) := by
  have hb := lvl_bounds' N H (R - 1) i hN (by omega) (by omega) hiH
  constructor
  · intro hc
    have hk1 : 1 ≤ (R - 1) / 2 ^ i := le_trans Nat.one_le_two_pow hb.1
    have hkN : (R - 1) / 2 ^ i < N := by
      have : 2 ^ (H + 1 - i) ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply rtinv_recompute A a z N _ _ _ hV hT hk1 hkN (hB _ ⟨i, by omega, hiH, Or.inr ⟨hc, rfl⟩⟩)
    · intro j hj
      rcases hj with h | ⟨-, h2⟩
      · exact Or.inl h
      · exact Or.inr h2
    · by_cases hiH' : i = H
      · left; subst hiH'
        have := lvl_bounds' N i (R - 1) i hN (by omega) (by omega) (le_refl _)
        simp at this; omega
      · right
        refine ⟨i + 1, by omega, by omega, Or.inr ⟨mod_succ_ne R i hc, ?_⟩⟩
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
  · intro hc
    apply rtinv_mono A a z N _ _ hT
    intro j hj
    rcases hj with h | ⟨h1, -⟩
    · exact h
    · exact absurd hc h1

end

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem allApply_fun (A : Act M F) (st : cp.LazySegmentTree M F) (k : Int) (f : F) (hk0 : 0 ≤ k)
    (hks : k.toNat < st.node.size) (hlz : st.lazy.size = st.n_node.toNat) :
    nodeF (allApplyS A st k f) = applyA A (nodeF st) k.toNat f ∧
      lazyF (allApplyS A st k f) = applyZ A (lazyF st) st.n_node.toNat k.toNat f ∧
      (allApplyS A st k f).node.size = st.node.size ∧ (allApplyS A st k f).lazy.size = st.lazy.size ∧
      (allApplyS A st k f).n = st.n ∧ (allApplyS A st k f).n_node = st.n_node ∧
      (allApplyS A st k f).h_node = st.h_node := by
  refine ⟨?_, ?_, by simp [allApplyS], ?_, rfl, rfl, rfl⟩
  · funext i
    simp only [nodeF, allApplyS, getB_set, applyA, get_eq]
    by_cases e : i = k.toNat
    · subst e; simp [hks]
    · simp [e]
  · funext i
    simp only [lazyF, allApplyS, applyZ]
    by_cases hk : k < st.n_node
    · simp only [hk, ite_true, getB_set, get_eq]
      by_cases e : i = k.toNat
      · subst e; simp [hlz]; try omega
      · simp [e]
    · have : ¬ k.toNat < st.n_node.toNat := by omega
      simp [hk, this]
  · simp only [allApplyS]; split <;> simp

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
theorem upd_fun (A : Act M F) (st : cp.LazySegmentTree M F) (k : Int) (hk0 : 0 ≤ k)
    (hks : k.toNat < st.node.size) :
    nodeF { st with node := Cpp.set st.node k (A.m.op (Cpp.get st.node (k * 2)) (Cpp.get st.node (k * 2 + 1))) } =
      updA A (nodeF st) k.toNat := by
  funext i
  simp only [nodeF, getB_set, updA, get_eq]
  by_cases e : i = k.toNat
  · subst e
    simp only [hks, and_self, ite_true]
    rw [show (k * 2).toNat = 2 * k.toNat by omega, show (k * 2 + 1).toNat = 2 * k.toNat + 1 by omega]
  · simp [e]

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
theorem mapIdx_getB (v : List M) (g : Nat → M → M) (i : Nat) (hi : i < v.length) :
    (v.mapIdx g)[i]! = g i v[i]! := by
  have h1 : (v.mapIdx g)[i]? = some (g i v[i]!) := by
    rw [List.getElem?_mapIdx]
    simp [List.getElem?_eq_getElem hi, hi]
  rw [getElem!_pos (v.mapIdx g) i (by simpa using hi)]
  rw [List.getElem?_eq_getElem (by simpa using hi)] at h1
  simpa using h1

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
open Classical in
theorem urange_valid (A : Act M F) (st st' : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v)
    (l r : Nat) (f : F) (hr : r ≤ v.length) (e1 : st'.n = st.n) (e2 : st'.n_node = st.n_node)
    (e3 : st'.h_node = st.h_node) (s1 : st'.node.size = 2 * st.n_node.toNat)
    (s2 : st'.lazy.size = st.n_node.toNat) (hV : AllV A.m (nodeF st') (2 * st.n_node.toNat))
    (hz : AllVF A (lazyF st') st.n_node.toNat) (hT : RTInv A (nodeF st') (lazyF st') st.n_node.toNat (fun _ => False))
    (hL : ∀ p, st.n_node.toNat ≤ p → p < 2 * st.n_node.toNat →
      virt A (nodeF st') (lazyF st') p = if st.n_node.toNat + l ≤ p ∧ p < st.n_node.toNat + r then
        A.ap f (virt A (nodeF st) (lazyF st) p) else virt A (nodeF st) (lazyF st) p) :
    LValid A st' (v.mapIdx fun j x => if l ≤ j ∧ j < r then A.ap f x else x) := by
  have hlen : v.length ≤ st.n_node.toNat := by
    rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
    · simp [h1]
    · exact h3
  have hsh : (v.mapIdx fun j x => if l ≤ j ∧ j < r then A.ap f x else x) = [] ∧ st'.n_node = 0 ∧ st'.h_node = 0 ∨
      (st'.n_node.toNat = 2 ^ st'.h_node.toNat ∧ 1 ≤ st'.h_node ∧
        (v.mapIdx fun j x => if l ≤ j ∧ j < r then A.ap f x else x).length ≤ st'.n_node.toNat ∧
        (st'.h_node = 1 ∨ 2 ^ (st'.h_node.toNat - 1) <
          (v.mapIdx fun j x => if l ≤ j ∧ j < r then A.ap f x else x).length)) := by
    simp only [e2, e3, List.length_mapIdx]
    rcases hv.shape with ⟨h1, h2, h3⟩ | h
    · left; exact ⟨by simp [h1], h2, h3⟩
    · right; exact h
  refine ⟨by simp [e1, hv.n], by rw [e2]; exact hv.nn, by rw [e3]; exact hv.hn, hsh, by rw [s1, e2],
    by rw [s2, e2], ?_, ?_, ?_⟩
  · rw [e2]; exact ⟨hV, hz, fun k h1 h2 => hT k h1 h2 id⟩
  · intro i hi
    simp only [List.length_mapIdx] at hi
    rw [e2, hL _ (by omega) (by omega), mapIdx_getB v _ i hi, hv.leaf i hi]
    by_cases c : l ≤ i ∧ i < r
    · rw [if_pos (by omega), if_pos c]
    · rw [if_neg (by omega), if_neg c]
  · intro j h1 h2
    simp only [List.length_mapIdx] at h1
    rw [e2] at h2 ⊢
    rw [hL _ (by omega) (by omega), if_neg (by omega)]
    exact hv.pad j h1 h2

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem allApplyC_le (st : cp.LazySegmentTree M F) (k : Int) (cC cA : Nat) : allApplyC st k cC cA ≤ 1 + cA + cC := by
  simp only [allApplyC]; split <;> omega

/-- The state facts kept by the loop over the canonical nodes. -/
def Kept (st0 st : cp.LazySegmentTree M F) : Prop :=
  st.n = st0.n ∧ st.n_node = st0.n_node ∧ st.h_node = st0.h_node ∧ st.node.size = 2 * st0.n_node.toNat ∧
    st.lazy.size = st0.n_node.toNat

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem lstep_left (A : Act M F) (st0 st1 : cp.LazySegmentTree M F) (f : F) (hf : A.VF f) (V0 : Nat → M)
    (H L R t hi : Nat) (x y : Int) (hN : st0.n_node.toNat = 2 ^ H) (hL : st0.n_node.toNat ≤ L) (hLR : L < R)
    (hR : R ≤ 2 * st0.n_node.toNat) (hK : Kept st0 st1) (hx : x.toNat = (L + 2 ^ t - 1) / 2 ^ t)
    (hy : y.toNat = R / 2 ^ t) (h0 : 0 ≤ x) (hxy : x < y) (hodd : land x 1 ≠ 0)
    (hU : UInv A (nodeF st1) (lazyF st1) st0.n_node.toNat H L R V0 f (x.toNat * 2 ^ t) hi)
    (hhi1 : (x.toNat + 1) * 2 ^ t ≤ hi) (hhi2 : hi ≤ R) :
    Kept st0 (allApplyS A st1 x f) ∧
      UInv A (nodeF (allApplyS A st1 x f)) (lazyF (allApplyS A st1 x f)) st0.n_node.toNat H L R V0 f
        ((x.toNat + 1) * 2 ^ t) hi := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := hK
  have hodd' : x.toNat % 2 = 1 := by rw [land_one x h0] at hodd; omega
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := left_cover _ H L R t x.toNat y.toNat _ hi hN hL hLR hR hx hy (by omega) hodd'
    rfl hhi1 hhi2
  have hc2N : x.toNat < 2 * st0.n_node.toNat := by
    have : 2 ^ (H + 1 - t) ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := allApply_fun A st1 x f h0 (by omega) (by rw [k5, k2])
  refine ⟨⟨by rw [f5, k1], by rw [f6, k2], by rw [f7, k3], by rw [f3, k4], by rw [f4, k5]⟩, ?_⟩
  rw [f1, f2, k2]
  exact uinv_apply A _ _ _ H L R V0 f hf _ _ _ t _ _ hN hU c1 c2 c3 c4 c5 c6 c7

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem lstep_right (A : Act M F) (st0 st1 : cp.LazySegmentTree M F) (f : F) (hf : A.VF f) (V0 : Nat → M)
    (H L R t lo : Nat) (y : Int) (hN : st0.n_node.toNat = 2 ^ H) (hL : st0.n_node.toNat ≤ L) (hLR : L < R)
    (hR : R ≤ 2 * st0.n_node.toNat) (hK : Kept st0 st1) (hxy : (L + 2 ^ t - 1) / 2 ^ t ≤ y.toNat - 1)
    (hy : y.toNat = R / 2 ^ t) (h0 : 0 ≤ y) (hodd : land y 1 ≠ 0)
    (hU : UInv A (nodeF st1) (lazyF st1) st0.n_node.toNat H L R V0 f lo (y.toNat * 2 ^ t))
    (hlo1 : L ≤ lo) (hlo2 : lo ≤ (y.toNat - 1) * 2 ^ t) :
    Kept st0 (allApplyS A st1 (y - 1) f) ∧
      UInv A (nodeF (allApplyS A st1 (y - 1) f)) (lazyF (allApplyS A st1 (y - 1) f)) st0.n_node.toNat H L R V0 f
        lo ((y.toNat - 1) * 2 ^ t) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := hK
  have hodd' : y.toNat % 2 = 1 := by rw [land_one y h0] at hodd; omega
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := right_cover _ H L R t _ y.toNat lo hN hL hLR hR rfl hy hxy hodd' hlo1 hlo2
  have hc2N : y.toNat - 1 < 2 * st0.n_node.toNat := by
    have : 2 ^ (H + 1 - t) ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := allApply_fun A st1 (y - 1) f (by omega) (by omega) (by rw [k5, k2])
  refine ⟨⟨by rw [f5, k1], by rw [f6, k2], by rw [f7, k3], by rw [f3, k4], by rw [f4, k5]⟩, ?_⟩
  rw [f1, f2, k2, show (y - 1).toNat = y.toNat - 1 by omega]
  exact uinv_apply A _ _ _ H L R V0 f hf _ _ _ t _ _ hN hU c1 c2 c3 c4 c5 c6 c7

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem pinvs_uinv (A : Act M F) (st st' : cp.LazySegmentTree M F) (f : F) (L R H : Nat)
    (hsz : st.node.size = 2 * st.n_node.toNat) (hlz : st.lazy.size = st.n_node.toNat)
    (hI : PInvS A st (Cut L R H H) st') :
    Kept st st' ∧ UInv A (nodeF st') (lazyF st') st.n_node.toNat H L R (virt A (nodeF st) (lazyF st)) f L R := by
  obtain ⟨g1, g2, g3, g4, g5, ⟨s1, s2, s3⟩, gV, gP⟩ := hI
  refine ⟨⟨g1, g2, g3, by rw [g4, hsz], by rw [g5, hlz]⟩, s1, s2, fun k h1 h2 _ => s3 k h1 h2, gP, fun p hp1 hp2 => ?_⟩
  rw [gV p hp2, ite_eq_right_iff.mpr (fun h => by omega)]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem cursor_next (L R t : Nat) (x y : Int) (h0 : 0 ≤ x) (h1 : 0 ≤ y) (hx : x.toNat = (L + 2 ^ t - 1) / 2 ^ t)
    (hy : y.toNat = R / 2 ^ t) :
    (land x 1 ≠ 0 → x.toNat % 2 = 1 ∧ (shr (x + 1) 1).toNat = (L + 2 ^ (t + 1) - 1) / 2 ^ (t + 1) ∧
      (shr (x + 1) 1).toNat * 2 ^ (t + 1) = (x.toNat + 1) * 2 ^ t ∧ 0 ≤ shr (x + 1) 1 ∧
      (shr (x + 1) 1).toNat = (x.toNat + 1) / 2) ∧
    (land x 1 = 0 → (shr x 1).toNat = (L + 2 ^ (t + 1) - 1) / 2 ^ (t + 1) ∧
      (shr x 1).toNat * 2 ^ (t + 1) = x.toNat * 2 ^ t ∧ 0 ≤ shr x 1 ∧ (shr x 1).toNat = x.toNat / 2) ∧
    (land y 1 ≠ 0 → y.toNat % 2 = 1 ∧ (shr (y - 1) 1).toNat = R / 2 ^ (t + 1) ∧
      (shr (y - 1) 1).toNat * 2 ^ (t + 1) = (y.toNat - 1) * 2 ^ t ∧ 0 ≤ shr (y - 1) 1 ∧
      (shr (y - 1) 1).toNat = (y.toNat - 1) / 2) ∧
    (land y 1 = 0 → (shr y 1).toNat = R / 2 ^ (t + 1) ∧ (shr y 1).toNat * 2 ^ (t + 1) = y.toNat * 2 ^ t ∧
      0 ≤ shr y 1 ∧ (shr y 1).toNat = y.toNat / 2) := by
  have n1 : 0 ≤ shr (x + 1) 1 := by rw [shr_one]; omega
  have n2 : 0 ≤ shr x 1 := by rw [shr_one]; omega
  have n4 : 0 ≤ shr y 1 := by rw [shr_one]; omega
  have cl := cursor_left L t x.toNat hx
  have cr := cursor_right R t y.toNat hy
  unfold pl1 at cl
  unfold pr1 at cr
  have m1 : (shr (x + 1) 1).toNat = (x.toNat + 1) / 2 := by rw [shr_one]; omega
  have m2 : (shr x 1).toNat = x.toNat / 2 := by rw [shr_one]; omega
  have m4 : (shr y 1).toNat = y.toNat / 2 := by rw [shr_one]; omega
  rw [land_one x h0, land_one y h1]
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · have hm : x.toNat % 2 = 1 := by omega
    rw [if_pos hm] at cl
    refine ⟨hm, by rw [m1, cl], ?_, n1, m1⟩
    rw [m1, pow_succ', ← Nat.mul_assoc, show (x.toNat + 1) / 2 * 2 = x.toNat + 1 by omega]
  · have hm : ¬ x.toNat % 2 = 1 := by omega
    rw [if_neg hm] at cl
    refine ⟨by rw [m2, cl], ?_, n2, m2⟩
    rw [m2, pow_succ', ← Nat.mul_assoc, show x.toNat / 2 * 2 = x.toNat by omega]
  · have hm : y.toNat % 2 = 1 := by omega
    have n3 : 0 ≤ shr (y - 1) 1 := by rw [shr_one]; omega
    have m3 : (shr (y - 1) 1).toNat = (y.toNat - 1) / 2 := by rw [shr_one]; omega
    rw [if_pos hm] at cr
    refine ⟨hm, by rw [m3, cr], ?_, n3, m3⟩
    rw [m3, pow_succ', ← Nat.mul_assoc, show (y.toNat - 1) / 2 * 2 = y.toNat - 1 by omega]
  · have hm : ¬ y.toNat % 2 = 1 := by omega
    rw [if_neg hm] at cr
    refine ⟨by rw [m4, cr], ?_, n4, m4⟩
    rw [m4, pow_succ', ← Nat.mul_assoc, show y.toNat / 2 * 2 = y.toNat by omega]

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
theorem upd_arr (A : Act M F) (nd : Array M) (k : Int) (hk0 : 0 ≤ k) (hks : k.toNat < nd.size) :
    (fun i => (Cpp.set nd k (A.m.op (Cpp.get nd (k * 2)) (Cpp.get nd (k * 2 + 1))))[i]!) =
      updA A (fun i => nd[i]!) k.toNat ∧
    (Cpp.set nd k (A.m.op (Cpp.get nd (k * 2)) (Cpp.get nd (k * 2 + 1)))).size = nd.size := by
  refine ⟨?_, by simp⟩
  funext i
  simp only [getB_set, updA, get_eq]
  by_cases e : i = k.toNat
  · subst e
    simp only [hks, and_self, ite_true]
    rw [show (k * 2).toNat = 2 * k.toNat by omega, show (k * 2 + 1).toNat = 2 * k.toNat + 1 by omega]
  · simp [e]

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
theorem mapIdx_cond (A : Act M F) (v : List M) (l r : Int) (f : F) (hl : 0 ≤ l) :
    (v.mapIdx fun j x => if l ≤ (j : Int) ∧ (j : Int) < r then A.ap f x else x) =
      v.mapIdx fun j x => if l.toNat ≤ j ∧ j < r.toNat then A.ap f x else x := by
  congr 1; funext j x
  by_cases c : l ≤ (j : Int) ∧ (j : Int) < r
  · rw [if_pos c, if_pos (by omega)]
  · rw [if_neg c, if_neg (by omega)]

omit [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] [Cpp.AdlCall2 "op" M M M] in
theorem mapIdx_empty (A : Act M F) (v : List M) (l : Int) (f : F) :
    (v.mapIdx fun j x => if l ≤ (j : Int) ∧ (j : Int) < l then A.ap f x else x) = v := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  rw [if_neg (by omega)]

set_option maxHeartbeats 1000000 in
theorem update_range_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29) (l r : Int)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ v.length) (f : F) (hf : A.VF f) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.update_int_int_F st l r f
    ⦃⇓ res c => ⌜LValid A res (v.mapIdx fun j x => if l.toNat ≤ j ∧ j < r.toNat then A.ap f x else x) ∧
      c ≤ t0 + 3 + st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) + (st.h_node.toNat + 1) * (3 + 2 * cA + 2 * cC) +
        st.h_node.toNat * (3 + 2 * cOp)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hU : ∀ (st : cp.LazySegmentTree M F) (i : Int) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (A.m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.LazySegmentTree.update_int st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.LazySegmentTree.update_int, hOp]
  have hAA : ∀ (st : cp.LazySegmentTree M F) (k : Int) (f : F) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 (allApplyS A st k f) (c + allApplyC st k cC cA)⦄ cp.LazySegmentTree.all_apply st k f ⦃Q⦄ :=
    fun st k f => all_apply_spec A cE cOp cI cC cA hO st k f
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  have hshape : l < r → st.n_node.toNat = 2 ^ st.h_node.toNat ∧ 1 ≤ st.h_node ∧ v.length ≤ st.n_node.toNat := by
    intro hlt
    rcases hv.shape with ⟨h1, _⟩ | ⟨h1, h2, h3, -⟩
    · simp [h1] at hr; omega
    · exact ⟨h1, h2, h3⟩
  set V0 := virt A (nodeF st) (lazyF st) with hV0
  set N := st.n_node.toNat with hNd
  set L := (l + st.n_node).toNat with hL
  set R := (r + st.n_node).toNat with hR
  set H := st.h_node.toNat with hH
  mvcgen [cp.LazySegmentTree.update_int_int_F, hP, hU, hAA]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', node', lazy'⟩ c =>
      ⌜PInvS A st (Cut L R H xs.prefix.length) ⟨n', nn', hh', node', lazy'⟩ ∧
        c ≤ t0 + 1 + xs.prefix.length * (7 + 4 * cA + 4 * cC + 2 * cI)⌝
  case vc19.inv =>
    exact ⟨fun ⟨n', nn', hh', nd', lz', x, y⟩ c => ⌜n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧
              nd'.size = 2 * N ∧ lz'.size = N ∧ ∃ t, x.toNat = (L + 2 ^ t - 1) / 2 ^ t ∧ y.toNat = R / 2 ^ t ∧
              0 ≤ x ∧ 0 ≤ y ∧ x ≤ y ∧ t ≤ H + 1 ∧
              UInv A (fun i => nd'[i]!) (fun i => lz'[i]!) N H L R V0 f (x.toNat * 2 ^ t) (y.toNat * 2 ^ t) ∧
              c ≤ t0 + 1 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + t * (3 + 2 * cA + 2 * cC)⌝,
           fun ⟨n', nn', hh', nd', lz', _, _⟩ c => ⌜n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧
              nd'.size = 2 * N ∧ lz'.size = N ∧
              UInv A (fun i => nd'[i]!) (fun i => lz'[i]!) N H L R V0 f R R ∧
              c ≤ t0 + 2 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + (H + 1) * (3 + 2 * cA + 2 * cC)⌝,
           fun ⟨_, _, _, _, _, x, y⟩ => (y - x).toNat⟩
  case vc26.inv =>
    exact ⟨fun ⟨n', nn', hh', nd', lz', i⟩ c => ⌜n' = st.n ∧ nn' = st.n_node ∧ hh' = st.h_node ∧
              nd'.size = 2 * N ∧ lz'.size = N ∧ 1 ≤ i ∧ i ≤ st.h_node + 1 ∧
              AllV A.m (fun i => nd'[i]!) (2 * N) ∧ AllVF A (fun i => lz'[i]!) N ∧
              RTInv A (fun i => nd'[i]!) (fun i => lz'[i]!) N (Cut L R H (H + 1 - i.toNat)) ∧
              (∀ j, Cut L R H H j → IdTag A (lz'[j]!)) ∧
              (∀ p, N ≤ p → p < 2 * N → virt A (fun i => nd'[i]!) (fun i => lz'[i]!) p =
                if L ≤ p ∧ p < R then A.ap f (V0 p) else V0 p) ∧
              c ≤ t0 + 2 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + (H + 1) * (3 + 2 * cA + 2 * cC) +
                (i.toNat - 1) * (3 + 2 * cOp)⌝,
           fun ⟨n', nn', hh', nd', lz', _⟩ c =>
              ⌜LValid A ⟨n', nn', hh', nd', lz'⟩ (v.mapIdx fun j x => if l.toNat ≤ j ∧ j < r.toNat then A.ap f x else x) ∧
              c ≤ t0 + 3 + H * (7 + 4 * cA + 4 * cC + 2 * cI) + (H + 1) * (3 + 2 * cA + 2 * cC) + H * (3 + 2 * cOp)⌝,
           fun ⟨_, _, hh', _, _, i⟩ => (hh' + 1 - i).toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.2.2.2.2.2 = y at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.2.2.2.2.1 = x at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.2.2.2.1 = lz2 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.2.2.1 = nd2 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.2.1 = hh2 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).2.1 = nn2 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × ℤ›).1 = n2 at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.2 = i' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.2.1 = lz3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.2.1 = nd3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.2.1 = hh3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).2.1 = nn3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ›).1 = n3 at *)
  case vc18.isTrue.isFalse.pre => exact ⟨pinvs_init A st v hv _ _ _, by omega⟩
  case vc2.a | vc3.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node) _ hN (by omega) (by omega) (by omega)
    simp at g2; omega
  case vc12.a | vc13.a | vc6.a | vc7.a =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (r + st.n_node - 1) _ hN (by omega) (by omega) (by omega)
    first
      | omega
      | (obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›; simp at g2; omega)
      | (obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
         obtain ⟨-, -, -, -, -, e2, -⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
         simp at g2; omega)
  case vc4.a | vc5.a | vc14.a | vc15.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc8.a | vc9.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨-, -, e1, e2, -, e4, -⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [e1, e4, g4, g2]; exact hsz) | (rw [e2, e4, g5, g2]; exact hlz)
  case vc10.step.isTrue.post.success.isTrue.post.success =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, bc⟩ :=
      ‹(fun i => _) = pushA A (fun i => (_ : cp.LazySegmentTree M F).node[i]!) _ _ ∧ _›
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ (l + st.n_node).toNat hN (by omega) (by omega) hm hI hS0 a1 a2 a3 a4 a5
      a6 a7
    have P2 := pinvs_push_lvl A st _ _ _ _ _ ((r + st.n_node).toNat - 1) hN (by omega) (by omega) hm P1
      (fun j hj => by rcases hj with hj | rfl; exacts [hS0 j hj, hk1]) b1 b2 b3 b4 b5 b6 b7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P2 (fun j hj => Or.inl (Or.inl hj)) (fun _ => Or.inl (Or.inr rfl))
      (fun _ => Or.inr rfl), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc11.step.isTrue.post.success.isFalse =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ (l + st.n_node).toNat hN (by omega) (by omega) hm hI hS0 a1 a2 a3 a4 a5
      a6 a7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P1 (fun j hj => Or.inl hj) (fun _ => Or.inr rfl)
      (fun c => absurd ‹_ % _ = 0› c), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc16.step.isFalse.isTrue.post.success =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, bc⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    have P2 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ ((r + st.n_node).toNat - 1) hN (by omega) (by omega) hm hI hS0 b1 b2 b3 b4 b5
      b6 b7
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm P2 (fun j hj => Or.inl hj) (fun c => absurd ‹_ % _ = 0› c)
      (fun _ => Or.inr rfl), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc17.step.isFalse.isFalse =>
    obtain ⟨hN, hh1, hle⟩ := hshape (by omega)
    obtain ⟨m, hm1, hm, e1, e2, c1, c2, c3, c4⟩ := two_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node)
      (r + st.n_node) _ hN (by omega) (by omega) (by omega) (by omega)
    simp only [hm1] at *
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp only [c1, c2, c3, c4] at *
    try simp only [e1, e2] at *
    try simp only [Int.toNat_natCast] at *
    have hS0 : ∀ j, Cut (l + st.n_node).toNat (r + st.n_node).toNat st.h_node.toNat m j → j < 2 ^ (m + 1) :=
      fun j hj => by
        have := cut_lt _ _ _ _ _ j hN (by omega) (by omega) (by omega) hj
        rw [pow_succ]; omega
    have hk1 := (lvl_bounds _ _ (l + st.n_node).toNat (st.h_node.toNat - m) hN (by omega) (by omega)
      (by omega)).2
    rw [show st.h_node.toNat + 1 - (st.h_node.toNat - m) = m + 1 by omega] at hk1
    refine ⟨pinvs_close A st _ _ _ _ _ _ hm hI (fun j hj => hj)
      (fun c => absurd ‹(l + st.n_node).toNat % _ = 0› c) (fun c => absurd ‹(r + st.n_node).toNat % _ = 0› c), ?_⟩
    have : (m + 1) * (7 + 4 * cA + 4 * cC + 2 * cI) = m * (7 + 4 * cA + 4 * cC + 2 * cI) + (7 + 4 * cA + 4 * cC + 2 * cI) := by
      ring
    omega
  case vc25.isTrue.isFalse.post.success.pre =>
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    have hlen : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hlen] at hI hc
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    obtain ⟨⟨k1, k2, k3, k4, k5⟩, hU⟩ := pinvs_uinv A st _ f _ _ _ hsz hlz hI
    have p6 : (r - l).toNat < fuel := by
      have : (r - l).toNat < 2 ^ 30 := by clear * - hlt hl hr hsmall; omega
      exact lt_trans this (by unfold fuel; norm_num)
    refine ⟨⟨k1, k2, k3, k4, k5, 0, by simp, by simp, by clear * - hl hnn; omega, by clear * - hlt hl hnn; omega,
      by clear * - hlt; omega, Nat.zero_le _, by simp only [pow_zero, Nat.mul_one]; exact hU,
      by clear * - hc; omega⟩, p6⟩
  case vc20.step.isTrue =>
    obtain ⟨e1, e2, e3, e4, e5, t, hx, hy, h0, h1, hxy, ht, hU, hc⟩ := ‹_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ ∃ t, _›
    have hxy' : x = y := by omega
    subst hxy'
    refine ⟨e1, e2, e3, e4, e5, uinv_mono A _ _ _ _ _ _ _ f _ _ _ _ hU (fun p _ _ => ?_), ?_⟩
    · have a1 : (l + st.n_node).toNat ≤ x.toNat * 2 ^ t := by
        rw [hx]; exact (ceil_facts _ _ (Nat.two_pow_pos t)).1
      have a2 : x.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by
        rw [hy]; exact Nat.div_mul_le_self _ _
      clear * - a1 a2; omega
    · have : t * (3 + 2 * cA + 2 * cC) ≤ (st.h_node.toNat + 1) * (3 + 2 * cA + 2 * cC) := Nat.mul_le_mul_right _ ht
      clear * - hc this; omega
  case vc21.step.isFalse.isTrue.isTrue =>
    rename_i hby hbx hlt' hinv
    obtain ⟨e1, e2, e3, e4, e5, t, hx, hy, h0, h1, hxy, ht, hU, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hK : Kept st ⟨n2, nn2, hh2, nd2, lz2⟩ := ⟨e1, e2, e3, e4, e5⟩
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    obtain ⟨cx1, cx0, cy1, cy0⟩ := cursor_next _ _ t x y h0 h1 hx hy
    have hpt := Nat.two_pow_pos t
    have hyR : y.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by rw [hy]; exact Nat.div_mul_le_self _ _
    have hLx : (l + st.n_node).toNat ≤ x.toNat * 2 ^ t := by rw [hx]; exact (ceil_facts _ _ hpt).1
    have hN1 : 1 ≤ st.n_node.toNat := by rw [hN]; exact Nat.one_le_two_pow
    have hx1 : 1 ≤ x.toNat := by
      by_contra hc0
      have : x.toNat = 0 := by omega
      rw [this] at hLx; omega
    have htH : t ≤ st.h_node.toNat := by
      have h2 : 2 * 2 ^ t ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hN]
        calc 2 * 2 ^ t ≤ y.toNat * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := le_trans hyR hR2
      exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    have hcost : (t + 1) * (3 + 2 * cA + 2 * cC) = t * (3 + 2 * cA + 2 * cC) + (3 + 2 * cA + 2 * cC) := by ring
    obtain ⟨ox, ex1, ex2, ex3, ex4⟩ := cx1 hbx
    obtain ⟨oy, ey1, ey2, ey3, ey4⟩ := cy1 hby
    have hxy2 : x.toNat + 2 ≤ y.toNat := by omega
    have a1 := allApplyC_le ⟨n2, nn2, hh2, nd2, lz2⟩ x cC cA
    obtain ⟨K1, U1⟩ := lstep_left A st ⟨n2, nn2, hh2, nd2, lz2⟩ f hf _ _ _ _ t (y.toNat * 2 ^ t) x y hN hNL hLR hR2 hK
      hx hy h0 hlt' hbx hU (Nat.mul_le_mul_right _ (by omega)) hyR
    generalize allApplyS A ⟨n2, nn2, hh2, nd2, lz2⟩ x f = s1 at *
    have a2 := allApplyC_le ⟨s1.n, s1.n_node, s1.h_node, s1.node, s1.lazy⟩ (y - 1) cC cA
    have hm1 : (x.toNat + 1) * 2 ^ t ≤ (y.toNat - 1) * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
    have hm0 : x.toNat * 2 ^ t ≤ (x.toNat + 1) * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨K2, U2⟩ := lstep_right A st ⟨s1.n, s1.n_node, s1.h_node, s1.node, s1.lazy⟩ f hf _ _ _ _ t
      ((x.toNat + 1) * 2 ^ t) y hN hNL hLR hR2 K1 (by omega) hy h1 hby U1 (by omega) hm1
    generalize allApplyS A ⟨s1.n, s1.n_node, s1.h_node, s1.node, s1.lazy⟩ (y - 1) f = s2 at *
    obtain ⟨k1, k2, k3, k4, k5⟩ := K2
    refine ⟨⟨k1, k2, k3, k4, k5, t + 1, ex1, ey1, ex3, ey3, by omega, by omega, ?_, by omega⟩, by omega⟩
    rw [ex2, ey2]; exact U2
  case vc22.step.isFalse.isTrue.isFalse =>
    rename_i hby hbx hlt' hinv
    obtain ⟨e1, e2, e3, e4, e5, t, hx, hy, h0, h1, hxy, ht, hU, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hK : Kept st ⟨n2, nn2, hh2, nd2, lz2⟩ := ⟨e1, e2, e3, e4, e5⟩
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    obtain ⟨cx1, cx0, cy1, cy0⟩ := cursor_next _ _ t x y h0 h1 hx hy
    have hpt := Nat.two_pow_pos t
    have hyR : y.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by rw [hy]; exact Nat.div_mul_le_self _ _
    have hLx : (l + st.n_node).toNat ≤ x.toNat * 2 ^ t := by rw [hx]; exact (ceil_facts _ _ hpt).1
    have hN1 : 1 ≤ st.n_node.toNat := by rw [hN]; exact Nat.one_le_two_pow
    have hx1 : 1 ≤ x.toNat := by
      by_contra hc0
      have : x.toNat = 0 := by omega
      rw [this] at hLx; omega
    have htH : t ≤ st.h_node.toNat := by
      have h2 : 2 * 2 ^ t ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hN]
        calc 2 * 2 ^ t ≤ y.toNat * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := le_trans hyR hR2
      exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    have hcost : (t + 1) * (3 + 2 * cA + 2 * cC) = t * (3 + 2 * cA + 2 * cC) + (3 + 2 * cA + 2 * cC) := by ring
    obtain ⟨ox, ex1, ex2, ex3, ex4⟩ := cx1 hbx
    obtain ⟨ey1, ey2, ey3, ey4⟩ := cy0 (by simpa using hby)
    have a1 := allApplyC_le ⟨n2, nn2, hh2, nd2, lz2⟩ x cC cA
    obtain ⟨K1, U1⟩ := lstep_left A st ⟨n2, nn2, hh2, nd2, lz2⟩ f hf _ _ _ _ t (y.toNat * 2 ^ t) x y hN hNL hLR hR2 hK
      hx hy h0 hlt' hbx hU (Nat.mul_le_mul_right _ (by omega)) hyR
    generalize allApplyS A ⟨n2, nn2, hh2, nd2, lz2⟩ x f = s1 at *
    obtain ⟨k1, k2, k3, k4, k5⟩ := K1
    refine ⟨⟨k1, k2, k3, k4, k5, t + 1, ex1, ey1, ex3, ey3, by omega, by omega, ?_, by omega⟩, by omega⟩
    rw [ex2, ey2]; exact U1
  case vc23.step.isFalse.isFalse.isTrue =>
    rename_i hby hbx hlt' hinv
    obtain ⟨e1, e2, e3, e4, e5, t, hx, hy, h0, h1, hxy, ht, hU, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hK : Kept st ⟨n2, nn2, hh2, nd2, lz2⟩ := ⟨e1, e2, e3, e4, e5⟩
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    obtain ⟨cx1, cx0, cy1, cy0⟩ := cursor_next _ _ t x y h0 h1 hx hy
    have hpt := Nat.two_pow_pos t
    have hyR : y.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by rw [hy]; exact Nat.div_mul_le_self _ _
    have hLx : (l + st.n_node).toNat ≤ x.toNat * 2 ^ t := by rw [hx]; exact (ceil_facts _ _ hpt).1
    have hN1 : 1 ≤ st.n_node.toNat := by rw [hN]; exact Nat.one_le_two_pow
    have hx1 : 1 ≤ x.toNat := by
      by_contra hc0
      have : x.toNat = 0 := by omega
      rw [this] at hLx; omega
    have htH : t ≤ st.h_node.toNat := by
      have h2 : 2 * 2 ^ t ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hN]
        calc 2 * 2 ^ t ≤ y.toNat * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := le_trans hyR hR2
      exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    have hcost : (t + 1) * (3 + 2 * cA + 2 * cC) = t * (3 + 2 * cA + 2 * cC) + (3 + 2 * cA + 2 * cC) := by ring
    obtain ⟨ex1, ex2, ex3, ex4⟩ := cx0 (by simpa using hbx)
    obtain ⟨oy, ey1, ey2, ey3, ey4⟩ := cy1 hby
    have a2 := allApplyC_le ⟨n2, nn2, hh2, nd2, lz2⟩ (y - 1) cC cA
    have hm1 : x.toNat * 2 ^ t ≤ (y.toNat - 1) * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨K2, U2⟩ := lstep_right A st ⟨n2, nn2, hh2, nd2, lz2⟩ f hf _ _ _ _ t (x.toNat * 2 ^ t) y hN hNL hLR hR2 hK
      (by omega) hy h1 hby hU hLx hm1
    generalize allApplyS A ⟨n2, nn2, hh2, nd2, lz2⟩ (y - 1) f = s2 at *
    obtain ⟨k1, k2, k3, k4, k5⟩ := K2
    refine ⟨⟨k1, k2, k3, k4, k5, t + 1, ex1, ey1, ex3, ey3, by omega, by omega, ?_, by omega⟩, by omega⟩
    rw [ex2, ey2]; exact U2
  case vc24.step.isFalse.isFalse.isFalse =>
    rename_i hby hbx hlt' hinv
    obtain ⟨e1, e2, e3, e4, e5, t, hx, hy, h0, h1, hxy, ht, hU, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hK : Kept st ⟨n2, nn2, hh2, nd2, lz2⟩ := ⟨e1, e2, e3, e4, e5⟩
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    obtain ⟨cx1, cx0, cy1, cy0⟩ := cursor_next _ _ t x y h0 h1 hx hy
    have hpt := Nat.two_pow_pos t
    have hyR : y.toNat * 2 ^ t ≤ (r + st.n_node).toNat := by rw [hy]; exact Nat.div_mul_le_self _ _
    have hLx : (l + st.n_node).toNat ≤ x.toNat * 2 ^ t := by rw [hx]; exact (ceil_facts _ _ hpt).1
    have hN1 : 1 ≤ st.n_node.toNat := by rw [hN]; exact Nat.one_le_two_pow
    have hx1 : 1 ≤ x.toNat := by
      by_contra hc0
      have : x.toNat = 0 := by omega
      rw [this] at hLx; omega
    have htH : t ≤ st.h_node.toNat := by
      have h2 : 2 * 2 ^ t ≤ 2 * 2 ^ st.h_node.toNat := by
        rw [← hN]
        calc 2 * 2 ^ t ≤ y.toNat * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := le_trans hyR hR2
      exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    have hcost : (t + 1) * (3 + 2 * cA + 2 * cC) = t * (3 + 2 * cA + 2 * cC) + (3 + 2 * cA + 2 * cC) := by ring
    obtain ⟨ex1, ex2, ex3, ex4⟩ := cx0 (by simpa using hbx)
    obtain ⟨ey1, ey2, ey3, ey4⟩ := cy0 (by simpa using hby)
    have px : x % 2 = 0 := by rw [← land_one x h0]; simpa using hbx
    have py : y % 2 = 0 := by rw [← land_one y h1]; simpa using hby
    refine ⟨⟨e1, e2, e3, e4, e5, t + 1, ex1, ey1, ex3, ey3, by omega, by omega, ?_, by omega⟩, by omega⟩
    rw [ex2, ey2]; exact hU
  case vc28.step.isFalse.isTrue.isTrue =>
    rename_i hcl hcr hih hinv
    obtain ⟨e1, e2, e3, e4, e5, hi1, hi2, hV, hZ, hT, hB, hLf, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hiH : i'.toNat ≤ st.h_node.toNat := by omega
    have hi1' : 1 ≤ i'.toNat := by omega
    have sl : shr (l + st.n_node) i' = (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) :=
      shr_nat _ _ (by omega)
    have sr : shr (r + st.n_node - 1) i' = ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) := by
      rw [shr_nat _ _ (by omega), show (r + st.n_node - 1).toNat = (r + st.n_node).toNat - 1 by omega]
    have bl := lvl_bounds' _ _ (l + st.n_node).toNat i'.toNat hN hNL (by omega) hiH
    have br := lvl_bounds' _ _ ((r + st.n_node).toNat - 1) i'.toNat hN (by omega) (by omega) hiH
    have hH1 : 2 ^ (st.h_node.toNat + 1 - i'.toNat) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have kl : ((l + st.n_node).toNat / 2 ^ i'.toNat) < nd3.size := by omega
    have kr : (((r + st.n_node).toNat - 1) / 2 ^ i'.toNat) < nd3.size := by omega
    have LL := level_left A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV hT hB
    have hcost : i'.toNat * (3 + 2 * cOp) = (i'.toNat - 1) * (3 + 2 * cOp) + (3 + 2 * cOp) := by
      rw [show i'.toNat = (i'.toNat - 1) + 1 by omega, Nat.add_one_mul]; simp
    have hHi : st.h_node.toNat - i'.toNat = st.h_node.toNat + 1 - (i' + 1).toNat := by omega
    have cL : (l + st.n_node).toNat % 2 ^ i'.toNat ≠ 0 := (cond_iff _ _ (by omega)).mp hcl
    have cR : (r + st.n_node).toNat % 2 ^ i'.toNat ≠ 0 := (cond_iff _ _ (by omega)).mp hcr
    obtain ⟨T1, V1, L1⟩ := LL.1 cL
    simp only [sl, sr] at *
    obtain ⟨u1, z1⟩ := upd_arr A nd3 (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) (by positivity)
      (by rw [Int.toNat_natCast]; exact kl)
    simp only [Int.toNat_natCast] at u1
    generalize Cpp.set nd3 _ _ = nd4 at *
    rw [← u1] at T1 V1 L1
    have LR := level_right A (fun i => nd4[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH V1 T1 hB
    obtain ⟨T2, V2, L2⟩ := LR.1 cR
    obtain ⟨u2, z2⟩ := upd_arr A nd4 ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) (by positivity)
      (by rw [z1, Int.toNat_natCast]; exact kr)
    simp only [Int.toNat_natCast] at u2
    generalize Cpp.set nd4 _ _ = nd5 at *
    rw [← u2] at T2 V2 L2
    refine ⟨⟨e1, e2, e3, e4, e5, by omega, by omega, V2, hZ, by rw [← hHi]; exact T2, hB,
      fun p hp1 hp2 => ?_, ?_⟩, by omega⟩
    · rw [L2 p (by omega), L1 p (by omega)]; exact hLf p hp1 hp2
    · rw [show (i' + 1).toNat - 1 = i'.toNat by omega]; omega
  case vc29.step.isFalse.isTrue.isFalse =>
    rename_i hcl hcr hih hinv
    obtain ⟨e1, e2, e3, e4, e5, hi1, hi2, hV, hZ, hT, hB, hLf, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hiH : i'.toNat ≤ st.h_node.toNat := by omega
    have hi1' : 1 ≤ i'.toNat := by omega
    have sl : shr (l + st.n_node) i' = (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) :=
      shr_nat _ _ (by omega)
    have sr : shr (r + st.n_node - 1) i' = ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) := by
      rw [shr_nat _ _ (by omega), show (r + st.n_node - 1).toNat = (r + st.n_node).toNat - 1 by omega]
    have bl := lvl_bounds' _ _ (l + st.n_node).toNat i'.toNat hN hNL (by omega) hiH
    have br := lvl_bounds' _ _ ((r + st.n_node).toNat - 1) i'.toNat hN (by omega) (by omega) hiH
    have hH1 : 2 ^ (st.h_node.toNat + 1 - i'.toNat) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have kl : ((l + st.n_node).toNat / 2 ^ i'.toNat) < nd3.size := by omega
    have kr : (((r + st.n_node).toNat - 1) / 2 ^ i'.toNat) < nd3.size := by omega
    have LL := level_left A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV hT hB
    have hcost : i'.toNat * (3 + 2 * cOp) = (i'.toNat - 1) * (3 + 2 * cOp) + (3 + 2 * cOp) := by
      rw [show i'.toNat = (i'.toNat - 1) + 1 by omega, Nat.add_one_mul]; simp
    have hHi : st.h_node.toNat - i'.toNat = st.h_node.toNat + 1 - (i' + 1).toNat := by omega
    have cL : (l + st.n_node).toNat % 2 ^ i'.toNat ≠ 0 := (cond_iff _ _ (by omega)).mp hcl
    have cR : (r + st.n_node).toNat % 2 ^ i'.toNat = 0 := (cond_eq_iff _ _ (by omega)).mp hcr
    obtain ⟨T1, V1, L1⟩ := LL.1 cL
    simp only [sl, sr] at *
    obtain ⟨u1, z1⟩ := upd_arr A nd3 (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) (by positivity)
      (by rw [Int.toNat_natCast]; exact kl)
    simp only [Int.toNat_natCast] at u1
    generalize Cpp.set nd3 _ _ = nd4 at *
    rw [← u1] at T1 V1 L1
    have LR := level_right A (fun i => nd4[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH V1 T1 hB
    have T2 := LR.2 cR
    refine ⟨⟨e1, e2, e3, e4, e5, by omega, by omega, V1, hZ, by rw [← hHi]; exact T2, hB,
      fun p hp1 hp2 => ?_, ?_⟩, by omega⟩
    · rw [L1 p (by omega)]; exact hLf p hp1 hp2
    · rw [show (i' + 1).toNat - 1 = i'.toNat by omega]; omega
  case vc30.step.isFalse.isFalse.isTrue =>
    rename_i hcl hcr hih hinv
    obtain ⟨e1, e2, e3, e4, e5, hi1, hi2, hV, hZ, hT, hB, hLf, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hiH : i'.toNat ≤ st.h_node.toNat := by omega
    have hi1' : 1 ≤ i'.toNat := by omega
    have sl : shr (l + st.n_node) i' = (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) :=
      shr_nat _ _ (by omega)
    have sr : shr (r + st.n_node - 1) i' = ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) := by
      rw [shr_nat _ _ (by omega), show (r + st.n_node - 1).toNat = (r + st.n_node).toNat - 1 by omega]
    have bl := lvl_bounds' _ _ (l + st.n_node).toNat i'.toNat hN hNL (by omega) hiH
    have br := lvl_bounds' _ _ ((r + st.n_node).toNat - 1) i'.toNat hN (by omega) (by omega) hiH
    have hH1 : 2 ^ (st.h_node.toNat + 1 - i'.toNat) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have kl : ((l + st.n_node).toNat / 2 ^ i'.toNat) < nd3.size := by omega
    have kr : (((r + st.n_node).toNat - 1) / 2 ^ i'.toNat) < nd3.size := by omega
    have LL := level_left A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV hT hB
    have hcost : i'.toNat * (3 + 2 * cOp) = (i'.toNat - 1) * (3 + 2 * cOp) + (3 + 2 * cOp) := by
      rw [show i'.toNat = (i'.toNat - 1) + 1 by omega, Nat.add_one_mul]; simp
    have hHi : st.h_node.toNat - i'.toNat = st.h_node.toNat + 1 - (i' + 1).toNat := by omega
    have cL : (l + st.n_node).toNat % 2 ^ i'.toNat = 0 := (cond_eq_iff _ _ (by omega)).mp hcl
    have cR : (r + st.n_node).toNat % 2 ^ i'.toNat ≠ 0 := (cond_iff _ _ (by omega)).mp hcr
    have T1 := LL.2 cL
    have LR := level_right A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV T1 hB
    obtain ⟨T2, V2, L2⟩ := LR.1 cR
    simp only [sl, sr] at *
    obtain ⟨u2, z2⟩ := upd_arr A nd3 ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) (by positivity)
      (by rw [Int.toNat_natCast]; exact kr)
    simp only [Int.toNat_natCast] at u2
    generalize Cpp.set nd3 _ _ = nd5 at *
    rw [← u2] at T2 V2 L2
    refine ⟨⟨e1, e2, e3, e4, e5, by omega, by omega, V2, hZ, by rw [← hHi]; exact T2, hB,
      fun p hp1 hp2 => ?_, ?_⟩, by omega⟩
    · rw [L2 p (by omega)]; exact hLf p hp1 hp2
    · rw [show (i' + 1).toNat - 1 = i'.toNat by omega]; omega
  case vc31.step.isFalse.isFalse.isFalse =>
    rename_i hcl hcr hih hinv
    obtain ⟨e1, e2, e3, e4, e5, hi1, hi2, hV, hZ, hT, hB, hLf, hc⟩ := hinv
    have hlt : l < r := by omega
    obtain ⟨hN, hh1, hle⟩ := hshape hlt
    have hNL : st.n_node.toNat ≤ (l + st.n_node).toNat := by clear * - hl hnn; omega
    have hLR : (l + st.n_node).toNat < (r + st.n_node).toNat := by clear * - hlt hl hnn; omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by clear * - hlt hr hle hl hnn; omega
    have hiH : i'.toNat ≤ st.h_node.toNat := by omega
    have hi1' : 1 ≤ i'.toNat := by omega
    have sl : shr (l + st.n_node) i' = (((l + st.n_node).toNat / 2 ^ i'.toNat : Nat) : Int) :=
      shr_nat _ _ (by omega)
    have sr : shr (r + st.n_node - 1) i' = ((((r + st.n_node).toNat - 1) / 2 ^ i'.toNat : Nat) : Int) := by
      rw [shr_nat _ _ (by omega), show (r + st.n_node - 1).toNat = (r + st.n_node).toNat - 1 by omega]
    have bl := lvl_bounds' _ _ (l + st.n_node).toNat i'.toNat hN hNL (by omega) hiH
    have br := lvl_bounds' _ _ ((r + st.n_node).toNat - 1) i'.toNat hN (by omega) (by omega) hiH
    have hH1 : 2 ^ (st.h_node.toNat + 1 - i'.toNat) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have kl : ((l + st.n_node).toNat / 2 ^ i'.toNat) < nd3.size := by omega
    have kr : (((r + st.n_node).toNat - 1) / 2 ^ i'.toNat) < nd3.size := by omega
    have LL := level_left A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV hT hB
    have hcost : i'.toNat * (3 + 2 * cOp) = (i'.toNat - 1) * (3 + 2 * cOp) + (3 + 2 * cOp) := by
      rw [show i'.toNat = (i'.toNat - 1) + 1 by omega, Nat.add_one_mul]; simp
    have hHi : st.h_node.toNat - i'.toNat = st.h_node.toNat + 1 - (i' + 1).toNat := by omega
    have cL : (l + st.n_node).toNat % 2 ^ i'.toNat = 0 := (cond_eq_iff _ _ (by omega)).mp hcl
    have cR : (r + st.n_node).toNat % 2 ^ i'.toNat = 0 := (cond_eq_iff _ _ (by omega)).mp hcr
    have T1 := LL.2 cL
    have LR := level_right A (fun i => nd3[i]!) (fun i => lz3[i]!) _ _ _ _ i'.toNat hN hNL hLR hR2 hi1' hiH hV T1 hB
    have T2 := LR.2 cR
    refine ⟨⟨e1, e2, e3, e4, e5, by omega, by omega, hV, hZ, by rw [← hHi]; exact T2, hB, hLf, ?_⟩, by omega⟩
    rw [show (i' + 1).toNat - 1 = i'.toNat by omega]; omega
  case vc32.isTrue.isFalse.post.success.post.success.pre =>
    obtain ⟨e1, e2, e3, e4, e5, hU, hc⟩ := ‹n2 = st.n ∧ _›
    obtain ⟨hV, hZ, hT, hB, hLf⟩ := hU
    have hlt : l < r := by omega
    refine ⟨⟨e1, e2, e3, e4, e5, by omega, hV, hZ, hT, hB, fun p hp1 hp2 => ?_, by omega⟩, ?_⟩
    · rw [hLf p (by omega) hp2]
      by_cases c : l + st.n_node ≤ (p : Int) ∧ (p : Int) < r + st.n_node
      · rw [if_pos (by omega), if_pos c]
      · rw [if_neg (by omega), if_neg c]
    · rw [e3]; exact lt_trans (show st.h_node.toNat < 2 ^ 30 by omega) (by unfold fuel; norm_num)
  case vc27.step.isTrue =>
    rename_i hih hinv
    obtain ⟨e1, e2, e3, e4, e5, hi1, hi2, hV, hZ, hT, hB, hLf, hc⟩ := hinv
    have hlt : l < r := by omega
    have hiv : i'.toNat = st.h_node.toNat + 1 := by omega
    rw [hiv, Nat.sub_self] at hT
    rw [hiv, Nat.add_sub_cancel] at hc
    rw [mapIdx_cond A v l r f hl]
    refine ⟨urange_valid A st ⟨n3, nn3, hh3, nd3, lz3⟩ v hv l.toNat r.toNat f (by omega) e1 e2 e3 e4 e5 hV hZ
      (rtinv_mono A _ _ _ _ _ hT (fun j ⟨s, h1, h2, _⟩ => by omega)) (fun p hp1 hp2 => ?_), by omega⟩
    show virt A (fun i => nd3[i]!) (fun i => lz3[i]!) p = _
    rw [hLf p (by omega) hp2]
    by_cases c : st.n_node.toNat + l.toNat ≤ p ∧ p < st.n_node.toNat + r.toNat
    · rw [if_pos (by omega), if_pos c]
    · rw [if_neg (by omega), if_neg c]
  case vc33.isTrue.isFalse.post.success.post.success.post.success => exact ‹LValid _ _ _ ∧ _›
  case vc1.isTrue.isTrue =>
    have e : r = l := by omega
    subst e
    rw [mapIdx_empty A v r f]
    exact ⟨hv, by omega⟩
  case vc35.isFalse => omega

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

theorem one_level {h cur : Int} {pref suff : List Int} (Hr : rangeDown 1 h = pref ++ cur :: suff) (x : Int)
    (hx0 : 0 ≤ x) : ∃ m, pref.length = m ∧ m < h.toNat ∧
      shr x cur = ((x.toNat / 2 ^ (h.toNat - m) : Nat) : Int) := by
  obtain ⟨e, c1, c2, cl⟩ := level_cursor Hr
  have hc : cur.toNat = h.toNat - pref.length := by omega
  exact ⟨pref.length, rfl, cl, by rw [shr_nat x cur hx0, hc]⟩

/-- The ancestors of the leaf `S` at the levels above `H - m`. -/
def AncS (S H m j : Nat) : Prop := ∃ s, H - m < s ∧ s ≤ H ∧ j = S / 2 ^ s

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem ancs_lt (N H S m j : Nat) (hN : N = 2 ^ H) (hS1 : N ≤ S) (hS2 : S < 2 * N) (hj : AncS S H m j) :
    j < 2 ^ (m + 1) := by
  obtain ⟨s, h1, h2, rfl⟩ := hj
  have := (lvl_bounds' N H S s hN hS1 hS2 h2).2
  have : 2 ^ (H + 1 - s) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem ancs_succ (S H m j : Nat) (hm : m < H) (h : AncS S H m j ∨ j = S / 2 ^ (H - m)) : AncS S H (m + 1) j := by
  rcases h with ⟨s, h1, h2, rfl⟩ | rfl
  · exact ⟨s, by omega, h2, rfl⟩
  · exact ⟨H - m, by omega, by omega, rfl⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- A node whose strict ancestors carry trivial tags reads as the pushed-down tree of the start state. -/
theorem read_of_anc (A : Act M F) (st0 st : cp.LazySegmentTree M F) (Q : Nat → Prop) (hI : PInvS A st0 Q st)
    (c : Nat) (hc : c < 2 * st0.n_node.toNat) (hQ : ∀ j, 1 ≤ j → SAnc j c → Q j) :
    st.node[c]! = virt A (nodeF st0) (lazyF st0) c := by
  obtain ⟨g1, g2, g3, g4, g5, gS, gV, gP⟩ := hI
  rw [← gV c hc]
  simp only [virt]
  rw [P_of_idTag A _ c _ (gS.1 c hc) (fun j hj hs => gP j (hQ j hj hs))]
  rfl

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- The climbing cursor `x = ⌈S / 2^t⌉` of a search, when odd, has its strict ancestors among those of `S`. -/
theorem climb_anc (N H S t x : Nat) (hN : N = 2 ^ H) (hS1 : N ≤ S) (hx : x = (S + 2 ^ t - 1) / 2 ^ t)
    (hodd : x % 2 = 1) (hx2 : x * 2 ^ t < 2 * N) : ∀ j, 1 ≤ j → SAnc j x → AncS S H H j := by
  intro j hj ⟨u, hu, e⟩
  obtain ⟨r1, -⟩ := read_left S t x u hx hodd hu
  have hxN : x < 2 * N := by have : x ≤ x * 2 ^ t := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t); omega
  have hle := anc_level N H j x u hN hxN hj e.symm t hx2
  exact ⟨t + u, by omega, hle, by rw [← e, r1]⟩

/-- The climbing cursor: `⌈S / 2^t⌉`, or one past it after passing an odd node. -/
def Good (S t x : Nat) : Prop :=
  x = (S + 2 ^ t - 1) / 2 ^ t ∨ (x = (S + 2 ^ t - 1) / 2 ^ t + 1 ∧ ((S + 2 ^ t - 1) / 2 ^ t) % 2 = 1)

theorem good_init (S : Nat) : Good S 0 S := Or.inl (by simp)

theorem good_climb (S t x : Nat) (hG : Good S t x) (he : x % 2 = 0) : Good S (t + 1) (x / 2) := by
  left
  have cl := cursor_left S t ((S + 2 ^ t - 1) / 2 ^ t) rfl
  unfold pl1 at cl
  rcases hG with rfl | ⟨rfl, ho⟩
  · rw [if_neg (by omega)] at cl; exact cl
  · rw [if_pos ho] at cl; exact cl

theorem good_climb_int (S t : Nat) (x : Int) (hx : 0 ≤ x) (hev : Cpp.mod x 2 = 0) (hG : Good S t x.toNat) :
    Good S (t + 1) (shr x 1).toNat := by
  have he := SegmentTree.even_of_mod _ hx hev
  rw [shr_one, show (x / 2).toNat = x.toNat / 2 by omega]
  exact good_climb S t _ hG he

theorem good_odd (S t x : Nat) (hG : Good S t x) (ho : x % 2 = 1) : x = (S + 2 ^ t - 1) / 2 ^ t := by
  rcases hG with h | ⟨h1, h2⟩
  · exact h
  · omega

theorem good_pass (S t x : Nat) (hG : Good S t x) (ho : x % 2 = 1) : Good S t (x + 1) := by
  have := good_odd S t x hG ho
  exact Or.inr ⟨by omega, by omega⟩

theorem desc_push (A : Act M F) (st0 st r : cp.LazySegmentTree M F) (ld : Nat)
    (hI : PInvS A st0 (fun j => 1 ≤ j ∧ SAnc j ld) st) (hk1 : 1 ≤ ld) (hkN : ld < st0.n_node.toNat)
    (hn : (fun i => r.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) ld)
    (hz : (fun i => r.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat ld)
    (h1 : r.node.size = st.node.size) (h2 : r.lazy.size = st.lazy.size) (h3 : r.n = st.n)
    (h4 : r.n_node = st.n_node) (h5 : r.h_node = st.h_node) :
    PInvS A st0 (fun j => 1 ≤ j ∧ SAnc j (2 * ld)) ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ ∧
      PInvS A st0 (fun j => 1 ≤ j ∧ SAnc j (2 * ld + 1)) ⟨r.n, r.n_node, r.h_node, r.node, r.lazy⟩ ∧
      r.node[2 * ld]! = virt A (nodeF st0) (lazyF st0) (2 * ld) ∧
      r.node[2 * ld + 1]! = virt A (nodeF st0) (lazyF st0) (2 * ld + 1) := by
  have P := pinvs_push A st0 st r _ ld hI hk1 hkN (fun j ⟨hj, hs⟩ => by
    have := sanc_le j ld hs (by omega); omega) hn hz h1 h2 h3 h4 h5
  have m0 : ∀ c, c / 2 = ld → 2 ≤ c → ∀ j, 1 ≤ j ∧ SAnc j c → (1 ≤ j ∧ SAnc j ld) ∨ j = ld := by
    intro c hc hc2 j ⟨hj, hs⟩
    rcases (sanc_step j c hc2).mp hs with e | e
    · right; omega
    · left; exact ⟨hj, by rwa [hc] at e⟩
  refine ⟨pinvs_mono A st0 _ _ _ P (m0 (2 * ld) (by omega) (by omega)),
    pinvs_mono A st0 _ _ _ P (m0 (2 * ld + 1) (by omega) (by omega)), ?_⟩
  exact ⟨read_of_anc A st0 _ _ P (2 * ld) (by omega) (fun j hj hs => m0 (2 * ld) (by omega) (by omega) j ⟨hj, hs⟩),
    read_of_anc A st0 _ _ P (2 * ld + 1) (by omega)
      (fun j hj hs => m0 (2 * ld + 1) (by omega) (by omega) j ⟨hj, hs⟩)⟩

/-- The node where the climb fails starts the descent: its ancestors carry trivial tags. -/
theorem desc_init (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p : M → Bool) (H S t : Nat) (x : Int) (sm : M)
    (hx0 : 0 ≤ x) (hodd : x.toNat % 2 = 1)
    (hR : RInv A.m (virt A (nodeF st) (lazyF st)) st.n_node.toNat p S x.toNat sm t) (hG : Good S t x.toNat)
    (hI : PInvS A st (AncS S H H) st1) (hN : st.n_node.toNat = 2 ^ H) (hS1 : st.n_node.toNat ≤ S)
    (hf : p (A.m.op sm (Cpp.get st1.node x)) = false) :
    PInvS A st (fun j => 1 ≤ j ∧ SAnc j x.toNat) st1 ∧
      DInv A.m (virt A (nodeF st) (lazyF st)) st.n_node.toNat p S x.toNat sm t ∧
      x.toNat < 2 * st.n_node.toNat := by
  have hxc := good_odd S t x.toNat hG hodd
  have hx2 : x.toNat * 2 ^ t < 2 * st.n_node.toNat := by
    have := hR.2.2.1; have : 0 < 2 ^ t := Nat.two_pow_pos t; nlinarith
  have hanc := climb_anc _ H S t x.toNat hN hS1 hxc hodd hx2
  have hxN : x.toNat < 2 * st.n_node.toNat := by
    have : x.toNat ≤ x.toNat * 2 ^ t := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t); omega
  have rd := read_of_anc A st st1 _ hI x.toNat hxN hanc
  refine ⟨pinvs_mono A st _ _ _ hI (fun j ⟨h1, h2⟩ => hanc j h1 h2), ⟨hR, ?_⟩, hxN⟩
  rw [get_eq, rd] at hf; exact hf

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem climb_read (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p : M → Bool) (H S t : Nat) (x : Int) (sm : M)
    (hodd : x.toNat % 2 = 1)
    (hR : RInv A.m (virt A (nodeF st) (lazyF st)) st.n_node.toNat p S x.toNat sm t) (hG : Good S t x.toNat)
    (hI : PInvS A st (AncS S H H) st1) (hN : st.n_node.toNat = 2 ^ H) (hS1 : st.n_node.toNat ≤ S) :
    Cpp.get st1.node x = virt A (nodeF st) (lazyF st) x.toNat := by
  have hxc := good_odd S t x.toNat hG hodd
  have hx2 : x.toNat * 2 ^ t < 2 * st.n_node.toNat := by
    have := hR.2.2.1; have : 0 < 2 ^ t := Nat.two_pow_pos t; nlinarith
  have hanc := climb_anc _ H S t x.toNat hN hS1 hxc hodd hx2
  have hxN : x.toNat < 2 * st.n_node.toNat := by
    have : x.toNat ≤ x.toNat * 2 ^ t := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t); omega
  rw [get_eq]; exact read_of_anc A st st1 _ hI x.toNat hxN hanc

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem pad_contra_v (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (p : M → Bool)
    (S x : Nat) (hS : st.n_node.toNat ≤ S) (hSx : S ≤ x) (hx2 : x < 2 * st.n_node.toNat)
    (h1 : p (rf A.m (virt A (nodeF st) (lazyF st)) S (x - S)) = true)
    (h2 : p (rf A.m (virt A (nodeF st) (lazyF st)) S (x + 1 - S)) = false) : x < st.n_node.toNat + v.length := by
  have hst := hv.state
  have hVV := virt_V A _ _ _ hst.1 hst.2.1
  by_contra hc
  have hpad := hv.pad (x - st.n_node.toNat) (by omega) (by omega)
  rw [show st.n_node.toNat + (x - st.n_node.toNat) = x by omega] at hpad
  have e : x + 1 - S = (x - S) + 1 := by omega
  rw [e, rf_add A.m _ _ hVV _ _ _ (by omega), show S + (x - S) = x by omega, rf_one A.m _ _ (by
    rw [hpad]; exact A.m.he)] at h2
  rw [hpad, A.m.rid _ (rf_V A.m _ _ hVV _ _ (by omega))] at h2
  rw [h1] at h2; exact absurd h2 (by decide)

set_option maxHeartbeats 1000000 in
theorem lsearch_right_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA) {G : Type}
    [Cpp.Invoke1 G M Bool] (p : M → Bool) (cF : Nat) (g : G)
    (hF : ∀ x, ∀ {Q : PostCond Bool PS}, ⦃fun t => Q.1 (p x) (t + cF)⦄
      (Cpp.Invoke1.call (A := M) (R := Bool) g x) ⦃Q⦄)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29)
    (l : Int) (h0 : 0 ≤ l) (hl : l ≤ v.length) (hpe : p A.m.e = true) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.search_prod_right st l g
    ⦃⇓ r c => ⌜l ≤ r.1 ∧ r.1 ≤ v.length ∧ p (rf A.m (fun i => v[i]!) l.toNat (r.1 - l).toNat) = true ∧
      (r.1 = v.length ∨ p (rf A.m (fun i => v[i]!) l.toNat (r.1 + 1 - l).toNat) = false) ∧ LValid A r.2 v ∧
      c ≤ t0 + 4 + 2 * cE + 2 * cF + cOp + (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) +
        st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  set a : Nat → M := virt A (nodeF st) (lazyF st) with ha
  set N := st.n_node.toNat with hNdef
  set h := st.h_node.toNat with hhdef
  set S := (l + st.n_node).toNat with hSdef
  set PC := 3 + 2 * cA + 2 * cC + cI with hPC
  set B := t0 + 1 + 2 * cE + cF + h * (1 + PC) with hB
  set D := 2 + 2 * cOp + cF with hD
  set E := 1 + 2 * cOp + cF + PC with hEc
  have hshape : N = 2 ^ h ∧ 1 ≤ st.h_node ∧ v.length ≤ N ∨ v = [] := by
    rcases hv.shape with ⟨h1, -⟩ | ⟨h1, h2, h3, -⟩
    · exact Or.inr h1
    · exact Or.inl ⟨h1, h2, h3⟩
  mvcgen [cp.LazySegmentTree.search_prod_right, hE, hOp, hF, hP]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', nd', lz'⟩ c =>
      ⌜PInvS A st (AncS S h xs.prefix.length) ⟨n', nn', hh', nd', lz'⟩ ∧
        c ≤ t0 + 1 + cE + cF + xs.prefix.length * (1 + PC)⌝
  case vc8.inv =>
    exact ⟨fun ⟨ret, n'', nn'', hh'', nd'', lz'', l', sm⟩ c => ⌜ret = none ∧
              PInvS A st (AncS S h h) ⟨n'', nn'', hh'', nd'', lz''⟩ ∧ 0 ≤ l' ∧
              ∃ t k, RInv A.m a N p S l'.toNat sm t ∧ Good S t l'.toNat ∧
                k ≤ t + (if l'.toNat % 2 = 0 then 1 else 0) ∧ c ≤ B + D * k + t⌝,
           fun ⟨ret, n'', nn'', hh'', nd'', lz'', _, _⟩ c => ⌜match ret with
              | some r => ∃ x : Nat, r.1 = (x : Int) - st.n_node ∧ (∃ Q, PInvS A st Q r.2) ∧ S ≤ x ∧ x < 2 * N ∧
                  p (rf A.m a S (x - S)) = true ∧ p (rf A.m a S (x + 1 - S)) = false ∧
                  c ≤ B + D * h + h + 3 + cOp + cF + h * E
              | none => p (rf A.m a S (2 * N - S)) = true ∧ PInvS A st (AncS S h h) ⟨n'', nn'', hh'', nd'', lz''⟩ ∧
                  c ≤ B + D * (h + 1) + h⌝,
           fun ⟨_, _, _, _, _, _, l', _⟩ => 2 * N - l'.toNat * 2 ^ (h - Nat.log2 l'.toNat)⟩
  case vc9.inv =>
    rename_i b _ _ _ _ _ _ _ _ _ _ _ lb smb _ _
    exact ⟨fun l'' c => ⌜0 ≤ l'' ∧ l'' ≤ lb ∧ ∃ t k, RInv A.m a N p S l''.toNat smb t ∧ Good S t l''.toNat ∧
              l''.toNat * 2 ^ t = lb.toNat * 2 ^ (h - Nat.log2 lb.toNat) ∧
              (if l'' = lb then k ≤ t + (if lb.toNat % 2 = 0 then 1 else 0) else k ≤ t) ∧
              c ≤ B + D * k + t + 1⌝,
           fun l'' c => ⌜0 ≤ l'' ∧ l''.toNat % 2 = 1 ∧ ∃ t k, RInv A.m a N p S l''.toNat smb t ∧
              Good S t l''.toNat ∧ l''.toNat * 2 ^ t = lb.toNat * 2 ^ (h - Nat.log2 lb.toNat) ∧ k ≤ t ∧
              c ≤ B + D * k + t + 2⌝,
           fun l'' => l''.toNat⟩
  case vc13.inv =>
    exact ⟨fun ⟨n3, nn3, hh3, nd3, lz3, ld, smd⟩ c => ⌜0 ≤ ld ∧
              PInvS A st (fun j => 1 ≤ j ∧ SAnc j ld.toNat) ⟨n3, nn3, hh3, nd3, lz3⟩ ∧
              ∃ t, DInv A.m a N p S ld.toNat smd t ∧ t ≤ h ∧
              c + t * E ≤ B + D * h + h + 2 + cOp + cF + h * E⌝,
           fun ⟨n3, nn3, hh3, nd3, lz3, ld, smd⟩ c => ⌜0 ≤ ld ∧
              PInvS A st (fun j => 1 ≤ j ∧ SAnc j ld.toNat) ⟨n3, nn3, hh3, nd3, lz3⟩ ∧ N ≤ ld.toNat ∧
              DInv A.m a N p S ld.toNat smd 0 ∧ c ≤ B + D * h + h + 3 + cOp + cF + h * E⌝,
           fun ⟨_, _, _, _, _, ld, _⟩ => 2 * N - ld.toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2.2 = smo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2.1 = lo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.1 = lzo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.1 = ndo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.1 = hho at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.1 = nno at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.1 = no at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2 = smd at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.1 = ld at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.1 = lz3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.1 = nd3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.1 = hh3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.1 = nn3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).1 = n3 at *)
  case vc1.isTrue.isTrue.isTrue =>
    subst ‹l = st.n›
    refine ⟨le_refl _, by omega, by simp [rf]; exact hpe, Or.inl (by omega), hv, ?_⟩
    generalize (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) = X
    omega
  case vc30.isFalse => omega
  case vc7.isTrue.isTrue.isFalse.pre =>
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun _ _ => rfl, fun j ⟨s, h1, h2, _⟩ => by omega⟩, by omega⟩
  case vc2.a | vc3.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, hh1, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node) _ hN (by omega) (by omega) (by omega)
    simp at g2; omega
  case vc4.a | vc5.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc6.step.post.success =>
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    rcases hshape with ⟨hN, hh1, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    obtain ⟨m, hm1, hm, e1⟩ := one_level ‹rangeDown _ _ = _ ++ _ :: _› (l + st.n_node) (by omega)
    simp only [hm1] at *
    simp only [e1, Int.toNat_natCast] at *
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ (l + st.n_node).toNat hN (by omega) (by omega) hm
      hI (fun j hj => ancs_lt _ _ _ _ j hN (by omega) (by omega) hj) a1 a2 a3 a4 a5 a6 a7
    refine ⟨pinvs_mono A st _ _ _ P1 (fun j hj => ?_), ?_⟩
    · obtain ⟨s', h1, h2, rfl⟩ := hj
      by_cases e : s' = st.h_node.toNat - m
      · right; rw [e]
      · left; exact ⟨s', by omega, h2, rfl⟩
    · have : (m + 1) * (1 + (3 + 2 * cA + 2 * cC + cI)) = m * (1 + (3 + 2 * cA + 2 * cC + cI)) +
          (1 + (3 + 2 * cA + 2 * cC + cI)) := by ring
      omega
  case vc25.isTrue.isTrue.isFalse.post.success.pre =>
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    have hlen : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hlen] at hI hc
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hS1 : st.n_node.toNat ≤ (l + st.n_node).toNat := by omega
    have hS2 : (l + st.n_node).toNat < 2 * st.n_node.toNat := by omega
    have hR := rinv_init A.m (virt A (nodeF st) (lazyF st)) _ p _ hS1 hS2 hpe
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨⟨hI, by omega, 0, hR, good_init _, 0, by simp, by omega⟩, ?_⟩
    simp [fuel]; omega
  case vc10.step.isTrue =>
    obtain ⟨hx0, hxle, t, hR, hG, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    have hodd := SegmentTree.odd_of_not_mod _ hx0 ‹_›
    refine ⟨hx0, hodd, t, hR, hG, hL, k, ?_, by omega⟩
    split at hk
    · rename_i heq; simp only [← heq] at hk; simp [hodd] at hk; exact hk
    · exact hk
  case vc11.step.isFalse =>
    obtain ⟨hx0, hxle, t, hR, hG, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    obtain ⟨c0, c1, c2, c3⟩ := SegmentTree.climb_int A.m _ _ _ hN p _ _ _ _ hx0 ‹_› hR
    have hev := SegmentTree.even_of_mod _ hx0 ‹_›
    have hG' := good_climb_int _ _ _ hx0 ‹_› hG
    refine ⟨⟨c0, by omega, t + 1, c2, hG', by rw [c3, hL], k, ?_, by omega⟩, c1, by omega⟩
    rw [if_neg (by omega)]
    split at hk
    · rename_i heq; simp only [← heq] at hk
      simp [hev] at hk; omega
    · omega
  case vc12.step.pre =>
    obtain ⟨-, -, hl0, t, hR, hG, k, hk, hc⟩ := ‹_ = none ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hb := SegmentTree.rinv_bound A.m _ _ p _ _ _ _ hR
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨⟨hl0, t, hR, hG, by rw [← SegmentTree.rinv_height A.m _ _ _ hN p _ _ _ _ hR]; simp, k,
      by simpa using hk, by omega⟩, ?_⟩
    have hN30 : st.n_node.toNat ≤ 2 ^ 30 := by rw [hN]; exact h30
    exact lt_of_lt_of_le hb (by unfold fuel; omega)
  case vc14.step.isTrue =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    have e2 := hI.2.1
    simp only at e2
    have ht0 := dinv_exit A.m _ _ p _ _ _ _ hD (by omega)
    subst ht0
    exact ⟨hd0, hI, Or.inl (by omega), hD, by omega⟩
  case vc15.a | vc16.a | vc17.a | vc18.a =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨g1, g2, g3, g4, g5, -⟩ := hI
    have h1l := hD.1.1
    simp only at g2 g4 g5
    first | omega | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc19.step.isFalse.post.success.isTrue =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A _ _ _ ∧ _›
    have g2 := hI.2.1
    simp only at g2
    have h1l := hD.1.1
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hD.1.2.2.1; simp at hn; omega
    obtain ⟨P1, P2, rd, -⟩ := desc_push A st _ _ ld.toNat hI h1l (by omega) a1 (by rw [g2] at a2 ⊢; exact a2) a3 a4 a5 a6 a7
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨t', rfl, d1, d2⟩ := dinv_step A.m _ _ hVV hTr p _ ld.toNat smd _ hD (by omega)
    clear hTr hVV hst
    rw [get_eq, show (ld * 2).toNat = 2 * ld.toNat by omega] at *
    have hcost : (t' + 1) * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        t' * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) + (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := by
      ring
    refine ⟨⟨by omega, by rw [show (ld * 2 + 1).toNat = 2 * ld.toNat + 1 by omega]; exact P2, t', ?_, by omega,
      by omega⟩, by omega⟩
    rw [show (ld * 2 + 1).toNat = 2 * ld.toNat + 1 by omega, rd]
    exact d1 (by rw [← rd]; exact ‹p (A.m.op smd _) = true›)
  case vc20.step.isFalse.post.success.isFalse =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A _ _ _ ∧ _›
    have g2 := hI.2.1
    simp only at g2
    have h1l := hD.1.1
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hD.1.2.2.1; simp at hn; omega
    obtain ⟨P1, P2, rd, -⟩ := desc_push A st _ _ ld.toNat hI h1l (by omega) a1 (by rw [g2] at a2 ⊢; exact a2) a3 a4 a5 a6 a7
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨t', rfl, d1, d2⟩ := dinv_step A.m _ _ hVV hTr p _ ld.toNat smd _ hD (by omega)
    clear hTr hVV hst
    rw [get_eq, show (ld * 2).toNat = 2 * ld.toNat by omega] at *
    have hcost : (t' + 1) * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        t' * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) + (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := by
      ring
    refine ⟨⟨by omega, P1, t', ?_, by omega, by omega⟩, by omega⟩
    exact d2 (by rw [← rd]; first | exact ‹p (A.m.op smd _) = false› | simpa using ‹¬ p (A.m.op smd _) = true›)
  case vc21.step.post.success.isTrue.pre =>
    obtain ⟨hr0, hodd, t, hR, hG, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have ht := t_le _ _ _ _ hN hR.1 hR.2.2.1
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hN30 : st.n_node.toNat ≤ 2 ^ 30 := by rw [hN]; exact h30
    have hS1 : st.n_node.toNat ≤ (l + st.n_node).toNat := by omega
    obtain ⟨P, D, hxN⟩ := desc_init A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo hr0 hodd hR hG hI hN hS1
      ‹p (A.m.op smo _) = false›
    refine ⟨⟨hr0, P, t, D, ht, ?_⟩, by unfold fuel; omega⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have m2 : t * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) ≤
        st.h_node.toNat * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := Nat.mul_le_mul_right _ ht
    omega
  case vc22.step.post.success.isTrue.post.success =>
    obtain ⟨hd0, hI, -, hD, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ _ _ ∧ (_ ∨ _) ∧ DInv _ _ _ _ _ _ _ 0 ∧ _›
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    have hop := rinv_op A.m _ _ hVV hTr p _ _ _ _ hD.1
    clear hTr hVV hst
    have g2 := hI.2.1
    simp only at g2
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hD
    simp at h2 h3 h4 h6 hop
    refine ⟨ld.toNat, by omega, ⟨_, hI⟩, by omega, by omega, by rw [← h6]; exact h7, by rw [← hop]; exact h8, ?_⟩
    omega
  case vc23.step.post.success.isFalse.isTrue =>
    obtain ⟨hr0, hodd, t, hR, hG, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hS1 : st.n_node.toNat ≤ (l + st.n_node).toNat := by omega
    have rd := climb_read A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo hodd hR hG hI hN hS1
    have hpow := (SegmentTree.pow_cond _ hr0).mp ‹_›
    have ht := t_le _ _ _ _ hN hR.1 hR.2.2.1
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    have hf := ‹p (A.m.op smo _) = true›
    rw [rd] at hf
    obtain ⟨-, hend⟩ := rinv_end A.m _ _ _ hN hVV hTr p _ _ _ _ hR hf hpow
    clear hTr hVV hst
    refine ⟨hend, hI, ?_⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have : (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) = (2 + 2 * cOp + cF) * st.h_node.toNat + (2 + 2 * cOp + cF) := by
      ring
    omega
  case vc24.step.post.success.isFalse.isFalse =>
    obtain ⟨hr0, hodd, t, hR, hG, hL, k, hk, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ _ % 2 = 1 ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hR.2.2.1; simp at hn; omega
    have hS1 : st.n_node.toNat ≤ (l + st.n_node).toNat := by omega
    have rd := climb_read A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo hodd hR hG hI hN hS1
    have hpow : ¬ ∃ k, _ = 2 ^ k := fun h => ‹¬ _› ((SegmentTree.pow_cond _ hr0).mpr h)
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    have hf := ‹p (A.m.op smo _) = true›
    rw [rd] at hf
    have hR' := rinv_next A.m _ _ _ hN hVV hTr p _ _ _ _ hR hf hpow
    clear hTr hVV hst
    have hG' := good_pass _ _ _ hG hodd
    rw [rd, SegmentTree.toNat_succ _ hr0]
    refine ⟨⟨hI, by omega, t, hR', hG', k + 1, by rw [if_pos (by omega)]; omega, ?_⟩, ?_⟩
    · have : (2 + 2 * cOp + cF) * (k + 1) = (2 + 2 * cOp + cF) * k + (2 + 2 * cOp + cF) := by ring
      omega
    · exact SegmentTree.measure_dec _ _ _ _ _ hR'.2.2.1 (SegmentTree.rinv_height A.m _ _ _ hN p _ _ _ _ hR') hL
  case vc26.isTrue.isTrue.isFalse.post.success.post.success.h_1 =>
    simp only [‹_ = some _›] at *
    obtain ⟨x, hx, ⟨Q, hQ⟩, hS, hx2, hp1, hp2, hc⟩ := ‹∃ x : Nat, _ = _ ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hlt := pad_contra_v A st v hv p _ x (by omega) (by omega) hx2 hp1 hp2
    have e1 : x - (l + st.n_node).toNat = ((x : Int) - st.n_node - l).toNat := by omega
    have e2 : x + 1 - (l + st.n_node).toNat = ((x : Int) - st.n_node + 1 - l).toNat := by omega
    have eS : (l + st.n_node).toNat = st.n_node.toNat + l.toNat := by omega
    rw [e1, eS, lrf_leaves A st v hv _ _ (by omega)] at hp1
    rw [e2, eS, lrf_leaves A st v hv _ _ (by omega)] at hp2
    rw [hx]
    refine ⟨by omega, by omega, by simpa using hp1, Or.inr (by simpa using hp2), pinvs_valid A st _ v hv _ hQ, ?_⟩
    have : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * st.h_node.toNat + st.h_node.toNat + st.h_node.toNat * (1 + 2 * cOp + cF) +
          (4 + 4 * cOp + 2 * cF) := by ring
    have : st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) = st.h_node.toNat * (1 + (3 + 2 * cA + 2 * cC + cI)) +
        st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    have : st.h_node.toNat * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        st.h_node.toNat * (1 + 2 * cOp + cF) + st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    omega
  case vc27.isTrue.isTrue.isFalse.post.success.post.success.h_2 =>
    simp only [‹_ = none›] at *
    obtain ⟨hp1, hI, hc⟩ := ‹p _ = true ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hpad := rf_pad A.m _ st.n_node.toNat v.length (l + st.n_node).toNat hVV hle (by omega) (by omega) hv.pad
    clear hVV hst
    rw [hpad, show st.n_node.toNat + v.length - (l + st.n_node).toNat = (st.n - l).toNat by omega,
      show (l + st.n_node).toNat = st.n_node.toNat + l.toNat by omega,
      lrf_leaves A st v hv _ _ (by omega)] at hp1
    have g1 := hI.1
    simp only at g1
    subst g1
    refine ⟨by omega, by omega, by simpa using hp1, Or.inl (by omega), pinvs_valid A st _ v hv _ hI, ?_⟩
    have e : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) + (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := by ring
    have : st.h_node.toNat + 1 ≤ (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) = st.h_node.toNat * (1 + (3 + 2 * cA + 2 * cC + cI)) +
        st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    omega


end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

/-- The cursor of the left search: `y = x + 1` is `⌊R / 2^t⌋`, or one below it after passing a node. -/
def GoodL (R t y : Nat) : Prop := y = R / 2 ^ t ∨ (y = R / 2 ^ t - 1 ∧ (R / 2 ^ t) % 2 = 1)

theorem goodl_init (R : Nat) : GoodL R 0 R := Or.inl (by simp)

theorem goodl_climb (R t x : Nat) (hG : GoodL R t (x + 1)) (ho : x % 2 = 1) : GoodL R (t + 1) (x / 2 + 1) := by
  left
  have cr := cursor_right R t (R / 2 ^ t) rfl
  unfold pr1 at cr
  rcases hG with h | ⟨h1, h2⟩
  · rw [if_neg (by omega)] at cr; omega
  · rw [if_pos h2] at cr; omega

theorem goodl_stop (R t x : Nat) (hG : GoodL R t (x + 1)) (he : x % 2 = 0) :
    x + 1 = R / 2 ^ t ∧ (x + 1) % 2 = 1 := by
  rcases hG with h | ⟨h1, h2⟩
  · exact ⟨h, by omega⟩
  · omega

theorem goodl_pass (R t x : Nat) (hG : GoodL R t (x + 1)) (he : x % 2 = 0) : GoodL R t x := by
  obtain ⟨h1, h2⟩ := goodl_stop R t x hG he
  exact Or.inr ⟨by omega, by omega⟩

theorem goodl_climb_int (R t : Nat) (x : Int) (h1 : 1 < x) (hodd : ¬ Cpp.mod x 2 = 0)
    (hG : GoodL R t (x.toNat + 1)) : GoodL R (t + 1) ((shr x 1).toNat + 1) := by
  have ho := SegmentTree.odd_of_not_mod _ (by omega) hodd
  rw [shr_one, show (x / 2).toNat = x.toNat / 2 by omega]
  exact goodl_climb R t _ hG ho

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- A node read by the left search has its strict ancestors among those of the leaf `R - 1`. -/
theorem climbl_anc (N H R t x : Nat) (hN : N = 2 ^ H) (hR1 : N < R) (hR2 : R ≤ 2 * N) (hx1 : 1 ≤ x)
    (hstop : ¬ (1 < x ∧ x % 2 = 1)) (hG : GoodL R t (x + 1)) (hxt : x * 2 ^ t < 2 * N) :
    ∀ j, 1 ≤ j → SAnc j x → AncS (R - 1) H H j := by
  intro j hj ⟨u, hu, e⟩
  by_cases h1 : x = 1
  · subst h1
    have : 1 / 2 ^ u = 0 := Nat.div_eq_of_lt (by
      have : 2 ^ 1 ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu
      omega)
    omega
  have he : x % 2 = 0 := by omega
  obtain ⟨g1, g2⟩ := goodl_stop R t x hG he
  obtain ⟨r1, -⟩ := read_right R t (x + 1) u g1 g2 hu
  simp only [Nat.add_sub_cancel] at r1
  have hxN : x < 2 * N := by have : x ≤ x * 2 ^ t := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t); omega
  have hle := anc_level N H j x u hN hxN hj e.symm t hxt
  exact ⟨t + u, by omega, hle, by rw [← e, r1]⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem climbl_read (A : Act M F) (st st1 : cp.LazySegmentTree M F) (p : M → Bool) (H R t : Nat) (x : Int) (sm : M)
    (hstop : ¬ (1 < x.toNat ∧ x.toNat % 2 = 1))
    (hL : LInv A.m (virt A (nodeF st) (lazyF st)) st.n_node.toNat p R x.toNat sm t) (hG : GoodL R t (x.toNat + 1))
    (hI : PInvS A st (AncS (R - 1) H H) st1) (hN : st.n_node.toNat = 2 ^ H) (hR1 : st.n_node.toNat < R) :
    Cpp.get st1.node x = virt A (nodeF st) (lazyF st) x.toNat ∧ x.toNat < 2 * st.n_node.toNat ∧
      ∀ j, 1 ≤ j → SAnc j x.toNat → AncS (R - 1) H H j := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hL
  have hx2 : x.toNat * 2 ^ t < 2 * st.n_node.toNat := by
    have : x.toNat * 2 ^ t < (x.toNat + 1) * 2 ^ t := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos t)
    omega
  have hanc := climbl_anc _ H R t x.toNat hN hR1 h4 h1 hstop hG hx2
  have hxN : x.toNat < 2 * st.n_node.toNat := by
    have : x.toNat ≤ x.toNat * 2 ^ t := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t); omega
  rw [get_eq]; exact ⟨read_of_anc A st st1 _ hI x.toNat hxN hanc, hxN, hanc⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
theorem climbl_init_facts (m : Mon M) (a : Nat → M) (p : M → Bool) (N H R t : Nat) (rr : Int) (sm : M)
    (hN : N = 2 ^ H) (hH : H ≤ 30) (hL : LInv m a N p R (rr.toNat - 1) sm t) :
    rr.toNat - 1 + 1 = rr.toNat ∧ (rr.toNat - 1 + 1) * 2 ^ t = rr.toNat * 2 ^ (H - Nat.log2 (rr.toNat - 1)) ∧
      rr.toNat - 1 < fuel ∧ 1 ≤ rr - 1 := by
  have hx1 := hL.1
  have hrr : 1 ≤ rr - 1 := by omega
  revert hrr
  generalize rr.toNat = x at *
  intro hrr
  have hb := hL.2.2.2.1
  have hb2 := hL.2.2.1
  have hp := Nat.two_pow_pos t
  have h30 : 2 ^ H ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hH
  have e1 : x - 1 + 1 = x := by omega
  refine ⟨e1, by rw [← SegmentTree.linv_height m _ _ _ hN p _ _ _ _ hL, e1], ?_⟩
  have : x - 1 < 2 ^ 32 := by
    have : x - 1 ≤ (x - 1 + 1) * 2 ^ t := by nlinarith
    omega
  exact ⟨lt_trans this (by unfold fuel; norm_num), hrr⟩

set_option maxHeartbeats 1000000 in
theorem lsearch_left_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA) {G : Type}
    [Cpp.Invoke1 G M Bool] (p : M → Bool) (cF : Nat) (g : G)
    (hF : ∀ x, ∀ {Q : PostCond Bool PS}, ⦃fun t => Q.1 (p x) (t + cF)⦄
      (Cpp.Invoke1.call (A := M) (R := Bool) g x) ⦃Q⦄)
    (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v) (hsmall : v.length ≤ 2 ^ 29)
    (r : Int) (h0 : 0 ≤ r) (hr : r ≤ v.length) (hpe : p A.m.e = true) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.search_prod_left st r g
    ⦃⇓ res c => ⌜0 ≤ res.1 ∧ res.1 ≤ r ∧ p (rf A.m (fun i => v[i]!) res.1.toNat (r - res.1).toNat) = true ∧
      (res.1 = 0 ∨ p (rf A.m (fun i => v[i]!) (res.1 - 1).toNat (r - res.1 + 1).toNat) = false) ∧
      LValid A res.2 v ∧
      c ≤ t0 + 4 + 2 * cE + 2 * cF + cOp + (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) +
        st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI)⌝⦄ := by
  have hP : ∀ (st : cp.LazySegmentTree M F) (k : Int), 1 ≤ k → k < st.n_node →
      st.node.size = 2 * st.n_node.toNat → st.lazy.size = st.n_node.toNat → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.push st k
      ⦃⇓ st' c => ⌜(fun i => st'.node[i]!) = pushA A (fun i => st.node[i]!) (fun i => st.lazy[i]!) k.toNat ∧
        (fun i => st'.lazy[i]!) = pushZ A (fun i => st.lazy[i]!) st.n_node.toNat k.toNat ∧
        st'.node.size = st.node.size ∧ st'.lazy.size = st.lazy.size ∧
        st'.n = st.n ∧ st'.n_node = st.n_node ∧ st'.h_node = st.h_node ∧
        c ≤ t0 + 3 + 2 * cA + 2 * cC + cI⌝⦄ :=
    fun st k hk hkN hsz hlz t0 => push_fun_spec A cE cOp cI cC cA hO st k hk hkN hsz hlz t0
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
      (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
  have hn := hv.n
  have hnn := hv.nn
  have hsz := hv.size
  have hlz := hv.lsize
  have hht := lheight_le A st v hv hsmall
  set a : Nat → M := virt A (nodeF st) (lazyF st) with ha
  set N := st.n_node.toNat with hNdef
  set h := st.h_node.toNat with hhdef
  set R := (r + st.n_node).toNat with hRdef
  set PC := 3 + 2 * cA + 2 * cC + cI with hPC
  set B := t0 + 1 + 2 * cE + cF + h * (1 + PC) with hB
  set D := 2 + 2 * cOp + cF with hD
  set E := 1 + 2 * cOp + cF + PC with hEc
  have hshape : N = 2 ^ h ∧ 1 ≤ st.h_node ∧ v.length ≤ N ∨ v = [] := by
    rcases hv.shape with ⟨h1, -⟩ | ⟨h1, h2, h3, -⟩
    · exact Or.inr h1
    · exact Or.inl ⟨h1, h2, h3⟩
  mvcgen [cp.LazySegmentTree.search_prod_left, hE, hOp, hF, hP]
  case inv1 =>
    exact ⇓⟨xs, n', nn', hh', nd', lz'⟩ c =>
      ⌜PInvS A st (AncS (R - 1) h xs.prefix.length) ⟨n', nn', hh', nd', lz'⟩ ∧
        c ≤ t0 + 1 + cE + cF + xs.prefix.length * (1 + PC)⌝
  case vc8.inv =>
    exact ⟨fun ⟨ret, n'', nn'', hh'', nd'', lz'', rr, sm⟩ c => ⌜ret = none ∧
              PInvS A st (AncS (R - 1) h h) ⟨n'', nn'', hh'', nd'', lz''⟩ ∧ 1 ≤ rr ∧
              ∃ t k, LInv A.m a N p R (rr.toNat - 1) sm t ∧ GoodL R t rr.toNat ∧
                k ≤ t + (if (rr.toNat - 1) % 2 = 1 ∧ 1 < rr.toNat - 1 then 1 else 0) ∧ c ≤ B + D * k + t⌝,
           fun ⟨ret, n'', nn'', hh'', nd'', lz'', _, _⟩ c => ⌜match ret with
              | some res => ∃ x : Nat, res.1 = (x : Int) + 1 - st.n_node ∧ (∃ Q, PInvS A st Q res.2) ∧ N ≤ x ∧
                  x < R ∧ p (rf A.m a (x + 1) (R - (x + 1))) = true ∧ p (rf A.m a x (R - x)) = false ∧
                  c ≤ B + D * h + h + 3 + cOp + cF + h * E
              | none => p (rf A.m a N (R - N)) = true ∧ PInvS A st (AncS (R - 1) h h) ⟨n'', nn'', hh'', nd'', lz''⟩ ∧
                  c ≤ B + D * (h + 1) + h⌝,
           fun ⟨_, _, _, _, _, _, rr, _⟩ => rr.toNat * 2 ^ (h - Nat.log2 (rr.toNat - 1))⟩
  case vc9.inv =>
    rename_i b _ _ _ _ _ _ _ _ _ _ _ rb smb _ _ _
    exact ⟨fun x c => ⌜1 ≤ x ∧ x ≤ rb - 1 ∧ ∃ t k, LInv A.m a N p R x.toNat smb t ∧ GoodL R t (x.toNat + 1) ∧
              (x.toNat + 1) * 2 ^ t = rb.toNat * 2 ^ (h - Nat.log2 (rb.toNat - 1)) ∧
              (if x = rb - 1 then
                k ≤ t + (if (rb.toNat - 1) % 2 = 1 ∧ 1 < rb.toNat - 1 then 1 else 0) else k ≤ t) ∧
              c ≤ B + D * k + t + 1⌝,
           fun x c => ⌜1 ≤ x ∧ ¬ (1 < x.toNat ∧ x.toNat % 2 = 1) ∧ ∃ t k, LInv A.m a N p R x.toNat smb t ∧
              GoodL R t (x.toNat + 1) ∧
              (x.toNat + 1) * 2 ^ t = rb.toNat * 2 ^ (h - Nat.log2 (rb.toNat - 1)) ∧ k ≤ t ∧
              c ≤ B + D * k + t + 2⌝,
           fun x => x.toNat⟩
  case vc13.inv =>
    exact ⟨fun ⟨n3, nn3, hh3, nd3, lz3, xd, smd⟩ c => ⌜0 ≤ xd ∧
              PInvS A st (fun j => 1 ≤ j ∧ SAnc j xd.toNat) ⟨n3, nn3, hh3, nd3, lz3⟩ ∧
              ∃ t, DLInv A.m a N p R xd.toNat smd t ∧ t ≤ h ∧
              c + t * E ≤ B + D * h + h + 2 + cOp + cF + h * E⌝,
           fun ⟨n3, nn3, hh3, nd3, lz3, xd, smd⟩ c => ⌜0 ≤ xd ∧
              PInvS A st (fun j => 1 ≤ j ∧ SAnc j xd.toNat) ⟨n3, nn3, hh3, nd3, lz3⟩ ∧ N ≤ xd.toNat ∧
              DLInv A.m a N p R xd.toNat smd 0 ∧ c ≤ B + D * h + h + 3 + cOp + cF + h * E⌝,
           fun ⟨_, _, _, _, _, xd, _⟩ => 2 * N - xd.toNat⟩
  all_goals simp +zetaDelta at *
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.2 = lz' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.2.1 = nd' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.2.1 = hh' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).2.1 = nn' at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F›).1 = n' at *)
  all_goals try (
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2.2 = smo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2.1 = ro at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.1 = lzo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.1 = ndo at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.1 = hho at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.1 = nno at *
    generalize (‹Option (ℤ × cp.LazySegmentTree M F) × ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.1 = no at *)
  all_goals try (
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.2 = smd at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.2.1 = xd at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.2.1 = lz3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.2.1 = nd3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.2.1 = hh3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).2.1 = nn3 at *
    generalize (‹ℤ × ℤ × ℤ × Array M × Array F × ℤ × M›).1 = n3 at *)
  case vc1.isTrue.isTrue.isTrue =>
    subst ‹r = 0›
    refine ⟨le_refl _, by simp [rf, hpe], hv, ?_⟩
    generalize (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) = X
    omega
  case vc30.isFalse => omega
  case vc7.isTrue.isTrue.isFalse.pre =>
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, hv.state, fun _ _ => rfl, fun j ⟨s, h1, h2, _⟩ => by omega⟩, by omega⟩
  case vc2.a | vc3.a =>
    obtain ⟨⟨g1, g2, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, hh1, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have := path_k ‹rangeDown _ _ = _ ++ _ :: _› (r + st.n_node - 1) _ hN (by omega) (by omega) (by omega)
    simp at g2; omega
  case vc4.a | vc5.a =>
    obtain ⟨⟨g1, g2, g3, g4, g5, -⟩, -⟩ := ‹PInvS _ _ _ _ ∧ _›
    simp at g2 g4 g5; first | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc6.step.post.success =>
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A (fun i => nd'[i]!) _ _ ∧ _›
    rcases hshape with ⟨hN, hh1, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    obtain ⟨m, hm1, hm, e1⟩ := one_level ‹rangeDown _ _ = _ ++ _ :: _› (r + st.n_node - 1) (by omega)
    simp only [hm1] at *
    simp only [e1, Int.toNat_natCast] at *
    rw [show (r + st.n_node - 1).toNat = (r + st.n_node).toNat - 1 by omega] at a1 a2
    have P1 := pinvs_push_lvl A st ⟨n', nn', hh', nd', lz'⟩ _ _ _ _ ((r + st.n_node).toNat - 1) hN (by omega)
      (by omega) hm hI (fun j hj => ancs_lt _ _ _ _ j hN (by omega) (by omega) hj) a1 a2 a3 a4 a5 a6 a7
    refine ⟨pinvs_mono A st _ _ _ P1 (fun j hj => ?_), ?_⟩
    · obtain ⟨s', h1, h2, rfl⟩ := hj
      by_cases e : s' = st.h_node.toNat - m
      · right; rw [e]
      · left; exact ⟨s', by omega, h2, rfl⟩
    · have : (m + 1) * (1 + (3 + 2 * cA + 2 * cC + cI)) = m * (1 + (3 + 2 * cA + 2 * cC + cI)) +
          (1 + (3 + 2 * cA + 2 * cC + cI)) := by ring
      omega
  case vc25.isTrue.isTrue.isFalse.post.success.pre =>
    obtain ⟨hI, hc⟩ := ‹PInvS _ _ _ _ ∧ _›
    have hlen : (rangeDown 1 st.h_node).length = st.h_node.toNat := by simp [rangeDown]
    rw [hlen] at hI hc
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have hR1 : st.n_node.toNat < (r + st.n_node).toNat := by omega
    have hR2 : (r + st.n_node).toNat ≤ 2 * st.n_node.toNat := by omega
    have hL := linv_init A.m (virt A (nodeF st) (lazyF st)) _ p (r + st.n_node).toNat hR1 hR2 hpe
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2 ^ (st.h_node.toNat - ((r + st.n_node).toNat - 1).log2) ≤ 2 ^ st.h_node.toNat :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : (r + st.n_node).toNat * 2 ^ (st.h_node.toNat - ((r + st.n_node).toNat - 1).log2) ≤
        2 ^ 31 * 2 ^ 30 := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨⟨hI, by omega, 0, hL, goodl_init _, 0, by simp, by omega⟩, ?_⟩
    simp [fuel]; omega
  case vc10.step.isTrue =>
    obtain ⟨hx1, hxle, t, hL, hG, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    have hstop := SegmentTree.stop_of _ hx1 ‹_›
    refine ⟨hx1, fun _ => by omega, t, hL, hG, hR, k, ?_, by omega⟩
    split at hk
    · rename_i heq; rw [if_neg (by omega)] at hk; exact hk
    · exact hk
  case vc11.step.isFalse =>
    obtain ⟨hx1, hxle, t, hL, hG, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ _ ≤ _ ∧ _›
    obtain ⟨hgt, hodd⟩ := ‹(1 : ℤ) < _ ∧ ¬ Cpp.mod _ 2 = 0›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    obtain ⟨c0, c1, c2, c3⟩ := SegmentTree.climb_left_int A.m _ _ _ hN p _ _ _ _ hgt hodd hL
    have hG' := goodl_climb_int _ _ _ hgt hodd hG
    refine ⟨⟨c0, by omega, t + 1, c2, hG', by rw [c3, hR], k, ?_, by omega⟩, c1, by omega⟩
    rw [if_neg (by omega)]
    split at hk
    · split at hk <;> omega
    · omega
  case vc12.step.pre =>
    obtain ⟨-, -, hr1, t, hL, hG, k, hk, hc⟩ := ‹_ = none ∧ _›
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hx1 := hL.1
    obtain ⟨e1, e2, e3, e4⟩ := climbl_init_facts A.m _ p _ _ _ _ _ _ hN (by omega) hL
    exact ⟨⟨e4, t, hL, by rw [e1]; exact hG, e2, k, hk, hc⟩, e3⟩
  case vc14.step.isTrue =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    have e2 := hI.2.1
    simp only at e2
    have ht0 := dlinv_exit A.m _ _ p _ _ _ _ hD (by omega)
    subst ht0
    exact ⟨hd0, hI, Or.inl (by omega), hD, by omega⟩
  case vc15.a | vc16.a | vc17.a | vc18.a =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨g1, g2, g3, g4, g5, -⟩ := hI
    have h1l := hD.1.1
    simp only at g2 g4 g5
    first | omega | (rw [g4, g2]; exact hsz) | (rw [g5, g2]; exact hlz)
  case vc19.step.isFalse.post.success.isTrue =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A _ _ _ ∧ _›
    have g2 := hI.2.1
    simp only at g2
    have h1l := hD.1.1
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hD.1.2.2.2.1; simp at hn; omega
    obtain ⟨P1, P2, -, rd⟩ := desc_push A st _ _ xd.toNat hI h1l (by omega) a1 (by rw [g2] at a2 ⊢; exact a2) a3 a4 a5
      a6 a7
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨t', rfl, d1, d2⟩ := dlinv_step A.m _ _ hVV hTr p _ xd.toNat smd _ hD (by omega)
    clear hTr hVV hst
    rw [get_eq, show (xd * 2 + 1).toNat = 2 * xd.toNat + 1 by omega] at *
    have hcost : (t' + 1) * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        t' * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) + (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := by
      ring
    rw [show (xd * 2).toNat = 2 * xd.toNat by omega, rd]
    have hf : p (A.m.op (virt A (nodeF st) (lazyF st) (2 * xd.toNat + 1)) smd) = true := by
      rw [← rd]; exact ‹p (A.m.op _ smd) = true›
    exact ⟨⟨hd0, P1, t', d1 hf, by omega, by omega⟩, by omega⟩
  case vc20.step.isFalse.post.success.isFalse =>
    obtain ⟨hd0, hI, t, hD, ht, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ (fun j => 1 ≤ j ∧ SAnc j _) _ ∧ _›
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, ac⟩ := ‹(fun i => _) = pushA A _ _ _ ∧ _›
    have g2 := hI.2.1
    simp only at g2
    have h1l := hD.1.1
    rcases hshape with ⟨hN, -, -⟩ | hnil
    swap; · subst hnil; have := hD.1.2.2.2.1; simp at hn; omega
    obtain ⟨P1, P2, -, rd⟩ := desc_push A st _ _ xd.toNat hI h1l (by omega) a1 (by rw [g2] at a2 ⊢; exact a2) a3 a4 a5
      a6 a7
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨t', rfl, d1, d2⟩ := dlinv_step A.m _ _ hVV hTr p _ xd.toNat smd _ hD (by omega)
    clear hTr hVV hst
    rw [get_eq, show (xd * 2 + 1).toNat = 2 * xd.toNat + 1 by omega] at *
    have hcost : (t' + 1) * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        t' * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) + (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := by
      ring
    have hf : p (A.m.op (virt A (nodeF st) (lazyF st) (2 * xd.toNat + 1)) smd) = false := by
      rw [← rd]; first | exact ‹p (A.m.op _ smd) = false› | simpa using ‹¬ p (A.m.op _ smd) = true›
    exact ⟨⟨by omega, P2, t', d2 hf, by omega, by omega⟩, by omega⟩
  case vc21.step.post.success.isTrue.pre =>
    obtain ⟨hx1, hev, t, hL, hG, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hR1 : st.n_node.toNat < (r + st.n_node).toNat := by
      have := hL.2.1; have := hL.2.2.1; have := hL.1; have hp := Nat.two_pow_pos t; nlinarith
    obtain ⟨rd, hxN, hanc⟩ := climbl_read A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo
      (fun ⟨h1, h2⟩ => by have := hev (by omega); omega) hL hG hI hN hR1
    have hf := ‹p (A.m.op (get ndo _) smo) = false›
    rw [rd] at hf
    have ht := t_le _ _ _ _ hN hL.1 (le_trans hL.2.2.1 hL.2.2.2.1)
    have h30 : 2 ^ st.h_node.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hN30 : st.n_node.toNat ≤ 2 ^ 30 := by rw [hN]; exact h30
    refine ⟨⟨by omega, pinvs_mono A st _ _ _ hI (fun j ⟨h1, h2⟩ => hanc j h1 h2), t, ⟨hL, hf⟩, ht, ?_⟩,
      lt_of_le_of_lt (Nat.sub_le _ _) (by unfold fuel; omega)⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have m2 : t * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) ≤
        st.h_node.toNat * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) := Nat.mul_le_mul_right _ ht
    omega
  case vc22.step.post.success.isTrue.post.success =>
    obtain ⟨hd0, hI, -, hD, hc⟩ := ‹(0 : ℤ) ≤ _ ∧ PInvS _ _ _ _ ∧ (_ ∨ _) ∧ DLInv _ _ _ _ _ _ _ 0 ∧ _›
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨-, hop⟩ := linv_pass A.m _ _ hVV hTr p _ _ _ _ hD.1
    clear hTr hVV hst
    have g2 := hI.2.1
    simp only at g2
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := hD
    simp at h2 h3 h6 hop
    refine ⟨xd.toNat, by omega, ⟨_, hI⟩, by omega, by omega, by rw [← h6]; exact h7, by rw [← hop]; exact h8, ?_⟩
    omega
  case vc23.step.post.success.isFalse.isTrue =>
    obtain ⟨hx1, hev, t, hL, hG, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hR1 : st.n_node.toNat < (r + st.n_node).toNat := by
      have := hL.2.1; have := hL.2.2.1; have := hL.1; have hp := Nat.two_pow_pos t; nlinarith
    obtain ⟨rd, hxN, hanc⟩ := climbl_read A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo
      (fun ⟨h1, h2⟩ => by have := hev (by omega); omega) hL hG hI hN hR1
    have hpow := (SegmentTree.pow_cond_left _ (lt_of_lt_of_le zero_lt_one hx1)).mp ‹_›
    have ht := t_le _ _ _ _ hN hL.1 (le_trans hL.2.2.1 hL.2.2.2.1)
    have hf := ‹p (A.m.op (get ndo _) smo) = true›
    rw [rd] at hf
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    obtain ⟨-, hend⟩ := linv_end A.m _ _ _ hN hVV hTr p _ _ _ _ hL hf hpow
    clear hTr hVV hst
    refine ⟨hend, hI, ?_⟩
    have m1 : (2 + 2 * cOp + cF) * k ≤ (2 + 2 * cOp + cF) * st.h_node.toNat := Nat.mul_le_mul_left _ (by omega)
    have : (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) = (2 + 2 * cOp + cF) * st.h_node.toNat + (2 + 2 * cOp + cF) := by
      ring
    omega
  case vc24.step.post.success.isFalse.isFalse =>
    obtain ⟨hx1, hev, t, hL, hG, hR, k, hk, hc⟩ := ‹(1 : ℤ) ≤ _ ∧ ((1 : ℤ) < _ → _) ∧ _›
    obtain ⟨-, hI, -⟩ := ‹_ = none ∧ PInvS _ _ _ _ ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; have := hL.2.2.2.1; simp at hn; omega
    have hR1 : st.n_node.toNat < (r + st.n_node).toNat := by
      have := hL.2.1; have := hL.2.2.1; have := hL.1; have hp := Nat.two_pow_pos t; nlinarith
    obtain ⟨rd, hxN, hanc⟩ := climbl_read A st ⟨no, nno, hho, ndo, lzo⟩ p _ _ t _ smo
      (fun ⟨h1, h2⟩ => by have := hev (by omega); omega) hL hG hI hN hR1
    have hpow : ¬ ∃ k, _ = 2 ^ k := fun h => ‹¬ _› ((SegmentTree.pow_cond_left _ (lt_of_lt_of_le zero_lt_one hx1)).mpr h)
    have h3 := SegmentTree.three_le_of _ hx1 hpow hev
    have hf := ‹p (A.m.op (get ndo _) smo) = true›
    rw [rd] at hf
    have hst := hv.state
    have hVV := virt_V A _ _ _ hst.1 hst.2.1
    have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
    have hL' := linv_next A.m _ _ _ hN hVV hTr p _ _ _ _ hL hf hpow
    clear hTr hVV hst
    have hG' := goodl_pass _ _ _ hG h3.2
    rw [rd]
    refine ⟨⟨hI, hx1, t, hL', hG', k + 1, by rw [if_pos (by omega)]; omega, ?_⟩, ?_⟩
    · have : (2 + 2 * cOp + cF) * (k + 1) = (2 + 2 * cOp + cF) * k + (2 + 2 * cOp + cF) := by ring
      omega
    · have hh := SegmentTree.linv_height A.m _ _ _ hN p _ _ _ _ hL'
      exact SegmentTree.measure_dec_left st.n_node.toNat _ _ _ _ (by omega) hh hR
  case vc26.isTrue.isTrue.isFalse.post.success.post.success.h_1 =>
    simp only [‹_ = some _›] at *
    obtain ⟨x, hx, ⟨Q, hQ⟩, hN1, hx2, hp1, hp2, hc⟩ := ‹∃ x : Nat, _ = _ ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have e1 : x + 1 = st.n_node.toNat + ((x : Int) + 1 - st.n_node).toNat := by omega
    rw [e1] at hp1
    rw [show (r + st.n_node).toNat - (st.n_node.toNat + ((x : Int) + 1 - st.n_node).toNat) =
      (r - ((x : Int) + 1 - st.n_node)).toNat by omega, lrf_leaves A st v hv _ _ (by omega)] at hp1
    have hl2 := lrf_leaves A st v hv (((x : Int) + 1 - st.n_node).toNat - 1)
      ((r - ((x : Int) + 1 - st.n_node) + 1).toNat) (by omega)
    rw [show st.n_node.toNat + (((x : Int) + 1 - st.n_node).toNat - 1) = x by omega,
      show (r - ((x : Int) + 1 - st.n_node) + 1).toNat = (r + st.n_node).toNat - x by omega] at hl2
    rw [hl2] at hp2
    rw [show (r + st.n_node).toNat - x = (r - ((x : Int) + 1 - st.n_node) + 1).toNat by omega] at hp2
    rw [hx]
    refine ⟨by omega, by omega, by simpa using hp1, Or.inr (by simpa using hp2), pinvs_valid A st _ v hv _ hQ, ?_⟩
    have : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * st.h_node.toNat + st.h_node.toNat + st.h_node.toNat * (1 + 2 * cOp + cF) +
          (4 + 4 * cOp + 2 * cF) := by ring
    have : st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) = st.h_node.toNat * (1 + (3 + 2 * cA + 2 * cC + cI)) +
        st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    have : st.h_node.toNat * (1 + 2 * cOp + cF + (3 + 2 * cA + 2 * cC + cI)) =
        st.h_node.toNat * (1 + 2 * cOp + cF) + st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    omega
  case vc27.isTrue.isTrue.isFalse.post.success.post.success.h_2 =>
    simp only [‹_ = none›] at *
    obtain ⟨hp1, hI, hc⟩ := ‹p _ = true ∧ _›
    rcases hshape with ⟨hN, -, hle⟩ | hnil
    swap; · subst hnil; simp at hn; omega
    have := lrf_leaves A st v hv 0 r.toNat (by omega)
    simp only [Nat.add_zero] at this
    rw [show (r + st.n_node).toNat - st.n_node.toNat = r.toNat by omega, this] at hp1
    refine ⟨by omega, by simpa using hp1, pinvs_valid A st _ v hv _ hI, ?_⟩
    have e : (st.h_node.toNat + 1) * (4 + 4 * cOp + 2 * cF) =
        (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) + (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := by ring
    have : st.h_node.toNat + 1 ≤ (2 + 2 * cOp + cF) * (st.h_node.toNat + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : st.h_node.toNat * (7 + 4 * cA + 4 * cC + 2 * cI) = st.h_node.toNat * (1 + (3 + 2 * cA + 2 * cC + cI)) +
        st.h_node.toNat * (3 + 2 * cA + 2 * cC + cI) := by ring
    omega

end Proofs.Cpp.LazySegmentTree

namespace Proofs.Cpp.LazySegmentTree
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeMath Proofs.Cpp.LazySegmentTreeMath
open Proofs.Cpp.SegmentTree (HInv LeafInv BuildInv)

variable {M F : Type} [Inhabited M] [Inhabited F] [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M]
  [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F] [Cpp.Method1 "apply" F M M]

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- A plain segment tree with trivial tags is a lazy segment tree of the same values. -/
theorem lvalid_of_valid (A : Act M F) (st : cp.SegmentTree M) (v : List M) (hv : SegmentTree.Valid A.m st v) :
    LValid A ⟨st.n, st.n_node, st.h_node, st.node, Cpp.replicate st.n_node A.id⟩ v := by
  have hz : ∀ j, j < st.n_node.toNat → (Cpp.replicate st.n_node A.id)[j]! = A.id := by
    intro j hj
    rw [getElem!_pos _ _ (by simp [replicate]; omega)]
    simp [replicate]
  have hvirt : ∀ k, k < 2 * st.n_node.toNat →
      virt A (fun i => st.node[i]!) (fun i => (Cpp.replicate st.n_node A.id)[i]!) k = st.node[k]! := by
    intro k hk
    apply virt_of_id A _ _ _ hv.allV k hk
    intro j hj ⟨t, ht⟩ hne
    have : t ≠ 0 := by intro h0; subst h0; simp at ht; omega
    have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : j * 2 ≤ k := by
      rw [ht]
      calc k / 2 ^ t * 2 ≤ k / 2 ^ t * 2 ^ t := Nat.mul_le_mul_left _ (by simpa using this)
        _ ≤ k := Nat.div_mul_le_self _ _
    exact hz j (by omega)
  refine ⟨hv.n, hv.nn, hv.hn, hv.shape, hv.size, by simp [replicate], ⟨hv.allV, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩,
    fun i hi => ?_, fun j h1 h2 => ?_⟩
  · dsimp only at h2
    show A.VF (Cpp.replicate st.n_node A.id)[k]!
    rw [hz k h2]; exact A.hid
  · dsimp only at h2
    show st.node[k]! = A.ap (Cpp.replicate st.n_node A.id)[k]! (A.m.op st.node[2 * k]! st.node[2 * k + 1]!)
    rw [hz k h2, A.ap_id _ (A.m.closed _ _ (hv.allV _ (by omega)) (hv.allV _ (by omega)))]
    exact hv.tree k h1 h2
  · have hb : st.n_node.toNat + i < 2 * st.n_node.toNat := by
      rcases hv.shape with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
      · simp [h1] at hi
      · omega
    show virt A (fun i => st.node[i]!) (fun i => (Cpp.replicate st.n_node A.id)[i]!) (st.n_node.toNat + i) = _
    rw [hvirt _ hb]; exact hv.leaf i hi
  · dsimp only at h2
    show virt A (fun i => st.node[i]!) (fun i => (Cpp.replicate st.n_node A.id)[i]!) (st.n_node.toNat + j) = _
    rw [hvirt _ (by omega)]; exact hv.pad j h1 h2

theorem upd_exit (n : Nat) (N hh i : Int) (hH : HInv n N hh) (hi2 : i ≤ N - 1) (h : 0 ≤ i ∨ i = N - 1)
    (hlt : i < 1) : i.toNat = 0 ∧ (N - 1 - i).toNat ≤ N.toNat - 1 := by
  have : 0 ≤ N := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  omega

theorem upd_step (n : Nat) (N hh i : Int) (hH : HInv n N hh) (hi2 : i ≤ N - 1) (hge : 1 ≤ i) :
    i - 1 ≤ N - 1 ∧ (0 ≤ i - 1 ∨ i - 1 = N - 1) ∧ ((↑(i.toNat) : Int) = i) ∧ i.toNat < N.toNat ∧
      (i - 1).toNat = i.toNat - 1 ∧ (N - 1 - (i - 1)).toNat = (N - 1 - i).toNat + 1 ∧
      (i - 1 + 1).toNat < (i + 1).toNat := by
  have : 0 ≤ N := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  omega

theorem cost_upd (a b : Int) (s base K : Nat) (hb : b ≤ a - 1) (h : s = base + (a - 1 - b).toNat * (2 + K)) :
    s + 1 + 1 + K = base + (a - b).toNat * (2 + K) := by
  rw [h, show (a - b).toNat = (a - 1 - b).toNat + 1 by omega, Nat.add_mul, Nat.one_mul]; omega

theorem init_vec_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA) (v : Array M)
    (hV : ∀ x ∈ v.toList, A.m.V x) (hsmall : v.size ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.LazySegmentTree.init_vec (F := F) v)
    ⦃⇓ st c => ⌜LValid A st v.toList ∧ c ≤ t0 + 4 + cE + cI + (13 + 2 * cOp) * v.size⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hI : ∀ {Q : PostCond F PS}, ⦃fun t => Q.1 A.id (t + cI)⦄
      (Cpp.StaticCall.call (name := "id") (T := F) (R := F)) ⦃Q⦄ := hO.id
  have hU : ∀ (st : cp.LazySegmentTree M F) (i : Int) {Q : PostCond (cp.LazySegmentTree M F) PS},
      ⦃fun c => Q.1 { st with node := Cpp.set st.node i (A.m.op (Cpp.get st.node (i * 2))
        (Cpp.get st.node (i * 2 + 1))) } (c + 1 + cOp)⦄ cp.LazySegmentTree.update_int st i ⦃Q⦄ := by
    intro st i Q
    have hOp : ∀ a b, ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 (A.m.op a b) (t + cOp)⦄
        (Cpp.AdlCall2.call (name := "op") (A := M) (B := M) (R := M) a b) ⦃Q⦄ := hO.op
    mvcgen [cp.LazySegmentTree.update_int, hOp]
  mvcgen [cp.LazySegmentTree.init_vec, hE, hU, hI]
  case vc1.inv =>
    exact ⟨fun ⟨nn, hh⟩ c => ⌜HInv v.size nn hh ∧ hh ≤ 29 ∧ c = t0 + 1 + hh.toNat⌝,
           fun ⟨nn, hh⟩ c => ⌜HInv v.size nn hh ∧ hh ≤ 29 ∧ v.size ≤ nn ∧ c = t0 + 2 + hh.toNat⌝,
           fun ⟨_, hh⟩ => (30 - hh).toNat⟩
  case inv1 =>
    rename_i s1 h1 n r nn hh s h t2 node lz
    exact ⇓⟨xs, node'⟩ c => ⌜LeafInv v A.m.e r.1.toNat xs.prefix.length node' ∧
      c = s + cE + 2 * r.1.toNat + cI + r.1.toNat + xs.prefix.length⌝
  case vc7.inv =>
    rename_i _ _ _ r1 _ _ s1 _ _ _ _ _ _ _ _
    exact ⟨fun ⟨n', nn', hh', nd', lz', i⟩ c => ⌜n' = v.size ∧ nn' = r1.1 ∧ hh' = r1.2 ∧
              lz' = Cpp.replicate r1.1 A.id ∧ i ≤ r1.1 - 1 ∧ (0 ≤ i ∨ i = r1.1 - 1) ∧
              BuildInv A.m v r1.1.toNat i.toNat nd' ∧
              c = s1 + cE + 3 * r1.1.toNat + cI + v.size + (r1.1 - 1 - i).toNat * (2 + cOp)⌝,
           fun ⟨n', nn', hh', nd', lz', _⟩ c => ⌜n' = v.size ∧ nn' = r1.1 ∧ hh' = r1.2 ∧
              lz' = Cpp.replicate r1.1 A.id ∧ BuildInv A.m v r1.1.toNat 0 nd' ∧
              c ≤ s1 + cE + 3 * r1.1.toNat + cI + v.size + (r1.1.toNat - 1) * (2 + cOp) + 1⌝,
           fun ⟨_, _, _, _, _, i⟩ => (i + 1).toNat⟩
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    obtain ⟨hI, hle, hc⟩ := ‹HInv _ _ _ ∧ _›
    exact ⟨hI, hle, by simpa [size] using ‹size v ≤ _›, by omega⟩
  case vc3.step.isFalse =>
    obtain ⟨hI, hle, hc⟩ := ‹HInv _ _ _ ∧ _›
    have hlt : (‹ℤ × ℤ›).1 < (v.size : Int) := by simpa [size] using ‹_ < size v›
    have h29 := SegmentTree.hinv_le v.size hsmall _ _ hI hlt
    have h0 : 0 ≤ (‹ℤ × ℤ›).2 := by rcases hI with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact ⟨⟨SegmentTree.hinv_step _ _ _ hI hlt, by omega, by omega⟩, by omega⟩
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
    have := SegmentTree.leafinv_step v A.m.e _ _ _ hI hl (by omega)
    rw [Int.toNat_of_nonneg h0] at this
    exact ⟨this, by omega⟩
  case vc6.post.success.pre =>
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    have h0 : 0 ≤ (‹ℤ × ℤ›).1 := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    have := SegmentTree.leafinv_init v A.m.e (‹ℤ × ℤ›).1.toNat
    rw [Int.toNat_of_nonneg h0] at this
    exact ⟨this, by omega⟩
  case vc10.post.success.post.success.pre =>
    obtain ⟨hI, hc⟩ := ‹LeafInv _ _ _ _ _ ∧ _›
    obtain ⟨hH, -, hvN, -⟩ := ‹HInv _ _ _ ∧ _›
    have h0 : 0 ≤ (‹ℤ × ℤ›).1 := by rcases hH with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
    simp [range, size] at hI hc
    refine ⟨⟨by simp [size], SegmentTree.buildinv_init A.m v (fun x hx => hV x (by simpa using hx)) _ (by omega) _ hI,
      by omega⟩, ?_⟩
    have hb := SegmentTree.hinv_bounds _ _ _ hH
    simp [fuel]; omega
  case vc8.step.isTrue =>
    obtain ⟨e1, e2, e3, e4, hi1, hi2, hB, hc⟩ := ‹_ = (v.size : Int) ∧ _›
    obtain ⟨hH, -⟩ := ‹HInv _ _ _ ∧ _›
    obtain ⟨a1, a2⟩ := upd_exit _ _ _ _ hH hi1 hi2 ‹(_ : ℤ) < 1›
    rw [a1] at hB
    refine ⟨e1, e2, e3, e4, hB, ?_⟩
    have := Nat.mul_le_mul_right (2 + cOp) a2
    omega
  case vc9.step.isFalse =>
    obtain ⟨e1, e2, e3, e4, hi1, hi2, hB, hc⟩ := ‹_ = (v.size : Int) ∧ _›
    obtain ⟨hH, -⟩ := ‹HInv _ _ _ ∧ _›
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := upd_step _ _ _ _ hH hi1 ‹(1 : ℤ) ≤ _›
    have hBs := SegmentTree.buildinv_step A.m v _ _ _ hB (by omega) u4
    rw [u3] at hBs
    have hge := ‹(1 : ℤ) ≤ _›
    exact ⟨⟨e1, e2, e3, e4, le_trans hi1 (by omega), Or.inl hge, hBs, cost_upd _ _ _ _ _ hi1 hc⟩,
      Int.lt_add_one_iff.mpr (le_trans (by norm_num) hge)⟩
  case vc11.post.success.post.success.post.success =>
    obtain ⟨e1, e2, e3, e4, hB, hc⟩ := ‹_ = (v.size : Int) ∧ _›
    obtain ⟨hH, -, hvN, hc1⟩ := ‹HInv _ _ _ ∧ _›
    obtain ⟨-, hc2⟩ := ‹LeafInv _ _ _ _ _ ∧ _›
    have hval := SegmentTree.buildinv_done A.m v _ _ _ e1 hH (by omega) _ hB
    rw [e2, e3, e4]
    refine ⟨lvalid_of_valid A _ _ hval, ?_⟩
    simp [range, size] at hc2
    rcases SegmentTree.hinv_bounds _ _ _ hH with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hc hvN hc2; rw [h2] at hc1; simp at hc hc1 hvN hc2; omega
    · have hm : ((‹ℤ × ℤ›).1.toNat - 1) * (2 + cOp) ≤ (2 * v.size) * (2 + cOp) :=
        Nat.mul_le_mul_right _ (by omega)
      have e5 : (2 * v.size) * (2 + cOp) = 4 * v.size + 2 * (cOp * v.size) := by ring
      have e6 : (13 + 2 * cOp) * v.size = 13 * v.size + 2 * (cOp * v.size) := by ring
      rw [e6]; omega

theorem init_int_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA) (n_ : Int) (h0 : 0 ≤ n_)
    (hs : n_ ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.LazySegmentTree.init_int (F := F) n_)
    ⦃⇓ st c => ⌜LValid A st (List.replicate n_.toNat A.m.e) ∧
      c ≤ t0 + 5 + 2 * cE + cI + (14 + 2 * cOp) * n_.toNat⌝⦄ := by
  have hE : ∀ {Q : PostCond M PS}, ⦃fun t => Q.1 A.m.e (t + cE)⦄
      (Cpp.StaticCall.call (name := "e") (T := M) (R := M)) ⦃Q⦄ := hO.e
  have hB := init_vec_spec (F := F) A cE cOp cI cC cA hO
  mvcgen [cp.LazySegmentTree.init_int, hE, hB]
  all_goals simp +zetaDelta at *
  case vc1.hV =>
    intro x hx
    simp [replicate] at hx
    rw [hx.2]; exact A.m.he
  case vc2.hsmall => simp [replicate]; omega
  case vc3.post.success =>
    obtain ⟨hv, hc⟩ := ‹LValid _ _ _ ∧ _›
    refine ⟨by simpa [replicate] using hv, ?_⟩
    simp [replicate] at hc
    have : (14 + 2 * cOp) * n_.toNat = n_.toNat + (13 + 2 * cOp) * n_.toNat := by ring
    omega

theorem init_0_spec (A : Act M F) (cE cOp cI cC cA : Nat) (hO : Ops A cE cOp cI cC cA) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.LazySegmentTree.init_0 (M := M) (F := F))
    ⦃⇓ st c => ⌜LValid A st [] ∧ c ≤ t0 + 6 + 2 * cE + cI⌝⦄ := by
  have hB := init_int_spec (F := F) A cE cOp cI cC cA hO
  mvcgen [cp.LazySegmentTree.init_0, hB]
  all_goals simp +zetaDelta at *
  obtain ⟨hv, hc⟩ := ‹LValid _ _ _ ∧ _›
  exact ⟨hv, by omega⟩

omit [Cpp.AdlCall2 "op" M M M] [Cpp.StaticCall "e" M M] [Cpp.AdlCall2 "compose" F F F] [Cpp.StaticCall "id" F F]
  [Cpp.Method1 "apply" F M M] in
/-- `product_all()` for `n ≥ 1`: the root holds the product (it has no ancestors to push). -/
theorem product_all_spec (A : Act M F) (st : cp.LazySegmentTree M F) (v : List M) (hv : LValid A st v)
    (hne : v ≠ []) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.LazySegmentTree.product_all st
    ⦃⇓ r c => ⌜r.1 = rf A.m (fun i => v[i]!) 0 v.length ∧ r.2 = st ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.LazySegmentTree.product_all]
  rcases hv.shape with ⟨h1, _⟩ | ⟨hN, hh, hle, -⟩
  · exact absurd h1 hne
  have hNpos : 2 ≤ st.n_node.toNat := by
    have : 2 ^ 1 ≤ 2 ^ st.h_node.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hN]; exact this
  have hst := hv.state
  have hVV := virt_V A _ _ _ hst.1 hst.2.1
  have hTr := virt_tree A _ _ _ hst.1 hst.2.1 hst.2.2
  have hroot := node_rf A.m _ st.n_node.toNat hVV hTr st.h_node.toNat 1 (le_refl _) (by rw [hN] <;> omega)
  simp only [Nat.one_mul] at hroot
  have hpad := rf_pad A.m _ st.n_node.toNat v.length st.n_node.toNat hVV hle (le_refl _) (by omega) hv.pad
  rw [← hN] at hroot
  rw [show st.n_node.toNat + v.length - st.n_node.toNat = v.length by omega,
    show 2 * st.n_node.toNat - st.n_node.toNat = st.n_node.toNat by omega] at hpad
  refine ⟨?_, rfl, by omega⟩
  have h1 : virt A (nodeF st) (lazyF st) 1 = st.node[1]! := by simp [virt, P_le_one A _ 1 _ (le_refl _)]; rfl
  rw [get_eq, show (1 : Int).toNat = 1 from rfl, ← h1, ← hroot, hpad]
  have := lrf_leaves A st v hv 0 v.length (by omega)
  simpa using this

end Proofs.Cpp.LazySegmentTree
