import Proofs.Cpp.Gen.SegmentTreeBeatsSum
import Proofs.Cpp.SegmentTreeBeatsSumCore

/-! # Segment tree beats with sums (library/segment_tree/segment_tree_beats_sum.hpp)

Every node holds the sum of its values (`SInv`, `Proofs.Cpp.SegmentTreeBeatsMath`), and every operation keeps it
(`*_rec_S`, combined with the specifications of `Proofs.Cpp.SegmentTreeBeatsSumCore` by `triple_and`). The public
theorems are `init_specS`, `chmin_specS`, ..., `calc_sum_specS` on `ValidS`. -/
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The sum array as a function of the node index. -/
def viewS (st : cp.SegmentTreeBeatsSum) : Nat → Int := fun j => st.sum[j]!

theorem viewS_set (st : cp.SegmentTreeBeatsSum) (r : cp.SegmentTreeBeatsSum) (k : Int) (v : Int) (hk0 : 0 ≤ k)
    (hk : k.toNat < st.sum.size) (h : r.sum = Cpp.set st.sum k v) : viewS r = upF (viewS st) k.toNat v := by
  unfold viewS; rw [h]; exact getB_set' _ _ _ hk0 hk

theorem unm_sum (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_max st k x
    ⦃⇓ r c => ⌜viewS r = unmS (view st) (viewS st) k.toNat x⌝⦄ := by
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  mvcgen [cp.SegmentTreeBeatsSum.update_node_max]
  all_goals exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq]; rfl)

theorem unmin_sum (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_min st k x
    ⦃⇓ r c => ⌜viewS r = unminS (view st) (viewS st) k.toNat x⌝⦄ := by
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  mvcgen [cp.SegmentTreeBeatsSum.update_node_min]
  all_goals exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq]; rfl)

theorem addAll_sum (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_all st k x
    ⦃⇓ r c => ⌜viewS r = addS (view st) (viewS st) k.toNat x⌝⦄ := by
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  mvcgen [cp.SegmentTreeBeatsSum.add_all]
  all_goals exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq]; rfl)

theorem updAll_sum (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_all st k x
    ⦃⇓ r c => ⌜viewS r = updS (view st) (viewS st) k.toNat x⌝⦄ := by
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  mvcgen [cp.SegmentTreeBeatsSum.update_all]
  all_goals exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq]; rfl)

theorem upd_sum (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k) (hk : 2 * k.toNat + 2 < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update st k ⦃⇓ r c => ⌜viewS r = updSum (viewS st) k.toNat⌝⦄ := by
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  have ea : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
  have eb : (2 * k + 2).toNat = 2 * k.toNat + 2 := by omega
  mvcgen [cp.SegmentTreeBeatsSum.update]
  all_goals exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq, ea, eb]; rfl)

theorem triple_and {α : Type} {x : M α} {t0 : Nat} {P Q : α → Nat → Prop}
    (h1 : ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜P r c⌝⦄) (h2 : ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜Q r c⌝⦄) :
    ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜P r c ∧ Q r c⌝⦄ := by
  obtain ⟨r, c, hx, hp⟩ := run_of_triple h1
  obtain ⟨r', c', hx', hq⟩ := run_of_triple h2
  rw [hx] at hx'
  simp only [Option.some.injEq, Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  exact triple_of_run r c hx ⟨hp, hq⟩

theorem unm_both (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_max st k x
    ⦃⇓ r c => ⌜(view r = unm (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧
      r.n0 = st.n0 ∧ c = t0 + 1) ∧ viewS r = unmS (view st) (viewS st) k.toNat x⌝⦄ :=
  triple_and (unm_cpp st k x hk0 hk hsz t0) (unm_sum st k x hk0 hk hsz t0)

theorem unmin_both (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_node_min st k x
    ⦃⇓ r c => ⌜(view r = unmin (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧
      r.n0 = st.n0 ∧ c = t0 + 1) ∧ viewS r = unminS (view st) (viewS st) k.toNat x⌝⦄ :=
  triple_and (unmin_cpp st k x hk0 hk hsz t0) (unmin_sum st k x hk0 hk hsz t0)

theorem addAll_both (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_all st k x
    ⦃⇓ r c => ⌜(view r = addAll (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧
      r.n0 = st.n0 ∧ c = t0 + 1) ∧ viewS r = addS (view st) (viewS st) k.toNat x⌝⦄ :=
  triple_and (addAll_cpp st k x hk0 hk hsz t0) (addAll_sum st k x hk0 hk hsz t0)

theorem updAll_both (st : cp.SegmentTreeBeatsSum) (k x : Int) (hk0 : 0 ≤ k) (hk : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_all st k x
    ⦃⇓ r c => ⌜(view r = updAll (view st) k.toNat x ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧
      r.n0 = st.n0 ∧ c = t0 + 1) ∧ viewS r = updS (view st) (viewS st) k.toNat x⌝⦄ :=
  triple_and (updAll_cpp st k x hk0 hk hsz t0) (updAll_sum st k x hk0 hk hsz t0)

theorem viewS_set_ladd (a : cp.SegmentTreeBeatsSum) (k v : Int) :
    viewS ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, Cpp.set a.ladd k v,
      a.lval⟩ = viewS a := rfl
theorem viewS_set_lval (a : cp.SegmentTreeBeatsSum) (k v : Int) :
    viewS ⟨a.n, a.n0, a.max_v, a.smax_v, a.max_c, a.min_v, a.smin_v, a.min_c, a.sum, a.len, a.ladd,
      Cpp.set a.lval k v⟩ = viewS a := rfl

/-- `push(k)` on the sum array in the C++ order (`pushC` for the other arrays). -/
def pushSSC (s : BS) (sm : Nat → Int) (k : Nat) : Nat → Int :=
  if s.lv k ≠ INF then
    let s1 := updAll s (2 * k + 1) (s.lv k)
    updS s1 (updS s sm (2 * k + 1) (s.lv k)) (2 * k + 2) (s1.lv k)
  else
    let s3 := if s.la k ≠ 0 then
      let t := addAll s (2 * k + 1) (s.la k)
      setLa (addAll t (2 * k + 2) (t.la k)) k 0 else s
    let sm3 := if s.la k ≠ 0 then
      let t := addAll s (2 * k + 1) (s.la k)
      addS t (addS s sm (2 * k + 1) (s.la k)) (2 * k + 2) (t.la k) else sm
    capsS (caps s3 k (2 * k + 1)) (capsS s3 sm3 k (2 * k + 1)) k (2 * k + 2)

set_option maxHeartbeats 4000000 in
theorem push_sum (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < st.n0 - 1 → 2 * k.toNat + 2 < st.max_v.size) (hkN : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.push st k
    ⦃⇓ r c => ⌜k < st.n0 - 1 → viewS r = pushSSC (view st) (viewS st) k.toNat⌝⦄ := by
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
    intro h; omega
  have hk2 := hk (by omega)
  have hd : decide (st.n0 - 1 ≤ k) = false := by simp [hleaf]
  simp only [cp.SegmentTreeBeatsSum.push, hd, Bool.false_eq_true, ite_false]
  mvcgen -trivial [unm_both, unmin_both, addAll_both, updAll_both]
  all_goals try simp +zetaDelta only [st_eta, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *
  all_goals try simp only [get_eq, ea, eb, cinf, fold_mx, fold_mn, fold_la, fold_lv, ne_eq, hleaf, false_imp_iff,
    true_and] at *
  all_goals try casesm* _ ∧ _
  all_goals first
    | (show 0 ≤ _; omega)
    | (show _ < _; omega)
    | (show SzE _; first | assumption | (apply SzE_set_ladd; assumption) | (apply SzE_set_lval; assumption))
    | skip
  all_goals try simp (disch := first | assumption | omega) only [view_set_ladd', view_set_lval', viewS_set_ladd,
    viewS_set_lval] at *
  all_goals try simp only [*] at *
  all_goals intro _
  all_goals simp only [pushSSC, capsS, caps, *, ne_eq, not_false_eq_true, not_true_eq_false,
      ite_true, ite_false, setLa_mx, setLa_mn, not_not]

theorem pushSSC_eq (s : BS) (sm : Nat → Int) (k : Nat) : pushSSC s sm k = pushSS s sm k := by
  have na : k ≠ 2 * k + 1 := by omega
  simp only [pushSSC, pushSS, updAll_lv _ _ _ _ na, addAll_la _ _ _ _ na]


theorem pushSS_ne (s : BS) (sm : Nat → Int) (k j : Nat) (h1 : j ≠ 2 * k + 1) (h2 : j ≠ 2 * k + 2) :
    pushSS s sm k j = sm j := by
  unfold pushSS
  split_ifs
  · simp [updS, upF, h1, h2]
  · rw [capsS_ne _ _ _ _ _ h2, capsS_ne _ _ _ _ _ h1]; simp [addS, upF, h1, h2]
  · rw [capsS_ne _ _ _ _ _ h2, capsS_ne _ _ _ _ _ h1]

theorem inner_sinv (f : Int → Int) (a b : Int) (s s3 s4 : BS) (sm sm3 sm4 : Nat → Int) (n : Nat) (B B' : Int)
    (hB : B < INF) (hB' : B' < INF) (h k lo : Nat) (O : List Int) (hZ : Zs O) (hI : Inv s n (h + 1) k lo)
    (hS : Safe s n B (h + 1) k lo O) (hSI : SInv s sm n (h + 1) k lo)
    (h3 : RecPost f a b n B' h (2 * k + 1) lo (0 :: O) (push s k) s3)
    (h3s : SInv s3 sm3 n h (2 * k + 1) lo ∧ ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j → sm3 j = pushSS s sm k j)
    (h4 : RecPost f a b n B' h (2 * k + 2) (lo + 2 ^ h) (0 :: O) s3 s4)
    (h4s : SInv s4 sm4 n h (2 * k + 2) (lo + 2 ^ h) ∧
      ∀ j, ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j → sm4 j = sm3 j) :
    SInv (upd s4 k) (updSum sm4 k) n (h + 1) k lo ∧
      ∀ j, ¬ SegmentTreeBeatsMath.Sub (h + 1) k j → updSum sm4 k j = sm j := by
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
  have c1SI : SInv s4 sm4 n h (2 * k + 1) lo :=
    sinv_frame s3 s4 sm3 sm4 n h _ _ (fun j hj => ⟨a43 j hj, h4s.2 j (fun h2 => sub_siblings h k j hj h2)⟩) h3s.1
  refine ⟨upd_sinv s4 sm4 n h k lo c1SI h4s.1 uT, fun j hj => ?_⟩
  have j0 : j ≠ k := fun e => hj (e ▸ sub_self _ _)
  have j1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 1) j := fun e => hj (sub_child1 h k j e)
  have j2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k + 2) j := fun e => hj (sub_child2 h k j e)
  rw [show updSum sm4 k j = sm4 j from upF_ne _ _ _ _ j0, h4s.2 j j2, h3s.2 j j1]
  exact pushSS_ne s sm k j (fun e => j1 (e ▸ sub_self _ _)) (fun e => j2 (e ▸ sub_self _ _))

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- The sum array after a recursion at node `k`: the sums below `k` are right and nothing else changed. -/
def SPost (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (res : cp.SegmentTreeBeatsSum) : Prop :=
  SInv (view res) (viewS res) st.n.toNat h k.toNat l.toNat ∧
    ∀ j, ¬ SegmentTreeBeatsMath.Sub h k.toNat j → viewS res j = viewS st j

theorem childS1 (st t2 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat) (k l : Int) (hk0 : 0 ≤ k)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hSI : SInv (view st) (viewS st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hv : view t2 = push (view st) k.toNat) (hs : viewS t2 = pushSSC (view st) (viewS st) k.toNat) (hn : t2.n = st.n) :
    SInv (view t2) (viewS t2) t2.n.toNat h (2 * k + 1).toNat l.toNat := by
  rw [hv, hs, hn, toNat_2k1 k hk0, pushSSC_eq]
  exact (push_sinv _ _ _ B hB h _ _ [0] (by simp) hI hS hSI).1

theorem childS2 (f : Int → Int) (a b : Int) (st t2 t3 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hSI : SInv (view st) (viewS st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hv : view t2 = push (view st) k.toNat) (hs : viewS t2 = pushSSC (view st) (viewS st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost f a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hS3 : SPost h t2 (2 * k + 1) l t3) (hn3 : t3.n = t2.n) :
    SInv (view t3) (viewS t3) t3.n.toNat h (2 * k + 2).toNat m.toNat := by
  have P := (push_sinv _ _ _ B hB h _ _ [0] (by simp) hI hS hSI).2.1
  obtain ⟨-, hS3f⟩ := hS3
  rw [hn] at hR3
  rw [hn3, hn, toNat_2k2 k hk0, hm]
  rw [toNat_2k1 k hk0] at hR3 hS3f
  refine sinv_frame _ _ _ _ _ h _ _ (fun j hj => ⟨?_, ?_⟩) P
  · rw [← hv]; exact hR3.2.2.2 j (fun h1 => sub_siblings h _ j h1 hj)
  · rw [hS3f j (fun h1 => sub_siblings h _ j h1 hj), hs, pushSSC_eq]

theorem finishS (f : Int → Int) (a b : Int) (st t2 t3 t4 t5 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF)
    (h : Nat) (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hSI : SInv (view st) (viewS st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hv : view t2 = push (view st) k.toNat) (hs : viewS t2 = pushSSC (view st) (viewS st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost f a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hS3 : SPost h t2 (2 * k + 1) l t3) (hn3 : t3.n = t2.n)
    (hR4 : RecPost f a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4))
    (hS4 : SPost h t3 (2 * k + 2) m t4) (hn4 : t4.n = t3.n)
    (hv5 : view t5 = upd (view t4) k.toNat) (hs5 : viewS t5 = updSum (viewS t4) k.toNat) :
    SPost (h + 1) st k l t5 := by
  obtain ⟨S3, S3f⟩ := hS3
  obtain ⟨S4, S4f⟩ := hS4
  rw [hv, hn, toNat_2k1 k hk0] at hR3
  rw [hn, toNat_2k1 k hk0] at S3
  rw [toNat_2k1 k hk0] at S3f
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4
  rw [hn3, hn, toNat_2k2 k hk0, hm] at S4
  rw [toNat_2k2 k hk0] at S4f
  obtain ⟨X1, X2⟩ := inner_sinv f a b _ _ _ _ _ _ _ B B hB hB h _ _ [0] zs0 hI hS hSI
    ((recpost_zeros _ _ _ _ _ _ _ _ _ _).mp hR3)
    ⟨S3, fun j hj => by rw [S3f j hj, hs, pushSSC_eq]⟩
    ((recpost_zeros _ _ _ _ _ _ _ _ _ _).mp hR4) ⟨S4, S4f⟩
  unfold SPost
  rw [hv5, hs5]
  exact ⟨X1, X2⟩

theorem push_both (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < st.n0 - 1 → 2 * k.toNat + 2 < st.max_v.size) (hkN : k.toNat < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.push st k
    ⦃⇓ r c => ⌜((st.n0 - 1 ≤ k → r = st) ∧ (k < st.n0 - 1 → view r = push (view st) k.toNat) ∧
      (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧ r.n0 = st.n0 ∧ c ≤ t0 + 9) ∧
      (k < st.n0 - 1 → viewS r = pushSSC (view st) (viewS st) k.toNat)⌝⦄ :=
  triple_and (push_cpp st k hk0 hk hkN hsz t0) (push_sum st k hk0 hk hkN hsz t0)

theorem upd_both (st : cp.SegmentTreeBeatsSum) (k : Int) (hk0 : 0 ≤ k) (hk : 2 * k.toNat + 2 < st.max_v.size)
    (hsz : SzE st) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update st k
    ⦃⇓ r c => ⌜(view r = upd (view st) k.toNat ∧ (SzE r ∧ r.max_v.size = st.max_v.size) ∧ r.n = st.n ∧
      r.n0 = st.n0 ∧ c = t0 + 1) ∧ viewS r = updSum (viewS st) k.toNat⌝⦄ :=
  triple_and (upd_cpp st k hk0 hk hsz t0) (upd_sum st k hk0 hk hsz t0)

theorem chmin_skip_S (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (Cpp.get st.max_v k ≤ x)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_mx]; omega
  simp only [cp.SegmentTreeBeatsSum._chmin_rec, hd, ite_true, st_eta]
  mvcgen
  exact ⟨hSI, fun _ _ => rfl⟩

theorem chmin_cover_S (H : Nat) (x a b B : Int) (hB : B < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : ¬ (b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x))
    (c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hkb := pos_bound H h _ _ hP
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (Cpp.get st.max_v k ≤ x)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mx]; omega
  have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (Cpp.get st.smax_v k < x)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_sx]; omega
  simp only [cp.SegmentTreeBeatsSum._chmin_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [unm_both]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨⟨hv, -, hnn, -, -⟩, hs⟩ := hpost
    have h2 : x < (view st).mx k.toNat := by omega
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hv, hs]
      exact unm_sinv _ _ _ B hB h _ _ [0] (by simp) hI hS hSI x c2.2.2 h2
    · rw [hs]; exact upF_ne _ _ _ _ (fun e => hj (e ▸ sub_self _ _))

theorem chmin_rec_S (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x
    · exact chmin_skip_S H x a b B 0 f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x
    · exact chmin_cover_S H x a b B hB 0 f st k l r t0 hpre hSI c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, hP, -, hI, -⟩ := hpre
    have := leaf_sx _ _ _ _ hI (by omega)
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ (view st).mx k.toNat ≤ x
    · exact chmin_skip_S H x a b B (h + 1) f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ (view st).sx k.toNat < x
    · exact chmin_cover_S H x a b B hB (h + 1) f st k l r t0 hpre hSI c1 c2
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
        SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmin_rec fuel st x a b k l r
        ⦃⇓ res c => ⌜ChminPost H x a b B h st k l t0 res c ∧ SPost h st k l res⌝⦄ :=
      fun fuel st k l r t0 hf hp hs =>
        triple_and (chmin_rec_spec H x a b B hB hx hx1 hx2 h fuel st k l r t0 hf hp) (ih fuel st k l r t0 hf hp hs)
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
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ihc, push_both, upd_both]
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 (min · x) a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact finishS (min · x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)

theorem chmax_skip_S (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (x ≤ Cpp.get st.min_v k)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_mn]; omega
  simp only [cp.SegmentTreeBeatsSum._chmax_rec, hd, ite_true, st_eta]
  mvcgen
  exact ⟨hSI, fun _ _ => rfl⟩

theorem chmax_cover_S (H : Nat) (x a b B : Int) (hB : B < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : ¬ (b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat))
    (c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hkb := pos_bound H h _ _ hP
  have hd : ((decide (b ≤ l) || decide (r ≤ a)) || decide (x ≤ Cpp.get st.min_v k)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; simp only [get_eq, fold_mn]; omega
  have hd2 : ((decide (a ≤ l) && decide (r ≤ b)) && decide (x < Cpp.get st.smin_v k)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; simp only [get_eq, fold_sn]; omega
  simp only [cp.SegmentTreeBeatsSum._chmax_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [unmin_both]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨⟨hv, -, hnn, -, -⟩, hs⟩ := hpost
    have h2 : (view st).mn k.toNat < x := by omega
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hv, hs]
      exact unmin_sinv _ _ _ B hB h _ _ [0] (by simp) hI hS hSI x h2 c2.2.2
    · rw [hs]; exact upF_ne _ _ _ _ (fun e => hj (e ▸ sub_self _ _))

theorem chmax_rec_S (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat
    · exact chmax_skip_S H x a b B 0 f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat
    · exact chmax_cover_S H x a b B hB 0 f st k l r t0 hpre hSI c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, hP, -, hI, -⟩ := hpre
    have := leaf_sn _ _ _ _ hI (by omega)
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a ∨ x ≤ (view st).mn k.toNat
    · exact chmax_skip_S H x a b B (h + 1) f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b ∧ x < (view st).sn k.toNat
    · exact chmax_cover_S H x a b B hB (h + 1) f st k l r t0 hpre hSI c1 c2
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
        SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._chmax_rec fuel st x a b k l r
        ⦃⇓ res c => ⌜ChmaxPost H x a b B h st k l t0 res c ∧ SPost h st k l res⌝⦄ :=
      fun fuel st k l r t0 hf hp hs =>
        triple_and (chmax_rec_spec H x a b B hB hx hx1 hx2 h fuel st k l r t0 hf hp) (ih fuel st k l r t0 hf hp hs)
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
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ihc, push_both, upd_both]
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 (max · x) a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact finishS (max · x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)

theorem updval_skip_S (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._update_val_rec, hd, ite_true, st_eta]
  mvcgen
  exact ⟨hSI, fun _ _ => rfl⟩

theorem updval_cover_S (H : Nat) (x a b B : Int) (hB : B < INF) (hx1 : -INF < x) (hx2 : x < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat) (hbn : b ≤ st.n)
    (c1 : ¬ (b ≤ l ∨ r ≤ a))
    (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hkb := pos_bound H h _ _ hP
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._update_val_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [updAll_both]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨⟨hv, -, hnn, -, -⟩, hs⟩ := hpost
    have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hv, hs]
      exact updAll_sinv _ _ _ h _ _ hI hSI (by omega) x ⟨hx1, hx2⟩
    · rw [hs]; exact upF_ne _ _ _ _ (fun e => hj (e ▸ sub_self _ _))

theorem updval_rec_S (H : Nat) (x a b B : Int) (hB : B < INF) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r → b ≤ st.n →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hbn hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact updval_skip_S H x a b B 0 f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact updval_cover_S H x a b B hB hx1 hx2 0 f st k l r t0 hpre hSI hbn c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hbn hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact updval_skip_S H x a b B (h + 1) f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact updval_cover_S H x a b B hB hx1 hx2 (h + 1) f st k l r t0 hpre hSI hbn c1 c2
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
        b ≤ st.n → SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._update_val_rec fuel st x a b k l r
        ⦃⇓ res c => ⌜OpPost H (fun _ => x) a b B h st k l t0 res c ∧ SPost h st k l res⌝⦄ :=
      fun fuel st k l r t0 hf hp hb hs =>
        triple_and (updval_rec_spec H x a b B hB hx hx1 hx2 h fuel st k l r t0 hf hp hb) (ih fuel st k l r t0 hf hp hb hs)
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
    have hpos : (0 : Int) ≤ 2 ^ h := by positivity
    have hm : (Cpp.div (l + r) 2).toNat = l.toNat + 2 ^ h := by rw [hdiv]; exact toNat_add_pow l h hl0
    clear hd hd2 c1 c2
    mvcgen [ihc, push_both, upd_both]
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 (fun _ => x) a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact finishS (fun _ => x) a b st _ _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)

theorem addval_skip_S (H : Nat) (x a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : AddPre H B x h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._add_val_rec, hd, ite_true, st_eta]
  mvcgen
  exact ⟨hSI, fun _ _ => rfl⟩

theorem addval_cover_S (H : Nat) (x a b B : Int) (hB : B < INF) (h f : Nat)
    (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : AddPre H B x h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat) (hbn : b ≤ st.n)
    (c1 : ¬ (b ≤ l ∨ r ≤ a))
    (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec (f + 1) st x a b k l r
    ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hkb := pos_bound H h _ _ hP
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._add_val_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen [addAll_both]
  · omega
  · rename_i s1 hs1 res c hpost
    obtain ⟨⟨hv, -, hnn, -, -⟩, hs⟩ := hpost
    have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hv, hs]
      exact addAll_sinv _ _ _ B hB h _ _ [0, x] (by simp) hI hS hSI (by omega) x (by simp)
    · rw [hs]; exact upF_ne _ _ _ _ (fun e => hj (e ▸ sub_self _ _))

theorem addval_rec_S (H : Nat) (x a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → AddPre H B x h st k l r → b ≤ st.n →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec fuel st x a b k l r
      ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hbn hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact addval_skip_S H x a b B 0 f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact addval_cover_S H x a b B hB 0 f st k l r t0 hpre hSI hbn c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hbn hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact addval_skip_S H x a b B (h + 1) f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact addval_cover_S H x a b B hB (h + 1) f st k l r t0 hpre hSI hbn c1 c2
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → AddPre H B x h st k l r →
        b ≤ st.n → SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._add_val_rec fuel st x a b k l r
        ⦃⇓ res c => ⌜OpPost H (· + x) a b B h st k l t0 res c ∧ SPost h st k l res⌝⦄ :=
      fun fuel st k l r t0 hf hp hb hs =>
        triple_and (addval_rec_spec H x a b B hB h fuel st k l r t0 hf hp hb) (ih fuel st k l r t0 hf hp hb hs)
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
    mvcgen [ihc, push_both, upd_both]
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
      | exact childS1 st _ B hB h k l hk0 hI (safe_x0 _ _ _ _ _ _ _ hS) hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 (· + x) a b st _ _ B hB h k l _ hk0 hm hI (safe_x0 _ _ _ _ _ _ _ hS) hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact finishS (· + x) a b st _ _ _ _ B hB h k l _ hk0 hm hI (safe_x0 _ _ _ _ _ _ _ hS) hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)

theorem qfinishS (a b : Int) (st t2 t3 t4 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF)
    (h : Nat) (k l m : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hSI : SInv (view st) (viewS st) st.n.toNat (h + 1) k.toNat l.toNat)
    (hv : view t2 = push (view st) k.toNat) (hs : viewS t2 = pushSSC (view st) (viewS st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost id a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hS3 : SPost h t2 (2 * k + 1) l t3) (hn3 : t3.n = t2.n)
    (hR4 : RecPost id a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4))
    (hS4 : SPost h t3 (2 * k + 2) m t4) :
    SPost (h + 1) st k l t4 := by
  obtain ⟨S3, S3f⟩ := hS3
  obtain ⟨S4, S4f⟩ := hS4
  rw [hv, hn, toNat_2k1 k hk0] at hR3
  rw [hn, toNat_2k1 k hk0] at S3
  rw [toNat_2k1 k hk0] at S3f
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4
  rw [hn3, hn, toNat_2k2 k hk0, hm] at S4
  rw [toNat_2k2 k hk0] at S4f
  have hR4' := hR4
  obtain ⟨hR, -⟩ := query_inner _ _ _ _ B hB h _ _ hI hS hR3 hR4
  have hTk : T (view t4) st.n.toNat (h + 1) k.toNat l.toNat = T (view st) st.n.toNat (h + 1) k.toNat l.toNat := by
    rw [hR.2.2.1, opL_id]
  have fr : ∀ j, j ≠ 2 * k.toNat + 1 → j ≠ 2 * k.toNat + 2 → ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 1) j →
      ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 2) j → viewS t4 j = viewS st j := by
    intro j h1 h2 h3 h4
    rw [S4f j h4, S3f j h3, hs, pushSSC_eq, pushSS_ne _ _ _ _ h1 h2]
  have nk1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 1) k.toNat := fun e => notsub_k h _ _ (Or.inl e) rfl
  have nk2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 2) k.toNat := fun e => notsub_k h _ _ (Or.inr e) rfl
  refine ⟨⟨sinv_frame _ _ _ _ _ h _ _ (fun j hj => ⟨hR4'.2.2.2 j (fun h2 => sub_siblings h _ j hj h2),
      S4f j (fun h2 => sub_siblings h _ j hj h2)⟩) S3, S4, ?_⟩, fun j hj => ?_⟩
  · rw [hTk, fr _ (by omega) (by omega) nk1 nk2]; exact sinv_top _ _ _ _ _ _ hSI
  · exact fr j (fun e => hj (by rw [e]; exact sub_child1 h _ _ (sub_self _ _)))
      (fun e => hj (by rw [e]; exact sub_child2 h _ _ (sub_self _ _)))
      (fun e => hj (sub_child1 h _ j e)) (fun e => hj (sub_child2 h _ j e))

theorem qS_ret_max (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (hc : (b ≤ l ∨ r ≤ a) ∨ (¬ (b ≤ l ∨ r ≤ a) ∧ (a ≤ l ∧ r ≤ b))) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜SPost h st k l p.2⌝⦄ := by
  rcases hc with c1 | ⟨c1, c2⟩
  · have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_max_rec, hd, ite_true, st_eta]
    mvcgen
    exact ⟨hSI, fun _ _ => rfl⟩
  · have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_max_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
    mvcgen
    exact ⟨hSI, fun _ _ => rfl⟩

theorem qS_ret_min (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat)
    (hc : (b ≤ l ∨ r ≤ a) ∨ (¬ (b ≤ l ∨ r ≤ a) ∧ (a ≤ l ∧ r ≤ b))) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜SPost h st k l p.2⌝⦄ := by
  rcases hc with c1 | ⟨c1, c2⟩
  · have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_min_rec, hd, ite_true, st_eta]
    mvcgen
    exact ⟨hSI, fun _ _ => rfl⟩
  · have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_min_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
    mvcgen
    exact ⟨hSI, fun _ _ => rfl⟩

theorem qmax_rec_S (H : Nat) (a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec fuel st a b k l r
      ⦃⇓ p c => ⌜SPost h st k l p.2⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qS_ret_max a b B 0 f st k l r t0 hSI (Or.inl c1)
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qS_ret_max a b B 0 f st k l r t0 hSI (Or.inr ⟨c1, c2⟩)
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qS_ret_max a b B (h + 1) f st k l r t0 hSI (Or.inl c1)
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qS_ret_max a b B (h + 1) f st k l r t0 hSI (Or.inr ⟨c1, c2⟩)
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
        SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_max_rec fuel st a b k l r
        ⦃⇓ p c => ⌜QPost H a b B h st k l t0 p.1 p.2 c ∧ SPost h st k l p.2⌝⦄ :=
      fun fuel st k l r t0 hf hp hs =>
        triple_and (qmax_rec_spec H a b B hB h fuel st k l r t0 hf hp) (ih fuel st k l r t0 hf hp hs)
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
    mvcgen [ihc, push_both]
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 id a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact qfinishS a b st _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)

theorem qmin_rec_S (H : Nat) (a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec fuel st a b k l r
      ⦃⇓ p c => ⌜SPost h st k l p.2⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qS_ret_min a b B 0 f st k l r t0 hSI (Or.inl c1)
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qS_ret_min a b B 0 f st k l r t0 hSI (Or.inr ⟨c1, c2⟩)
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qS_ret_min a b B (h + 1) f st k l r t0 hSI (Or.inl c1)
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qS_ret_min a b B (h + 1) f st k l r t0 hSI (Or.inr ⟨c1, c2⟩)
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
        SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_min_rec fuel st a b k l r
        ⦃⇓ p c => ⌜QPostMin H a b B h st k l t0 p.1 p.2 c ∧ SPost h st k l p.2⌝⦄ :=
      fun fuel st k l r t0 hf hp hs =>
        triple_and (qmin_rec_spec H a b B hB h fuel st k l r t0 hf hp) (ih fuel st k l r t0 hf hp hs)
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
    mvcgen [ihc, push_both]
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 id a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    exact qfinishS a b st _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)


theorem sum_maskL_disjoint (a b : Int) (lo : Nat) (L : List Int) (h : b ≤ lo ∨ lo + L.length ≤ a) :
    (maskL 0 a b lo L).sum = 0 := by
  have hc := maskL_const 0 a b lo L h
  generalize maskL 0 a b lo L = M at hc ⊢
  induction M with
  | nil => rfl
  | cons x t ih =>
    simp only [List.sum_cons]
    rw [hc x List.mem_cons_self, ih (fun v hv => hc v (List.mem_cons_of_mem _ hv))]; rfl
/-- The postcondition of `_calc_sum` at node `k`: the answer and an unchanged sequence. -/
def QSumPost (H : Nat) (a b B : Int) (h : Nat) (st : cp.SegmentTreeBeatsSum) (k l : Int) (t0 : Nat) (q : Int)
    (res : cp.SegmentTreeBeatsSum) (c : Nat) : Prop :=
  RecPost id a b st.n.toNat B h k.toNat l.toNat [0] (view st) (view res) ∧
    q = List.sum (maskL 0 a b l.toNat (T (view st) st.n.toNat h k.toNat l.toNat)) ∧
    Shape res H ∧ res.max_v.size = st.max_v.size ∧ res.n = st.n ∧ c + 12 ≤ t0 + 12 * 2 ^ (h + 1) ∧
    SPost h st k l res

theorem qsum_skip_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat) (c1 : b ≤ l ∨ r ≤ a) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_sum_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QSumPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_sum_rec, hd, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)),
    (sum_maskL_disjoint a b _ _ (by omega)).symm, ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega, hSI, fun _ _ => rfl⟩

theorem qsum_cover_cpp (H : Nat) (a b B : Int) (h f : Nat) (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat)
    (hpre : ChminPre H B h st k l r) (hSI : SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat) (c1 : ¬ (b ≤ l ∨ r ≤ a)) (c2 : a ≤ l ∧ r ≤ b) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_sum_rec (f + 1) st a b k l r
    ⦃⇓ p c => ⌜QSumPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
  have hr' : r = ((l.toNat + 2 ^ h : Nat) : Int) := by rw [hr]; push_cast; omega
  have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [cp.SegmentTreeBeatsSum._calc_sum_rec, hd, hd2, Bool.false_eq_true, ite_false, ite_true, st_eta]
  mvcgen
  rename_i c hc
  have hlen := len_T_le (view st) st.n.toNat h k.toNat l.toNat
  have := two_le_pow h
  refine ⟨rec_skip _ a b _ _ B B le_rfl _ _ _ [0] hI hS (opL_fix _ a b _ _ (fun _ _ => rfl)), ?_,
    ⟨hsz, hn0, hsize, hn⟩, rfl, rfl, by omega, hSI, fun _ _ => rfl⟩
  rw [maskL_all _ a b _ _ (by omega) (by omega), ← sinv_top _ _ _ _ _ _ hSI]
  rfl

theorem qsum_finish (a b : Int) (st t2 t3 t4 : cp.SegmentTreeBeatsSum) (B : Int) (hB : B < INF) (h : Nat)
    (k l m : Int) (q1 q2 : Int) (hk0 : 0 ≤ k) (hm : m.toNat = l.toNat + 2 ^ h)
    (hI : Inv (view st) st.n.toNat (h + 1) k.toNat l.toNat) (hS : Safe (view st) st.n.toNat B (h + 1) k.toNat l.toNat [0])
    (hv : view t2 = push (view st) k.toNat) (hn : t2.n = st.n)
    (hR3 : RecPost id a b t2.n.toNat B h (2 * k + 1).toNat l.toNat [0] (view t2) (view t3))
    (hq1 : q1 = List.sum (maskL 0 a b l.toNat (T (view t2) t2.n.toNat h (2 * k + 1).toNat l.toNat)))
    (hn3 : t3.n = t2.n)
    (hR4 : RecPost id a b t3.n.toNat B h (2 * k + 2).toNat m.toNat [0] (view t3) (view t4))
    (hq2 : q2 = List.sum (maskL 0 a b m.toNat (T (view t3) t3.n.toNat h (2 * k + 2).toNat m.toNat))) :
    RecPost id a b st.n.toNat B (h + 1) k.toNat l.toNat [0] (view st) (view t4) ∧
      q1 + q2 = List.sum (maskL 0 a b l.toNat (T (view st) st.n.toNat (h + 1) k.toNat l.toNat)) := by
  rw [hv, hn, toNat_2k1 k hk0] at hR3 hq1
  rw [hn3, hn, toNat_2k2 k hk0, hm] at hR4 hq2
  obtain ⟨hR, hsplit⟩ := query_inner _ _ _ _ B hB h _ _ hI hS hR3 hR4
  refine ⟨hR, ?_⟩
  rw [hsplit, maskL_append' _ a b _ (2 ^ h), List.sum_append, hq1, hq2]
  simp only [T_length]
  by_cases hn' : 2 ^ h ≤ st.n.toNat - l.toNat
  · left; omega
  · right; apply List.eq_nil_of_length_eq_zero; rw [T_length]; omega


theorem qsum_rec_spec (H : Nat) (a b B : Int) (hB : B < INF) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → ChminPre H B h st k l r →
      SInv (view st) (viewS st) st.n.toNat h k.toNat l.toNat →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._calc_sum_rec fuel st a b k l r
      ⦃⇓ p c => ⌜QSumPost H a b B h st k l t0 p.1 p.2 c⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qsum_skip_cpp H a b B 0 f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qsum_cover_cpp H a b B 0 f st k l r t0 hpre hSI c1 c2
    exfalso
    obtain ⟨hk0, hl0, hr, -⟩ := hpre
    simp at hr
    omega
  | succ h ih =>
    intro fuel st k l r t0 hf hpre hSI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases c1 : b ≤ l ∨ r ≤ a
    · exact qsum_skip_cpp H a b B (h + 1) f st k l r t0 hpre hSI c1
    by_cases c2 : a ≤ l ∧ r ≤ b
    · exact qsum_cover_cpp H a b B (h + 1) f st k l r t0 hpre hSI c1 c2
    obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hI, hS⟩ := hpre
    have hin := pos_inner H h _ _ hP
    have e2 : ((2 ^ H : Nat) : Int) = 2 ^ H := by push_cast; rfl
    have hd : (decide (b ≤ l) || decide (r ≤ a)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hd2 : (decide (a ≤ l) && decide (r ≤ b)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [cp.SegmentTreeBeatsSum._calc_sum_rec, hd, hd2, Bool.false_eq_true, ite_false, st_eta]
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
    mvcgen [ih, push_both]
    all_goals try (show ChminPre _ _ _ _ _ _ _; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try unfold QSumPost at *
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
      | exact childS1 st _ B hB h k l hk0 hI hS hSI (by assumption) (by assumption) (by assumption)
      | exact childS2 id a b st _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | skip
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
    have hp1 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    obtain ⟨hA, hQ⟩ := qsum_finish a b st _ _ _ B hB h k l _ _ _ hk0 hm hI hS (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    exact ⟨hA, hQ, ⟨by assumption, by omega, by omega, by omega⟩, by omega, by omega, by omega,
      qfinishS a b st _ _ _ B hB h k l _ hk0 hm hI hS hSI (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)⟩

theorem triple_imp {α : Type} {x : M α} {t0 : Nat} {P Q : α → Nat → Prop}
    (h : ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜P r c⌝⦄) (hPQ : ∀ r c, P r c → Q r c) :
    ⦃fun c => ⌜c = t0⌝⦄ x ⦃⇓ r c => ⌜Q r c⌝⦄ := by
  obtain ⟨r, c, hx, hp⟩ := run_of_triple h
  exact triple_of_run r c hx (hPQ r c hp)

theorem leaf_sum_cpp (H : Nat) (B : Int) (a : Array Int) (f : Nat) (st : cp.SegmentTreeBeatsSum)
    (k l r : Int) (t0 : Nat) (hpre : BuildPre H B a 0 st k l r) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build_rec (f + 1) st a k l r
    ⦃⇓ res c => ⌜viewS res = upF (viewS st) k.toNat (if l.toNat < st.n.toNat then a[l.toNat]! else 0)⌝⦄ := by
  obtain ⟨hk0, hl0, hr, hP, ⟨hsz, hn0, hsize, hn⟩, hA⟩ := hpre
  have hkb := pos_bound H 0 _ _ hP
  have hd : decide (r - l = 1) = true := by simp [hr]
  have y : k.toNat < st.sum.size := by have := hsz.2.2.2.2.2.2.2.2.2; omega
  by_cases hl : l < st.n
  · have hd2 : decide (l < st.n) = true := by simp [hl]
    simp only [cp.SegmentTreeBeatsSum._build_rec, hd, hd2, ite_true]
    mvcgen
    rw [if_pos (by omega)]
    exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq])
  · have hd2 : decide (l < st.n) = false := by simp [hl]
    simp only [cp.SegmentTreeBeatsSum._build_rec, hd, hd2, ite_true, Bool.false_eq_true, ite_false]
    mvcgen
    rw [if_neg (by omega)]
    exact viewS_set _ _ _ _ hk0 y (by simp +zetaDelta [get_eq])

theorem buildS_finish (a : Array Int) (B : Int) (hB : B < INF) (h : Nat) (st t1 t2 t3 : cp.SegmentTreeBeatsSum)
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
    (hv3 : view t3 = upd (view t2) k.toNat)
    (hS1 : SPost h (preBuild st k l r) (2 * k + 1) l t1) (hS2 : SPost h t1 (2 * k + 2) m t2)
    (hs3 : viewS t3 = updSum (viewS t2) k.toNat) :
    SPost (h + 1) st k l t3 := by
  obtain ⟨s1, f1⟩ := hS1
  obtain ⟨s2, f2⟩ := hS2
  simp only [preBuild_n] at s1
  have B3 := (build_finish a B hB h st t1 t2 t3 k l r m hk0 hr hm hsz hk hA h1I h1S h1T h1A hn1 h2I h2S h2T h2A
    hv3).2.2.1
  rw [toNat_2k1 k hk0] at h1T h1A s1 f1
  rw [toNat_2k2 k hk0, hm, hn1] at h2T s2
  rw [toNat_2k2 k hk0] at h2A f2
  have c1T : T (view t2) st.n.toNat h (2 * k.toNat + 1) l.toNat = leafL a st.n.toNat l.toNat h := by
    rw [← T_frame _ _ _ h _ _ (fun j hj => h2A j (fun h2 => sub_siblings h _ j hj h2)), h1T]
  have c1S : SInv (view t2) (viewS t2) st.n.toNat h (2 * k.toNat + 1) l.toNat :=
    sinv_frame _ _ _ _ _ h _ _ (fun j hj => ⟨h2A j (fun h2 => sub_siblings h _ j hj h2),
      f2 j (fun h2 => sub_siblings h _ j hj h2)⟩) s1
  have uT : T (upd (view t2) k.toNat) st.n.toNat (h + 1) k.toNat l.toNat =
      T (view t2) st.n.toNat h (2 * k.toNat + 1) l.toNat ++ T (view t2) st.n.toNat h (2 * k.toNat + 2) (l.toNat + 2 ^ h) := by
    rw [← hv3, B3, c1T, h2T, leafL_succ]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hv3, hs3]; exact upd_sinv _ _ _ h _ _ c1S s2 uT
  · have j0 : j ≠ k.toNat := fun e => hj (e ▸ sub_self _ _)
    have j1 : ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 1) j := fun e => hj (sub_child1 h _ j e)
    have j2 : ¬ SegmentTreeBeatsMath.Sub h (2 * k.toNat + 2) j := fun e => hj (sub_child2 h _ j e)
    rw [hs3, show updSum (viewS t2) k.toNat j = viewS t2 j from upF_ne _ _ _ _ j0, f2 j j2, f1 j j1]
    rfl

theorem build_rec_S (H : Nat) (B : Int) (hB : B < INF) (a : Array Int) :
    ∀ h fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → BuildPre H B a h st k l r →
      ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build_rec fuel st a k l r
      ⦃⇓ res c => ⌜SPost h st k l res⌝⦄ := by
  intro h
  induction h with
  | zero =>
    intro fuel st k l r t0 hf hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hc := triple_and (build_leaf_cpp H B hB a f st k l r t0 hpre) (leaf_sum_cpp H B a f st k l r t0 hpre)
    refine triple_imp hc (fun res c hrc => ?_)
    obtain ⟨⟨-, -, hT, -⟩, hs⟩ := hrc
    · refine ⟨?_, fun j hj => ?_⟩
      · show viewS res k.toNat = _
        rw [hT, hs, upF_eq]
        unfold leafL
        by_cases hl : l.toNat < st.n.toNat
        · simp [hl, show min 1 (st.n.toNat - l.toNat) = 1 by omega]
        · simp [hl, show st.n.toNat - l.toNat = 0 by omega]
      · rw [hs]; exact upF_ne _ _ _ _ (fun e => hj (by simp [SegmentTreeBeatsMath.Sub, e]))
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
    have ihc : ∀ fuel (st : cp.SegmentTreeBeatsSum) (k l r : Int) (t0 : Nat), h < fuel → BuildPre H B a h st k l r →
        ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build_rec fuel st a k l r
        ⦃⇓ res c => ⌜BuildPost H B a h st k l t0 res c ∧ SPost h st k l res⌝⦄ :=
      fun fuel st k l r t0 hf hp => triple_and (build_rec_spec H B hB a h fuel st k l r t0 hf hp) (ih fuel st k l r t0 hf hp)
    mvcgen [ihc, upd_both]
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
    exact buildS_finish a B hB h st _ _ _ k l r _ hk0 hrl hm hsz hkb hA (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)

end Proofs.Cpp.SegmentTreeBeatsSum
namespace Proofs.Cpp.SegmentTreeBeatsSum
open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SegmentTreeBeatsMath

/-- Every node holds the sum of its values (`sum[k]`), for the height `H` of the tree. -/
def SumOK (st : cp.SegmentTreeBeatsSum) : Prop :=
  ∀ H : Nat, st.n0 = 2 ^ H → SInv (view st) (viewS st) st.n.toNat H 0 0

theorem pow_two_inj (H H' : Nat) (h : (2 : Int) ^ H = 2 ^ H') : H = H' := by
  have : (2 : Nat) ^ H = 2 ^ H' := by exact_mod_cast h
  exact Nat.pow_right_injective (le_refl 2) this

theorem sumok_of (res st : cp.SegmentTreeBeatsSum) (H : Nat)
    (hS : SInv (view res) (viewS res) st.n.toNat H (0 : Int).toNat (0 : Int).toNat) (hn0 : res.n0 = 2 ^ H)
    (hn : res.n = st.n) : SumOK res := by
  intro H' h'
  have := pow_two_inj H H' (hn0.symm.trans h')
  subst this
  rw [hn]; exact hS

theorem build_both (B : Int) (hB : B < INF) (a : Array Int) (st : cp.SegmentTreeBeatsSum) (r : Int) (t0 : Nat)
    (hH : r.toNat.log2 < Cpp.fuel) (hpre : BuildPre r.toNat.log2 B a r.toNat.log2 st 0 0 r) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum._build st a 0 0 r
    ⦃⇓ res c => ⌜BuildPost r.toNat.log2 B a r.toNat.log2 st 0 0 t0 res c ∧ SPost r.toNat.log2 st 0 0 res⌝⦄ :=
  triple_and (build_spec B hB a st r t0 hH hpre) (build_rec_S _ B hB a _ _ st 0 0 r t0 hH hpre)

theorem init_sum (a : Array Int) (B : Int) (hB : B < INF) (hA : Bnd a a.size B) (h1 : 1 ≤ a.size)
    (h2 : a.size ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.init a
    ⦃⇓ r c => ⌜SumOK r⌝⦄ := by
  have bs := build_both B hB a
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
    obtain ⟨⟨-, -, -, -, pSh, -, pn, -⟩, hSP⟩ := hpost
    simp +zetaDelta only [st_eta]
    exact sumok_of res _ _ hSP.1 pSh.2.1 pn


theorem chmin_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmin st a b x ⦃⇓ r c => ⌜SumOK r⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => triple_and (chmin_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre)
    (chmin_rec_S H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.chmin, cp.SegmentTreeBeatsSum._chmin, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res st H hSP.1 hSh.2.1 hnn

theorem chmax_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmax st a b x ⦃⇓ r c => ⌜SumOK r⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => triple_and (chmax_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre)
    (chmax_rec_S H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.chmax, cp.SegmentTreeBeatsSum._chmax, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res st H hSP.1 hSh.2.1 hnn

theorem update_val_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b x : Int) (hb : b ≤ vals.length) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_val st a b x ⦃⇓ r c => ⌜SumOK r⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => triple_and (updval_rec_spec H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre (by omega))
    (updval_rec_S H x a b B hB hx hx1 hx2 H Cpp.fuel st 0 0 st.n0 t0 hH hpre (by omega) (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.update_val, cp.SegmentTreeBeatsSum._update_val, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res st H hSP.1 hSh.2.1 hnn

theorem add_val_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b x : Int) (hb : b ≤ vals.length) (hBx : B + |x| < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_val st a b x ⦃⇓ r c => ⌜SumOK r⌝⦄ := by
  obtain ⟨H, hH, hB, hn, ⟨p1, p2, p3, p4, p5, p6, p7⟩, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have hS' : Safe (view st) st.n.toNat (B + |x|) H (0 : Int).toNat (0 : Int).toNat [0, x] :=
    safe_mono _ _ _ H _ _ _ _ (by simp) (safe_shift _ _ B x H _ _ [0] p7)
  have sp := fun t0 => triple_and (addval_rec_spec H x a b (B + |x|) hBx H Cpp.fuel st 0 0 st.n0 t0 hH
      ⟨p1, p2, p3, p4, p5, p6, hS'⟩ (by omega))
    (addval_rec_S H x a b (B + |x|) hBx H Cpp.fuel st 0 0 st.n0 t0 hH ⟨p1, p2, p3, p4, p5, p6, hS'⟩ (by omega)
      (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.add_val, cp.SegmentTreeBeatsSum._add_val, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res st H hSP.1 hSh.2.1 hnn

theorem calc_max_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_max st a b ⦃⇓ r c => ⌜SumOK r.2⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => triple_and (qmax_rec_spec H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre)
    (qmax_rec_S H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.calc_max, cp.SegmentTreeBeatsSum._calc_max, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hq, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res.2 st H hSP.1 hSh.2.1 hnn

theorem calc_min_sum (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : Valid st vals B) (hS : SumOK st)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_min st a b ⦃⇓ r c => ⌜SumOK r.2⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv
  have sp := fun t0 => triple_and (qmin_rec_spec H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre)
    (qmin_rec_S H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre (hS H hn0))
  simp only [cp.SegmentTreeBeatsSum.calc_min, cp.SegmentTreeBeatsSum._calc_min, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨⟨hR, hq, hSh, -, hnn, hc2⟩, hSP⟩ := hpost
  exact sumok_of res.2 st H hSP.1 hSh.2.1 hnn

/-- The object holds `vals` with values bounded by `B`, and every node holds the sum of its values. -/
def ValidS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) : Prop := Valid st vals B ∧ SumOK st

/-- The constructor: the tree of `a` with correct sums, in `O(n)` steps. -/
theorem init_specS (a : Array Int) (B : Int) (hB : B < INF) (hA : Bnd a a.size B) (h1 : 1 ≤ a.size)
    (h2 : a.size ≤ 2 ^ 29) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.init a
    ⦃⇓ r c => ⌜ValidS r a.toList B ∧ c ≤ t0 + 50 * a.size + 10⌝⦄ :=
  triple_imp (triple_and (init_spec a B hB hA h1 h2 t0) (init_sum a B hB hA h1 h2 t0))
    (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

theorem chmin_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmin st a b x
    ⦃⇓ r c => ⌜ValidS r (opL (min · x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (chmin_spec st vals B hv.1 a b x hx hx1 hx2 t0)
    (chmin_sum st vals B hv.1 hv.2 a b x hx hx1 hx2 t0)) (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

theorem chmax_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b x : Int) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.chmax st a b x
    ⦃⇓ r c => ⌜ValidS r (opL (max · x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (chmax_spec st vals B hv.1 a b x hx hx1 hx2 t0)
    (chmax_sum st vals B hv.1 hv.2 a b x hx hx1 hx2 t0)) (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

theorem update_val_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b x : Int) (hb : b ≤ vals.length) (hx : |x| ≤ B) (hx1 : -INF < x) (hx2 : x < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.update_val st a b x
    ⦃⇓ r c => ⌜ValidS r (opL (fun _ => x) a b 0 vals) B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (update_val_spec st vals B hv.1 a b x hb hx hx1 hx2 t0)
    (update_val_sum st vals B hv.1 hv.2 a b x hb hx hx1 hx2 t0)) (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

theorem add_val_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b x : Int) (hb : b ≤ vals.length) (hBx : B + |x| < INF) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.add_val st a b x
    ⦃⇓ r c => ⌜ValidS r (opL (· + x) a b 0 vals) (B + |x|) ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (add_val_spec st vals B hv.1 a b x hb hBx t0)
    (add_val_sum st vals B hv.1 hv.2 a b x hb hBx t0)) (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

theorem calc_max_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_max st a b
    ⦃⇓ r c => ⌜r.1 = lmax (maskL (-INF) a b 0 vals) ∧ ValidS r.2 vals B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (calc_max_spec st vals B hv.1 a b t0) (calc_max_sum st vals B hv.1 hv.2 a b t0))
    (fun _ _ h => ⟨h.1.1, ⟨h.1.2.1, h.2⟩, h.1.2.2⟩)

theorem calc_min_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_min st a b
    ⦃⇓ r c => ⌜r.1 = lmin (maskL INF a b 0 vals) ∧ ValidS r.2 vals B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ :=
  triple_imp (triple_and (calc_min_spec st vals B hv.1 a b t0) (calc_min_sum st vals B hv.1 hv.2 a b t0))
    (fun _ _ h => ⟨h.1.1, ⟨h.1.2.1, h.2⟩, h.1.2.2⟩)

/-- `calc_sum(a, b)`: the sum of the values at the positions in `[a, b)`, in `O(n)` steps. -/
theorem calc_sum_specS (st : cp.SegmentTreeBeatsSum) (vals : List Int) (B : Int) (hv : ValidS st vals B)
    (a b : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SegmentTreeBeatsSum.calc_sum st a b
    ⦃⇓ r c => ⌜r.1 = (maskL 0 a b 0 vals).sum ∧ ValidS r.2 vals B ∧ c ≤ t0 + 48 * vals.length + 1⌝⦄ := by
  obtain ⟨H, hH, hB, hn, hpre, hT, hn0, h1, h2⟩ := valid_root st vals B hv.1
  have sp := fun t0 => qsum_rec_spec H a b B hB H Cpp.fuel st 0 0 st.n0 t0 hH hpre (hv.2 H hn0)
  simp only [cp.SegmentTreeBeatsSum.calc_sum, cp.SegmentTreeBeatsSum._calc_sum, st_eta]
  mvcgen [sp]
  rename_i c hc res c2 hpost
  obtain ⟨hR, hq, hSh, -, hnn, hc2, hSP⟩ := hpost
  have := valid_of_post _ a b st res.2 vals B H hH hB hn h1 h2 hT hR hSh hnn
  rw [opL_id] at this
  simp only [Int.toNat_zero] at hq
  refine ⟨by rw [hq, hT], ⟨this, sumok_of res.2 st H hSP.1 hSh.2.1 hnn⟩, ?_⟩
  rw [pow_succ] at hc2; omega

end Proofs.Cpp.SegmentTreeBeatsSum
