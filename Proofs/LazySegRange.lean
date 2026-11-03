import Proofs.LazySegProduct
import Proofs.LazySegArith

namespace Proofs.LazySegRange
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.LazySegBlocks
open Proofs.LazySegMath (Rep LzFid Cl SInvL)
open Proofs.LazySegChmin (chminMon mi)
open Proofs.SegmentTreeExec (maxMon mx AppBlk appblk_exec)

/-- The nodes on the two boundary paths that have been pushed: levels `t > i`. -/
def S2 (h l0 r0 i : Nat) : Nat → Prop := fun s =>
  ∃ t, i < t ∧ t ≤ h ∧ ((l0 % 2 ^ t ≠ 0 ∧ s = l0 / 2 ^ t) ∨ (r0 % 2 ^ t ≠ 0 ∧ s = (r0 - 1) / 2 ^ t))

def PInv2 (nn : Nat) (A : List Int) (l0 r0 h i : Nat) (vv : Nat → List Int) : Prop :=
  Rep chminMon nn A (vv 0) (vv 1) ∧ LzFid chminMon (S2 h l0 r0 i) (vv 1)

/-- Optionally push the node `k`. -/
def cpv (c : Prop) [Decidable c] (vv : Nat → List Int) (nn k : Nat) : Nat → List Int := if c then pushVV vv nn k else vv

theorem pow_hi (h t x : Nat) (ht : t ≤ h + 1) (hx : x < 2 ^ (h + 1)) : x / 2 ^ t < 2 ^ (h + 1 - t) := by
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
  have : h + 1 - t + t = h + 1 := by omega
  rw [this]; exact hx

theorem S2_lt (nn h l0 r0 i : Nat) (hN : nn = 2 ^ h) (hl : l0 ≤ 2 * nn) (hr : r0 ≤ 2 * nn) (hi : 1 ≤ i) (hih : i ≤ h) :
    ∀ s, S2 h l0 r0 i s → s < 2 ^ (h - i + 1) := by
  rintro s ⟨t, ht1, ht2, (⟨hm, rfl⟩ | ⟨hm, rfl⟩)⟩
  · have hlt : l0 < 2 ^ (h + 1) := by
      have hne : l0 ≠ 2 * nn := by
        intro e
        apply hm
        rw [e, hN, ← Nat.pow_succ']
        exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
      rw [Nat.pow_succ']; omega
    have := pow_hi h t l0 (by omega) hlt
    have h2 : 2 ^ (h + 1 - t) ≤ 2 ^ (h - i) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 2 ^ (h - i) < 2 ^ (h - i + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  · have hlt : r0 - 1 < 2 ^ (h + 1) := by
      have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
      have hne : r0 - 1 < 2 * nn := by omega
      rw [Nat.pow_succ']; omega
    have := pow_hi h t (r0 - 1) (by omega) hlt
    have h2 : 2 ^ (h + 1 - t) ≤ 2 ^ (h - i) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 2 ^ (h - i) < 2 ^ (h - i + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega

theorem push_gen (nn : Nat) (A : List Int) (h i k : Nat) (vv : Nat → List Int) (S : Nat → Prop) (hN : nn = 2 ^ h) (hi : 1 ≤ i)
    (hih : i ≤ h) (hk : 2 ^ (h - i) ≤ k ∧ k < 2 ^ (h - i + 1)) (hSlt : ∀ s, S s → s < 2 ^ (h - i + 1))
    (hR : Rep chminMon nn A (vv 0) (vv 1)) (hF : LzFid chminMon S (vv 1)) :
    Rep chminMon nn A (pushVV vv nn k 0) (pushVV vv nn k 1) ∧
      LzFid chminMon (fun s => S s ∨ s = k) (pushVV vv nn k 1) := by
  have hpos : 0 < 2 ^ (h - i) := Nat.two_pow_pos _
  have h1 : 2 ^ (h - i + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ (h - i + 1) = 2 * 2 ^ (h - i) := Nat.pow_succ' ..
  have hk1 : 1 ≤ k := by omega
  have hk2 : k < nn := by rw [hN]; omega
  rw [pushVV_0, pushVV_1]
  refine ⟨Proofs.LazySegMath.rep_push _ nn A _ _ _ hk1 hk2 hR, ?_⟩
  exact Proofs.LazySegMath.pushLz_fid2 _ nn (vv 1) k S hk1 hk2 hR.2.1 (fun s hs => by
    have := hSlt s hs
    omega) hF

theorem push_opt (nn : Nat) (A : List Int) (h i k : Nat) (vv : Nat → List Int) (S : Nat → Prop) (c : Prop) [Decidable c]
    (hN : nn = 2 ^ h) (hi : 1 ≤ i) (hih : i ≤ h) (hk : c → 2 ^ (h - i) ≤ k ∧ k < 2 ^ (h - i + 1))
    (hSlt : ∀ s, S s → s < 2 ^ (h - i + 1)) (hR : Rep chminMon nn A (vv 0) (vv 1)) (hF : LzFid chminMon S (vv 1)) :
    Rep chminMon nn A (cpv c vv nn k 0) (cpv c vv nn k 1) ∧
      LzFid chminMon (fun s => S s ∨ (c ∧ s = k)) (cpv c vv nn k 1) := by
  by_cases hc : c
  · unfold cpv
    rw [if_pos hc]
    obtain ⟨h1, h2⟩ := push_gen nn A h i k vv S hN hi hih (hk hc) hSlt hR hF
    exact ⟨h1, lzfid_mono _ _ _ h2 (fun s hs => by
      rcases hs with hs | ⟨_, hs⟩
      · exact Or.inl hs
      · exact Or.inr hs)⟩
  · unfold cpv
    rw [if_neg hc]
    exact ⟨hR, lzfid_mono _ _ _ hF (fun s hs => by
      rcases hs with hs | ⟨hc', _⟩
      · exact hs
      · exact absurd hc' hc)⟩

theorem left_bounds (nn h i l0 : Nat) (hN : nn = 2 ^ h) (hi : 1 ≤ i) (hih : i ≤ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn)
    (hm : l0 % 2 ^ i ≠ 0) : 2 ^ (h - i) ≤ l0 / 2 ^ i ∧ l0 / 2 ^ i < 2 ^ (h - i + 1) := by
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  constructor
  · have : nn / 2 ^ i ≤ l0 / 2 ^ i := Nat.div_le_div_right hl.1
    rw [hN, Nat.pow_div hih (by decide)] at this
    exact this
  · have hlt : l0 < 2 ^ (h + 1) := by
      have hne : l0 ≠ 2 * nn := by
        intro e
        apply hm
        rw [e, hN, ← Nat.pow_succ']
        exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
      rw [Nat.pow_succ']; omega
    have := pow_hi h i l0 (by omega) hlt
    have e : h + 1 - i = h - i + 1 := by omega
    rw [e] at this; exact this

theorem right_bounds (nn h i r0 : Nat) (hN : nn = 2 ^ h) (hi : 1 ≤ i) (hih : i ≤ h) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (hm : r0 % 2 ^ i ≠ 0) : 2 ^ (h - i) ≤ (r0 - 1) / 2 ^ i ∧ (r0 - 1) / 2 ^ i < 2 ^ (h - i + 1) := by
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hne : r0 ≠ nn := by
    intro e
    apply hm
    rw [e, hN]
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hih)
  constructor
  · have : nn / 2 ^ i ≤ (r0 - 1) / 2 ^ i := Nat.div_le_div_right (by omega)
    rw [hN, Nat.pow_div hih (by decide)] at this
    exact this
  · have hlt : r0 - 1 < 2 ^ (h + 1) := by rw [Nat.pow_succ']; omega
    have := pow_hi h i (r0 - 1) (by omega) hlt
    have e : h + 1 - i = h - i + 1 := by omega
    rw [e] at this; exact this

theorem pInv2_step (nn : Nat) (A : List Int) (l0 r0 h i : Nat) (vv : Nat → List Int) (hN : nn = 2 ^ h) (hi : 1 ≤ i) (hih : i ≤ h)
    (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hI : PInv2 nn A l0 r0 h i vv) :
    PInv2 nn A l0 r0 h (i - 1)
      (cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i)) := by
  obtain ⟨hR, hF⟩ := hI
  have hSlt := S2_lt nn h l0 r0 i hN hl.2 hr.2 hi hih
  obtain ⟨hR1, hF1⟩ := push_opt nn A h i (l0 / 2 ^ i) vv (S2 h l0 r0 i) (l0 % 2 ^ i ≠ 0) hN hi hih
    (fun hc => left_bounds nn h i l0 hN hi hih hl hc) hSlt hR hF
  obtain ⟨hR2, hF2⟩ := push_opt nn A h i ((r0 - 1) / 2 ^ i) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i))
    (fun s => S2 h l0 r0 i s ∨ (l0 % 2 ^ i ≠ 0 ∧ s = l0 / 2 ^ i)) (r0 % 2 ^ i ≠ 0) hN hi hih
    (fun hc => right_bounds nn h i r0 hN hi hih hr hc)
    (fun s hs => by
      rcases hs with hs | ⟨hc, rfl⟩
      · exact hSlt s hs
      · exact (left_bounds nn h i l0 hN hi hih hl hc).2) hR1 hF1
  refine ⟨hR2, lzfid_mono _ _ _ hF2 ?_⟩
  rintro s ⟨t, ht1, ht2, (⟨hm, rfl⟩ | ⟨hm, rfl⟩)⟩
  · by_cases hti : t = i
    · subst hti; exact Or.inl (Or.inr ⟨hm, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, by omega, ht2, Or.inl ⟨hm, rfl⟩⟩)
  · by_cases hti : t = i
    · subst hti; exact Or.inr ⟨hm, rfl⟩
    · exact Or.inl (Or.inl ⟨t, by omega, ht2, Or.inr ⟨hm, rfl⟩⟩)

/-! ### The two-sided path loop: `if (l / pw * pw != l) push(l / pw); if (r / pw * pw != r) push((r - 1) / pw); pw = pw / 2;` -/

abbrev NeE (nv a m : Nat) : NExpr :=
  .binary bT .ne (.binary i32 .mul (.divrem i32 false (.variable i32 (nv + a)) (.variable i32 (nv + m))) (.variable i32 (nv + m)))
    (.variable i32 (nv + a))

abbrev KEl (nv m : Nat) : NExpr := .divrem i32 false (.variable i32 (nv + 3)) (.variable i32 (nv + m))
abbrev KEr (nv m : Nat) : NExpr :=
  .divrem i32 false (.binary i32 .sub (.variable i32 (nv + 4)) (.literal i32 1)) (.variable i32 (nv + m))

abbrev Path2Body (nv m : Nat) : Command :=
  .sequence (.scope (.sequence (.branch (NeE nv 3 m) (.sequence (.scope (PushCall nv (m + 2) (KEl nv m) Sk)) Sk) Sk)
    (.sequence (.branch (NeE nv 4 m) (.sequence (.scope (PushCall nv (m + 2) (KEr nv m) Sk)) Sk) Sk) (PwHalf nv m))))
    (.sequence (.primitive (.assign (nv + m + 1) i32 (.binary i32 .sub (.variable i32 (nv + m + 1)) (.literal i32 1)))) Sk)

abbrev Path2Loop (nv m : Nat) : Command :=
  .whileLoop (.binary bT .ge (.variable i32 (nv + m + 1)) (.literal i32 1)) (Path2Body nv m)

abbrev bodyProd (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
    (.sequence (.primitive (.assign (nv + 4) i32 (.binary i32 .add (.variable i32 (nv + 4)) (.variable i32 (nv + 1)))))
      (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 1))))
        (.sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 (nv + 2)))) (.sequence (Path2Loop nv 5) Sk)))
          (.sequence (.primitive (.declare s64 true (.literal s64 Proofs.LazySegProduct.EMIN)))
            (.sequence (.primitive (.declare s64 true (vS nv 6)))
              (.sequence (.primitive (.declare s64 true (.literal s64 Proofs.LazySegProduct.EMIN)))
                (.sequence (.primitive (.declare s64 true (vS nv 8)))
                  (.sequence (.whileLoop (Proofs.LazySegProduct.condP nv) (Proofs.LazySegProduct.LoopBodyP nv))
                    (Proofs.SegmentTreeExec.AppBlk nv 10 (vS nv 7) (vS nv 9) (.sequence (.primitive (.ret (vS nv 13))) Sk))))))))))

theorem body_eqProd : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product.body
    = bodyProd 2 := rfl

set_option maxHeartbeats 64000000 in
/-- `if (c) { push(KE); }` where the push is wrapped in a scope. -/
theorem cpush_exec (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (cl : List Cell) (m : Nat) (hc : cl.length = m + 2)
    (n0 nn h0 : Nat) (hn0 : cl[0]? = some (ci n0)) (hnn' : cl[1]? = some (ci nn)) (hh0' : cl[2]? = some (ci h0))
    (hn0b : n0 < 2147483648) (hnnb : nn ≤ 1073741824) (hh0b : h0 < 2147483648)
    (NE KE : NExpr) (k : Nat) (c : Prop) [Decidable c]
    (hcnd : vdenM mv vv (penvN mv.nv (gS P cl)) NE = some (if c then 1 else 0))
    (hKE : c → vdenM mv vv (penvN mv.nv (gS P (cl ++ [ci n0, ci nn, ci h0]))) KE = some (k : Int))
    (hk1 : c → 1 ≤ k) (hk2 : c → k < nn) (hl0 : (vv 0).length = 2 * nn) (hl1 : (vv 1).length = nn)
    (hV0 : ∀ i, i < 2 * nn → s64.valid ((vv 0).getD i 0) = true) (hV1 : ∀ i, i < nn → s64.valid ((vv 1).getD i 0) = true) :
    ∃ r : PRM, pexecM mv fu (.branch NE (.sequence (.scope (PushCall mv.nv (m + 2) KE Sk)) Sk) Sk) (gS P cl) vv = some r ∧
      r.ret = none ∧ r.ps = gS P cl ∧ r.vv = cpv c vv nn k ∧ r.cost ≤ 1300 + (vwp NE).1 + (vwp KE).1 ∧
      r.need ≤ P.length + 2 * m + 500 + (vwp NE).2 + (vwp KE).2 ∧ r.wk ≤ 5 := by
  by_cases hcc : c
  · rw [if_pos hcc] at hcnd
    have hKE' := hKE hcc
    obtain ⟨rP, hP, retP, psP, vvP, cP, nP, wP⟩ := pushcall_exec mv hnv ty0 ty1 P vv fu cl (m + 2) hc n0 nn h0 k hn0 hnn' hh0'
      hn0b hnnb hh0b KE hKE' (hk1 hcc) (hk2 hcc) hl0 hl1 hV0 hV1 Sk _
      (pexecM_skip mv fu _ _)
    have b0 := pexecM_scope mv fu _ _ _ _ hP
    rw [psP, List.append_assoc] at b0
    simp only [gS_take] at b0
    have b1 := seqM_some b0 (by simpa using retP) (pexecM_skip mv fu _ _)
    have b2 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hcnd (by decide) _ b1
    refine ⟨_, b2, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using retP
    · simp [cpv, hcc, vvP]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cP ⊢; omega
    · have hn := nP (P.length + 2 * m + 500 + (vwp NE).2 + (vwp KE).2) (by simp [gS_mem_len, gS_bs_len, hc]; omega) (by omega)
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hc] at hn ⊢
      omega
    · simp at wP ⊢; omega
  · rw [if_neg hcc] at hcnd
    have b2 := pexecM_branch_false mv fu _ (.sequence (.scope (PushCall mv.nv (m + 2) KE Sk)) Sk) Sk _ _ hcnd _
      (pexecM_skip mv fu _ _)
    refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [cpv, hcc]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hc]; omega
    · simp

set_option maxRecDepth 100000 in
theorem ne_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (cl : List Cell) (a m x pw : Nat)
    (hx : cl[a]? = some (ci x)) (hp : cl[m]? = some (ci pw)) (hx31 : x < 2147483648) (hpw0 : 0 < pw) (hpw : pw < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (NeE mv.nv a m) = some (if x % pw ≠ 0 then 1 else 0) := by
  have ex : penvN mv.nv (gS P cl) (mv.nv + a) i32 = some (x : Int) := envs mv P cl a (ci x) hx (i32v x hx31)
  have ep : penvN mv.nv (gS P cl) (mv.nv + m) i32 = some (pw : Int) := envs mv P cl m (ci pw) hp (i32v pw hpw)
  have hle : x / pw * pw ≤ x := Nat.div_mul_le_self x pw
  have hmul : binaryValue .mul ((x / pw : Nat) : Int) (pw : Int) = ((x / pw * pw : Nat) : Int) := by
    show ((x / pw : Nat) : Int) * (pw : Int) = _
    exact (Int.natCast_mul _ _).symm
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_binary, den_divrem, den_variable, ex, Option.bind_some, den_variable, ep,
    Option.bind_some, cdr_i32_div x pw hx31 hpw0 hpw, Option.bind_some, Option.bind_some, hmul,
    conv_signed i32 rfl rfl _ (i32v _ (by show x / pw * pw < 2147483648; omega)), Option.bind_some, Option.bind_some]
  have hdiv := Nat.div_add_mod x pw
  by_cases h : x % pw ≠ 0
  · have : ¬ (((x / pw * pw : Nat) : Int) = (x : Int)) := by
      intro e
      have e' : x / pw * pw = x := by exact_mod_cast e
      apply h
      have := Nat.div_add_mod x pw
      rw [Nat.mul_comm] at e'
      omega
    generalize (((x / pw * pw : Nat) : Int)) = Q at this ⊢
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]
  · have h' : x % pw = 0 := by simpa using h
    have : (((x / pw * pw : Nat) : Int) = (x : Int)) := by
      have : x / pw * pw = x := by rw [Nat.mul_comm]; omega
      exact_mod_cast this
    generalize (((x / pw * pw : Nat) : Int)) = Q at this ⊢
    simp [binaryValue, h, this, Ty.convert, bT, Ty.valid]

theorem kEr_den (env : Nat → Ty → Option Int) (a b x y : Nat) (ha : env a i32 = some (x : Int)) (hb : env b i32 = some (y : Int))
    (hx1 : 1 ≤ x) (hx : x < 2147483648) (hy0 : 0 < y) (hy : y < 2147483648) :
    (NExpr.divrem i32 false (.binary i32 .sub (.variable i32 a) (.literal i32 1)) (.variable i32 b)).denote env =
      some (((x - 1) / y : Nat) : Int) := by
  have hs : binaryValue .sub (x : Int) 1 = ((x - 1 : Nat) : Int) := by
    show (x : Int) - 1 = _; omega
  rw [den_divrem, den_binary, den_variable, ha, Option.bind_some, den_literal, if_pos (show i32.valid 1 = true from rfl),
    Option.bind_some, hs, conv_signed i32 rfl rfl _ (i32v _ (by show x - 1 < 2147483648; omega)), Option.bind_some,
    den_variable, hb, Option.bind_some, cdr_i32_div (x - 1) y (by omega) hy0 hy]

set_option maxHeartbeats 64000000 in
/-- One iteration of the two-sided path loop. -/
theorem path2_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (fu : Nat) (pb : List Cell) (m : Nat) (hm : pb.length + 5 = m)
    (A : List Int) (nn h n0 l0 r0 i : Nat) (hN : nn = 2 ^ h) (hh29 : h ≤ 29) (hn0b : n0 < 2147483648)
    (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hi : 1 ≤ i) (hih : i ≤ h)
    (hI : PInv2 nn A l0 r0 h i vv) :
    ∃ r : PRM, pexecM mv fu (Path2Body mv.nv m) (gS P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i), ci i])) vv = some r ∧
      r.ret = none ∧ r.ps = gS P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci (i - 1)]) ∧
      r.vv = cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i) ∧
      r.cost ≤ 3300 ∧ r.need ≤ P.length + 2 * m + 700 ∧ r.wk ≤ 10 := by
  have hN30 : nn ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
    have h30 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hpow : 2 ^ i ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hih
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpw31 : 2 ^ i < 2147483648 := by omega
  have hnnpos : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hl31 : l0 < 2147483649 := by omega
  obtain ⟨hR, hF⟩ := hI
  set cl := [ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i), ci i] with hcl
  have hc : cl.length = m + 2 := by simp [hcl]; omega
  have c0 : cl[0]? = some (ci n0) := by simp [hcl]
  have c1 : cl[1]? = some (ci nn) := by simp [hcl]
  have c2 : cl[2]? = some (ci h) := by simp [hcl]
  have c3 : cl[3]? = some (ci l0) := by simp [hcl]
  have c4 : cl[4]? = some (ci r0) := by simp [hcl]
  have hlen5 : ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb).length = m := by simp; omega
  have cm : cl[m]? = some (ci (2 ^ i)) := by
    rw [hcl, List.getElem?_append_right (by rw [hlen5]), hlen5]; simp
  have hv0 := rep_valid0 nn A (vv 0) (vv 1) hR
  have hv1 := rep_valid1 nn A (vv 0) (vv 1) hR
  have hSlt := S2_lt nn h l0 r0 i hN hl.2 hr.2 hi hih
  obtain ⟨hR1, hF1⟩ := push_opt nn A h i (l0 / 2 ^ i) vv (S2 h l0 r0 i) (l0 % 2 ^ i ≠ 0) hN hi hih
    (fun hc => left_bounds nn h i l0 hN hi hih hl hc) hSlt hR hF
  have hpowi : 2 ^ (h - i + 1) ≤ nn := by
    rw [hN]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hone : ∀ x, 2 ^ (h - i) ≤ x → 1 ≤ x := fun x hx => by
    have := Nat.two_pow_pos (h - i); omega
  have env3 : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + 3) i32 = some (l0 : Int) := fun ys =>
    envs mv P (cl ++ ys) 3 (ci l0) (by rw [List.getElem?_append_left (by omega)]; exact c3) (i32v l0 (by show l0 < 2147483648; omega))
  have env4 : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + 4) i32 = some (r0 : Int) := fun ys =>
    envs mv P (cl ++ ys) 4 (ci r0) (by rw [List.getElem?_append_left (by omega)]; exact c4) (i32v r0 (by show r0 < 2147483648; omega))
  have envm : ∀ ys : List Cell, penvN mv.nv (gS P (cl ++ ys)) (mv.nv + m) i32 = some ((2 ^ i : Nat) : Int) := fun ys =>
    envs mv P (cl ++ ys) m (ci (2 ^ i)) (by rw [List.getElem?_append_left (by omega)]; exact cm) (i32v _ (by show 2 ^ i < 2147483648; omega))
  -- the first conditional push
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := cpush_exec mv hnv ty0 ty1 P vv fu cl m hc n0 nn h c0 c1 c2 hn0b (by omega)
    (by omega) (NeE mv.nv 3 m) (KEl mv.nv m) (l0 / 2 ^ i) (l0 % 2 ^ i ≠ 0)
    (ne_val mv P vv cl 3 m l0 (2 ^ i) c3 cm (by omega) hpos hpw31)
    (fun _ => by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact divvar_den _ _ _ l0 (2 ^ i) (env3 _) (envm _) (by omega) hpos hpw31)
    (fun hc' => hone _ (left_bounds nn h i l0 hN hi hih hl hc').1)
    (fun hc' => by have := (left_bounds nn h i l0 hN hi hih hl hc').2; omega)
    hR.1 hR.2.1 hv0 hv1
  -- the second conditional push
  obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ := cpush_exec mv hnv ty0 ty1 P (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) fu cl m hc
    n0 nn h c0 c1 c2 hn0b (by omega) (by omega) (NeE mv.nv 4 m) (KEr mv.nv m) ((r0 - 1) / 2 ^ i) (r0 % 2 ^ i ≠ 0)
    (ne_val mv P _ cl 4 m r0 (2 ^ i) c4 cm (by omega) hpos hpw31)
    (fun _ => by
      rw [vdenM_scalar _ _ _ _ rfl]
      exact kEr_den _ _ _ r0 (2 ^ i) (env4 _) (envm _) (by omega) (by omega) hpos hpw31)
    (fun hc' => hone _ (right_bounds nn h i r0 hN hi hih hr hc').1)
    (fun hc' => by have := (right_bounds nn h i r0 hN hi hih hr hc').2; omega)
    hR1.1 hR1.2.1 (rep_valid0 nn A _ _ hR1) (rep_valid1 nn A _ _ hR1)
  -- pw = pw / 2
  obtain ⟨rH, hH, retH, psH, vvH, cH, nH, wH⟩ := pwhalf_exec mv P
    (cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i)) fu ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb) [] m
    hlen5 (2 ^ i) i hpw31
  have hH' : pexecM mv fu (PwHalf mv.nv m) (gS P cl) (cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i))
      = some rH := by
    simpa [hcl] using hH
  have s2 := seqM_some hB retB (by rw [psB, vvB]; exact hH')
  have s1 := seqM_some hA retA (by rw [psA, vvA]; exact s2)
  have b0 := pexecM_scope mv fu _ _ _ _ s1
  have eps : rH.ps = gS P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i]) := by
    simpa using psH
  have tk := Proofs.PexecKit.scope_take (gS P cl) rH.ps (by rw [eps]; simp [gS_mem_len, hcl]) (by rw [eps]; simp [gS_bs_len, hcl])
  simp only [tk] at b0
  rw [eps] at b0
  -- the decrement
  have cI : ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i])[m + 1]? = some (ci i) := by
    rw [List.getElem?_append_right (by rw [hlen5]; omega), hlen5]; simp
  have EI := envs mv P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i]) (m + 1) (ci i) cI
    (i32v i (by show i < 2147483648; omega))
  have e2 := dec_val mv (cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i))
    (penvN mv.nv (gS P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i]))) (mv.nv + (m + 1)) i EI hi
    (by omega)
  have s3 := gSM_assign mv P ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i])
    (cpv (r0 % 2 ^ i ≠ 0) (cpv (l0 % 2 ^ i ≠ 0) vv nn (l0 / 2 ^ i)) nn ((r0 - 1) / 2 ^ i)) (m + 1) (by simp; omega) i32 _ _ _ e2
    (ci i) cI rfl (i32v i (by show i < 2147483648; omega))
    (conv_signed i32 rfl rfl _ (i32v _ (by show i - 1 < 2147483648; omega)))
  have eS : ([ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci i]).set (m + 1) ⟨i32, ((i - 1 : Nat) : Int)⟩ =
      [ci n0, ci nn, ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i / 2), ci (i - 1)] := by
    rw [List.set_append_right _ _ (by rw [hlen5]; omega), hlen5]
    simp
  rw [eS] at s3
  have a3 := (pexecM_prim mv fu (.assign (mv.nv + m + 1) i32 (.binary i32 .sub (.variable i32 (mv.nv + m + 1)) (.literal i32 1))) _ _).trans s3
  have b2 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have b3 := seqM_some b0 (by simpa using retH) (by rw [vvH]; exact b2)
  refine ⟨_, b3, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · first | rfl | simp [vvH]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cA cB cH ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nA nB nH ⊢
    omega
  · simp at wA wB wH ⊢; omega

set_option maxHeartbeats 64000000 in
theorem path2_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (pb : List Cell) (m : Nat) (hm : pb.length + 5 = m) (A : List Int) (h n0 l0 r0 : Nat) (hh29 : h ≤ 29)
    (hn0b : n0 < 2147483648) (hl : 2 ^ h ≤ l0 ∧ l0 ≤ 2 * 2 ^ h) (hr : 2 ^ h ≤ r0 ∧ r0 ≤ 2 * 2 ^ h) :
    ∀ (d i : Nat) (vv : Nat → List Int) (fu : Nat), i = d → i ≤ h → PInv2 (2 ^ h) A l0 r0 h i vv → d + 1 ≤ fu →
      ∃ (res : PRM) (vf : Nat → List Int),
        pexecM mv fu (Path2Loop mv.nv m) (gS P ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i), ci i])) vv = some res ∧
        res.ret = none ∧ res.ps = gS P ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ 0), ci 0]) ∧ res.vv = vf ∧
        PInv2 (2 ^ h) A l0 r0 h 0 vf ∧ res.cost ≤ 3400 * d + 30 ∧ res.need ≤ P.length + 2 * m + 700 ∧ res.wk ≤ 10 * d := by
  have hlen5 : ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb).length = m := by simp; omega
  intro d
  induction d with
  | zero =>
    intro i vv fu hid hih hI hfu
    have him : i = 0 := hid
    subst him
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ge1 mv P vv ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ 0), ci 0]) m 0 (by
      rw [List.getElem?_append_right (by rw [hlen5]; omega), hlen5]; simp) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, vv, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; omega
    · simp
  | succ d ih =>
    intro i vv fu hid hih hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_ge1 mv P vv ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ i), ci i]) m i (by
      rw [List.getElem?_append_right (by rw [hlen5]; omega), hlen5]; simp) (by omega)
    rw [if_pos (by omega)] at hc
    have hdiv : 2 ^ i / 2 = 2 ^ d := by
      rw [show i = d + 1 from hid, Nat.pow_succ]; omega
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := path2_iter mv hnv ty0 ty1 P vv (fu' + 1) pb m hm A (2 ^ h) h n0 l0 r0 i rfl
      hh29 hn0b hl hr (by omega) hih hI
    have hnext := pInv2_step (2 ^ h) A l0 r0 h i vv rfl (by omega) hih hl hr hI
    have e1 : i - 1 = d := by omega
    rw [e1] at hnext
    have ps1' : r1.ps = gS P ([ci n0, ci (2 ^ h), ci h, ci l0, ci r0] ++ pb ++ [ci (2 ^ d), ci d]) := by rw [ps1, hdiv, e1]
    obtain ⟨r2, vf, h2, ret2, ps2, vv2, hIf, c2, n2, w2⟩ := ih d _ fu' rfl (by omega) hnext (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1', vv1, h2]
    refine ⟨_, vf, rfl, ret2, ps2, vv2, hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

/-! ### The tree vector of the abstract array -/

open Proofs.SegTreeMath in
/-- The values of the ideal tree of `A`. -/
def treeVec (A : List Int) (N : Nat) : List Int :=
  (List.range (2 * N)).map (Proofs.LazySegMath.tr chminMon (Proofs.LazySegMath.lfA chminMon A N) N)

theorem treeVec_len (A : List Int) (N : Nat) : (treeVec A N).length = 2 * N := by simp [treeVec]

theorem treeVec_get (A : List Int) (N k : Nat) (hk : k < 2 * N) :
    (treeVec A N).getD k 0 = Proofs.LazySegMath.tr chminMon (Proofs.LazySegMath.lfA chminMon A N) N k := by
  simp [treeVec, List.getD_eq_getElem?_getD, hk]

theorem treeVec_allV (A : List Int) (N : Nat) (hN : 0 < N) (hA : A.length = N) (hAV : Proofs.SegTreeMath.AllV chminMon.toMon A) :
    Proofs.SegTreeMath.AllV maxMon (treeVec A N) := by
  intro x hx
  unfold treeVec at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have hk' : k < 2 * N := List.mem_range.mp hk
  by_cases h0 : k = 0
  · subst h0
    rw [Proofs.LazySegMath.tr_leaf chminMon _ N 0 (by omega)]
    show chminMon.V (A.getD (0 - N) chminMon.e)
    rw [Nat.zero_sub]
    exact Proofs.LazySegMath.getD_Ve chminMon A hAV 0 (by omega)
  · exact Proofs.LazySegMath.tr_v chminMon _ N (Proofs.LazySegMath.leafV_lfA chminMon A N hAV hA) k (by omega) hk'

theorem treeVec_TInv (A : List Int) (N : Nat) (hN : 0 < N) :
    Proofs.SegTreeMath.TInv maxMon (treeVec A N) N := by
  refine ⟨hN, treeVec_len A N, ?_⟩
  intro i h1 h2
  rw [treeVec_get A N i (by omega), treeVec_get A N (2 * i) (by omega), treeVec_get A N (2 * i + 1) (by omega),
    Proofs.LazySegMath.tr_node chminMon _ N i h1 h2]
  rfl

theorem rfold_leaves (A : List Int) (N : Nat) (hA : A.length = N) :
    ∀ (len a : Nat), a + len ≤ N → Proofs.SegTreeMath.rfold maxMon (treeVec A N) (N + a) len =
      Proofs.SegTreeMath.rfold maxMon A a len := by
  intro len
  induction len with
  | zero => intro a _; rfl
  | succ len ih =>
    intro a ha
    unfold Proofs.SegTreeMath.rfold
    have e : N + a + 1 = N + (a + 1) := by omega
    rw [e, ih (a + 1) (by omega), treeVec_get A N (N + a) (by omega), Proofs.LazySegMath.tr_leaf chminMon _ N (N + a) (by omega)]
    unfold Proofs.LazySegMath.lfA
    rw [Nat.add_sub_cancel_left, Proofs.LazySegBlocks.getD_dflt A a chminMon.e 0 (by omega)]

/-! ### The loop state of `product` / `update(l, r, f)` -/

open Proofs.LazySegArith in
def LRp (h l0 r0 : Nat) : Nat → Nat → Prop := fun l r =>
  ∃ j, j ≤ h + 1 ∧ l = ceilDiv l0 (2 ^ j) ∧ r = r0 / 2 ^ j

theorem LRp_init (h l0 r0 : Nat) : LRp h l0 r0 l0 r0 := ⟨0, by omega, by simp [Proofs.LazySegArith.ceilDiv], by simp⟩

theorem LRp_step (h l0 r0 : Nat) (hl0 : 1 ≤ l0) (hr0 : r0 ≤ 2 ^ (h + 1)) (l r : Nat) (hLR : LRp h l0 r0 l r) (hlr : l < r) :
    LRp h l0 r0 (Proofs.SegTreeMath.pl1 l / 2) (Proofs.SegTreeMath.pr1 r / 2) := by
  obtain ⟨j, hj, rfl, rfl⟩ := hLR
  have hjh : j ≤ h := by
    apply Classical.byContradiction
    intro hc
    have hj' : j = h + 1 := by omega
    subst hj'
    have h1 := Proofs.LazySegArith.ceil_pos l0 (2 ^ (h + 1)) hl0 (Nat.two_pow_pos _)
    have h2 : r0 / 2 ^ (h + 1) ≤ 1 := by
      have : r0 / 2 ^ (h + 1) ≤ 2 ^ (h + 1) / 2 ^ (h + 1) := Nat.div_le_div_right hr0
      rw [Nat.div_self (Nat.two_pow_pos _)] at this
      exact this
    omega
  refine ⟨j + 1, by omega, ?_, ?_⟩
  · rw [Proofs.LazySegArith.ceil_step]
    unfold Proofs.SegTreeMath.pl1
    split <;> omega
  · rw [Proofs.LazySegArith.floor_step]
    unfold Proofs.SegTreeMath.pr1
    split <;> omega

/-- A clean node equals the ideal tree. -/
theorem node_clean (N : Nat) (A node lz : List Int) (k : Nat) (hR : Rep chminMon N A node lz) (hCl : Cl chminMon lz k)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * N) : node.getD k chminMon.e = Proofs.LazySegMath.tr chminMon (Proofs.LazySegMath.lfA chminMon A N) N k := by
  obtain ⟨hn, hl, hA, hV, hF, hAV, hE⟩ := hR
  have hG := Proofs.LazySegMath.G_clean chminMon lz hF k hCl
  have := hE k hk1 hk2 (fun h => h)
  rw [hG, chminMon.mp_id _ (Proofs.LazySegMath.getD_Ve chminMon node hV k (by omega))] at this
  exact this

theorem read_left (nn : Nat) (A : List Int) (l0 r0 h : Nat) (vv : Nat → List Int) (hN : nn = 2 ^ h)
    (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hI : PInv2 nn A l0 r0 h 0 vv) (l r : Nat)
    (hLR : LRp h l0 r0 l r) (hlr : l < r) (hodd : l % 2 = 1) :
    (vv 0).getD l 0 = (treeVec A nn).getD l 0 := by
  obtain ⟨hR, hF⟩ := hI
  obtain ⟨j, hj, hl', hr'⟩ := hLR
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hl1 : 1 ≤ l := by rw [hl']; exact Proofs.LazySegArith.ceil_pos l0 _ (by omega) (Nat.two_pow_pos _)
  have hr2 : r ≤ 2 * nn := by
    rw [hr']; exact le_trans (Nat.div_le_self _ _) hr.2
  have hCl : Cl chminMon (vv 1) l := by
    intro t ht h1
    have hodd' : Proofs.LazySegArith.ceilDiv l0 (2 ^ j) % 2 = 1 := by rw [← hl']; exact hodd
    obtain ⟨hm, he⟩ := Proofs.LazySegArith.left_anc l0 j t ht hodd'
    rw [hl'] at h1 ⊢
    apply hF
    refine ⟨j + t, by omega, ?_, Or.inl ⟨hm, he⟩⟩
    apply Classical.byContradiction
    intro hc
    have hpow : 2 ^ (h + 1) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : l0 < 2 ^ (j + t) := by
      by_cases hq : j + t = h + 1
      · have hne : l0 ≠ 2 * nn := by
          intro e; apply hm
          rw [e, hN, ← Nat.pow_succ', hq]
          exact Nat.mod_self _
        rw [hq, Nat.pow_succ']; omega
      · have hp2 : 2 ^ (h + 2) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.pow_succ' (n := h + 1), Nat.pow_succ' (n := h)] at hp2
        omega
    rw [he, Nat.div_eq_of_lt hlt] at h1
    omega
  have := node_clean nn A (vv 0) (vv 1) l hR hCl hl1 (by omega)
  rw [treeVec_get A nn l (by omega), ← this]
  exact Proofs.LazySegBlocks.getD_dflt (vv 0) l 0 chminMon.e (by rw [hR.1]; omega)

theorem read_right (nn : Nat) (A : List Int) (l0 r0 h : Nat) (vv : Nat → List Int) (hN : nn = 2 ^ h)
    (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hI : PInv2 nn A l0 r0 h 0 vv) (l r : Nat)
    (hLR : LRp h l0 r0 l r) (hlr : l < r) (hodd : r % 2 = 1) :
    (vv 0).getD (r - 1) 0 = (treeVec A nn).getD (r - 1) 0 := by
  obtain ⟨hR, hF⟩ := hI
  obtain ⟨j, hj, hl', hr'⟩ := hLR
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hl1 : 1 ≤ l := by rw [hl']; exact Proofs.LazySegArith.ceil_pos l0 _ (by omega) (Nat.two_pow_pos _)
  have hr2 : r ≤ 2 * nn := by
    rw [hr']; exact le_trans (Nat.div_le_self _ _) hr.2
  have hCl : Cl chminMon (vv 1) (r - 1) := by
    intro t ht h1
    have hodd' : (r0 / 2 ^ j) % 2 = 1 := by rw [← hr']; exact hodd
    obtain ⟨hm, he⟩ := Proofs.LazySegArith.right_anc r0 j t ht hodd'
    rw [hr'] at h1 ⊢
    apply hF
    refine ⟨j + t, by omega, ?_, Or.inr ⟨hm, he⟩⟩
    apply Classical.byContradiction
    intro hc
    have hpow : 2 ^ (h + 1) ≤ 2 ^ (j + t) := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : r0 - 1 < 2 ^ (j + t) := by
      rw [Nat.pow_succ'] at hpow; omega
    rw [he, Nat.div_eq_of_lt hlt] at h1
    omega
  have := node_clean nn A (vv 0) (vv 1) (r - 1) hR hCl (by omega) (by omega)
  rw [treeVec_get A nn (r - 1) (by omega), ← this]
  exact Proofs.LazySegBlocks.getD_dflt (vv 0) (r - 1) 0 chminMon.e (by rw [hR.1]; omega)

open Proofs.LazySegProduct (LPL EMIN condP LoopBodyP prod_loop)

theorem emin_valid_ll : s64.valid EMIN = true := by decide

set_option maxHeartbeats 128000000 in
theorem body_execProd (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (ty1 : mv.ty 1 = s64) (P : List Cell)
    (vv : Nat → List Int) (n h l0 r0 : Nat) (A : List Int) (hh29 : h ≤ 29) (hn : n < 2147483648) (hlr : l0 ≤ r0)
    (hrN : r0 ≤ 2 ^ h) (hR : Rep chminMon (2 ^ h) A (vv 0) (vv 1)) (fu : Nat) (hfu : h + Nat.log2 (r0 - l0) + 8 ≤ fu) :
    ∃ (r : PRM) (vf : Nat → List Int), pexecM mv fu (bodyProd mv.nv) (gS P [ci n, ci (2 ^ h), ci h, ci l0, ci r0]) vv = some r ∧
      r.ret = some (Proofs.SegTreeMath.rfold maxMon A l0 (r0 - l0)) ∧ r.vv = vf ∧ Rep chminMon (2 ^ h) A (vf 0) (vf 1) ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧ r.cost ≤ 3400 * h + 1600 * (Nat.log2 (r0 - l0) + 1) + 700 ∧
      r.need ≤ P.length + 800 ∧ r.wk ≤ 10 * h := by
  have hN29 : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hNpos : 0 < 2 ^ h := Nat.two_pow_pos h
  set N := 2 ^ h with hNdef
  have hl31 : l0 < 2147483648 := by omega
  have hr31 : r0 < 2147483648 := by omega
  have hN31 : N < 2147483648 := by omega
  -- l += n_node; r += n_node
  have eN : penvN mv.nv (gS P [ci n, ci N, ci h, ci l0, ci r0]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci l0, ci r0] 1 (ci N) rfl (i32v N hN31)
  have eL : penvN mv.nv (gS P [ci n, ci N, ci h, ci l0, ci r0]) (mv.nv + 3) i32 = some (l0 : Int) :=
    envs mv P [ci n, ci N, ci h, ci l0, ci r0] 3 (ci l0) rfl (i32v l0 hl31)
  have vA : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci l0, ci r0]))
      (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) = some ((l0 + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eL, Option.bind_some, den_variable, eN, Option.bind_some]
    have : binaryValue .add (l0 : Int) (N : Int) = ((l0 + N : Nat) : Int) := by
      show (l0 : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show l0 + N < 2147483648; omega))
  have s5 := gSM_assign mv P [ci n, ci N, ci h, ci l0, ci r0] vv 3 (by simp) i32 _ _ _ vA (ci l0) rfl rfl (i32v l0 hl31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show l0 + N < 2147483648; omega)))
  have eS5 : [ci n, ci N, ci h, ci l0, ci r0].set 3 ⟨i32, ((l0 + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (l0 + N), ci r0] := rfl
  rw [eS5] at s5
  have a5 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s5
  have eR : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l0 + N), ci r0]) (mv.nv + 4) i32 = some (r0 : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l0 + N), ci r0] 4 (ci r0) rfl (i32v r0 hr31)
  have eN2 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l0 + N), ci r0]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l0 + N), ci r0] 1 (ci N) rfl (i32v N hN31)
  have vB : vdenM mv vv (penvN mv.nv (gS P [ci n, ci N, ci h, ci (l0 + N), ci r0]))
      (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1))) = some ((r0 + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, eR, Option.bind_some, den_variable, eN2, Option.bind_some]
    have : binaryValue .add (r0 : Int) (N : Int) = ((r0 + N : Nat) : Int) := by
      show (r0 : Int) + (N : Int) = _; push_cast; rfl
    rw [this]; exact conv_signed i32 rfl rfl _ (i32v _ (by show r0 + N < 2147483648; omega))
  have s6 := gSM_assign mv P [ci n, ci N, ci h, ci (l0 + N), ci r0] vv 4 (by simp) i32 _ _ _ vB (ci r0) rfl rfl (i32v r0 hr31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show r0 + N < 2147483648; omega)))
  have eS6 : [ci n, ci N, ci h, ci (l0 + N), ci r0].set 4 ⟨i32, ((r0 + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] := rfl
  rw [eS6] at s6
  have a6 := (pexecM_prim mv fu (.assign (mv.nv + 4) i32 (.binary i32 .add (.variable i32 (mv.nv + 4)) (.variable i32 (mv.nv + 1)))) _ _).trans s6
  -- pw = n_node
  have eN3 : penvN mv.nv (gS P [ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)]) (mv.nv + 1) i32 = some (N : Int) :=
    envs mv P [ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] 1 (ci N) rfl (i32v N hN31)
  have d7 := gSM_decl mv P [ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] vv i32 (.variable i32 (mv.nv + 1)) (N : Int) (N : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eN3) (conv_signed i32 rfl rfl _ (i32v N hN31))
  have a7 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 1))) _ _).trans d7
  -- i = h_node
  have eH : penvN mv.nv (gS P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N])) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N]) 2 (ci h) rfl (i32v h (by show h < 2147483648; omega))
  have d8 := gSM_decl mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N]) vv i32 (.variable i32 (mv.nv + 2)) (h : Int) (h : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact eH) (conv_signed i32 rfl rfl _ (i32v h (by show h < 2147483648; omega)))
  have a8 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 2))) _ _).trans d8
  -- the path loop
  have hI0 : PInv2 N A (l0 + N) (r0 + N) h h vv := ⟨hR, fun s ⟨t, ht1, ht2, _⟩ => absurd ht2 (by omega)⟩
  obtain ⟨rL, vf, hL, retL, psL, vvL, hIf, cL, nL, wL⟩ := path2_loop mv hnv ty0 ty1 P [] 5 rfl A h n (l0 + N) (r0 + N) hh29 hn
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h h vv fu rfl le_rfl hI0 (by omega)
  have hL' : pexecM mv fu (Path2Loop mv.nv 5) (gS P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N] ++ [ci h])) vv = some rL := hL
  have sLoop := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have sIn := seqM_some a8 rfl sLoop
  have b0 := pexecM_scope mv fu _ _ _ _ sIn
  have tk : (⟨(gS P ([ci n, ci (2 ^ h), ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0), ci 0])).mem.take
      (gS P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N])).mem.length,
      (gS P ([ci n, ci (2 ^ h), ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0), ci 0])).bs.take
      (gS P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N])).bs.length⟩ : PS) =
        gS P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)]) :=
    gS_takeC P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci N]) ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)]) [ci 0] rfl
  rw [psL, List.append_nil] at b0
  simp only [tk] at b0
  -- the four declarations
  have lit : ∀ cl : List Cell, vdenM mv vf (penvN mv.nv (gS P cl)) (.literal s64 EMIN) = some EMIN := by
    intro cl; rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos emin_valid_ll]
  have d1 := gSM_decl mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)]) vf s64 (.literal s64 EMIN) EMIN EMIN (lit _)
    (conv_signed s64 rfl rfl _ emin_valid_ll)
  have a1 := (pexecM_prim mv fu (.declare s64 true (.literal s64 EMIN)) _ _).trans d1
  have d2 := gSM_decl mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)] ++ [cs EMIN]) vf s64 (vS mv.nv 6) EMIN EMIN
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 6 EMIN rfl emin_valid_ll) (conv_signed s64 rfl rfl _ emin_valid_ll)
  have a2 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 6)) _ _).trans d2
  have d3 := gSM_decl mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)] ++ [cs EMIN] ++ [cs EMIN]) vf s64
    (.literal s64 EMIN) EMIN EMIN (lit _) (conv_signed s64 rfl rfl _ emin_valid_ll)
  have a3 := (pexecM_prim mv fu (.declare s64 true (.literal s64 EMIN)) _ _).trans d3
  have d4 := gSM_decl mv P ([ci n, ci N, ci h, ci (l0 + N), ci (r0 + N)] ++ [ci (2 ^ 0)] ++ [cs EMIN] ++ [cs EMIN] ++ [cs EMIN]) vf s64
    (vS mv.nv 8) EMIN EMIN (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 8 EMIN rfl emin_valid_ll)
    (conv_signed s64 rfl rfl _ emin_valid_ll)
  have a4 := (pexecM_prim mv fu (.declare s64 true (vS mv.nv 8)) _ _).trans d4
  -- the loop
  have hRf := hIf.1
  have hlenV : (treeVec A N).length = 2 * N := treeVec_len A N
  have hV : Proofs.SegTreeMath.AllV maxMon (treeVec A N) := treeVec_allV A N hNpos hRf.2.2.1 hRf.2.2.2.2.2.1
  have hT : Proofs.SegTreeMath.TInv maxMon (treeVec A N) N := treeVec_TInv A N hNpos
  set T := Proofs.SegTreeMath.rfold maxMon (treeVec A N) (l0 + N) (r0 - l0) with hTdef
  have vT : s64.valid T = true := Proofs.SegTreeMath.rfold_V maxMon (treeVec A N) hV (r0 - l0) (l0 + N) (by omega)
  have hI0 : Proofs.SegTreeMath.PInv maxMon (treeVec A N) N T (l0 + N) (r0 + N) EMIN EMIN := by
    refine ⟨by omega, by omega, by omega, emin_valid_ll, emin_valid_ll, ?_⟩
    have e : r0 + N - (l0 + N) = r0 - l0 := by omega
    rw [e]
    show maxMon.op (maxMon.op maxMon.e T) maxMon.e = T
    rw [maxMon.lid _ vT, maxMon.rid _ vT]
  have hls : Proofs.LazySegProduct.lsteps (r0 - l0) ≤ Nat.log2 (r0 - l0) + 1 := by
    unfold Proofs.LazySegProduct.lsteps; split <;> omega
  have hLR0 : LRp h (l0 + N) (r0 + N) (l0 + N) (r0 + N) := LRp_init h _ _
  obtain ⟨rP, lF, rF, leftF, rightF, hP, retP, psP, vvP, hIP, hex, cP, nP, wP⟩ :=
    prod_loop mv hnv ty0 P (treeVec A N) vf n N h (2 ^ 0) T hn hN31 (by omega) hV hT (by omega) (by rw [hlenV, hRf.1]) (LRp h (l0 + N) (r0 + N))
    (fun l r hLR hlr => LRp_step h (l0 + N) (r0 + N) (by omega) (by rw [Nat.pow_succ']; omega) l r hLR hlr)
    (fun l r hLR hlr => ⟨fun hodd => read_left N A (l0 + N) (r0 + N) h vf rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hIf l r hLR hlr hodd,
      fun hodd => read_right N A (l0 + N) (r0 + N) h vf rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hIf l r hLR hlr hodd⟩)
    (r0 - l0) (l0 + N) (r0 + N) EMIN EMIN fu (by omega) hLR0 hI0 (by omega)
  have hexit := Proofs.SegTreeMath.PInv_exit maxMon (treeVec A N) N T lF rF leftF rightF hIP hex
  obtain ⟨_, _, _, vLF, vRF, _⟩ := hIP
  -- the final apply
  have hX : vdenM mv vf (penvN mv.nv (gS P (LPL n N h lF rF (2 ^ 0) leftF rightF))) (vS mv.nv 7) = some leftF := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 7 leftF rfl vLF
  have hY : vdenM mv vf (penvN mv.nv (gS P (LPL n N h lF rF (2 ^ 0) leftF rightF ++ [cs leftF]))) (vS mv.nv 9) = some rightF := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 9 rightF rfl vRF
  have vm : s64.valid (mx leftF rightF) = true := by unfold mx; split <;> assumption
  obtain ⟨r2, hr2, ret2, ps2, vv2, c2, n2, w2⟩ : ∃ r2 : PRM,
      pexecM mv fu (.sequence (.primitive (.ret (vS mv.nv 13))) Sk)
        (gS P (LPL n N h lF rF (2 ^ 0) leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)])) vf = some r2 ∧
      r2.ret = some (mx leftF rightF) ∧ r2.ps = gS P (LPL n N h lF rF (2 ^ 0) leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)]) ∧
      r2.vv = vf ∧ r2.cost ≤ 100 ∧ r2.need ≤ P.length + 70 ∧ r2.wk = 0 := by
    have rr := pstmtM_ret_ok mv (gS P (LPL n N h lF rF (2 ^ 0) leftF rightF ++ [cs leftF, cs rightF, cs (mx leftF rightF), cs (mx leftF rightF)]))
      vf (vS mv.nv 13) (mx leftF rightF)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact vr mv P _ 13 (mx leftF rightF) rfl vm)
    have e5 := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (vS mv.nv 13)) _ _).trans rr) rfl
    refine ⟨_, e5, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := appblk_exec mv P vf fu (LPL n N h lF rF (2 ^ 0) leftF rightF) 10 rfl (vS mv.nv 7) (vS mv.nv 9)
    leftF rightF vLF vRF hX hY (.sequence (.primitive (.ret (vS mv.nv 13))) Sk) r2 hr2
  have s9 := seqM_some hP retP (by rw [psP, vvP]; exact hA)
  have s8 := seqM_some a4 rfl s9
  have s7 := seqM_some a3 rfl s8
  have s6' := seqM_some a2 rfl s7
  have s5' := seqM_some a1 rfl s6'
  have s4 := seqM_some b0 (by simp) (by rw [vvL]; exact s5')
  have s3 := seqM_some a7 rfl s4
  have s2 := seqM_some a6 rfl s3
  have s1 := seqM_some a5 rfl s2
  have hmx : mx leftF rightF = T := hexit
  have hTA : T = Proofs.SegTreeMath.rfold maxMon A l0 (r0 - l0) := by
    rw [hTdef]
    have := rfold_leaves A N hRf.2.2.1 (r0 - l0) l0 (by omega)
    rwa [Nat.add_comm N l0] at this
  refine ⟨_, vf, s1, ?_, ?_, hRf, ⟨_, psA.trans ps2⟩, ?_, ?_, ?_⟩
  · simp [retA, ret2, hmx, hTA]
  · simp [vvA, vv2]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL cP cA c2 ⊢
    omega
  · have hA' := nA (P.length + 90) (by omega) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hA' nL nP n2 ⊢
    omega
  · simp at wA w2 wL wP ⊢
    omega

end Proofs.LazySegRange
