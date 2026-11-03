import Proofs.ForLoopC
import Proofs.Generated.SquareMatrix

namespace Proofs.MatMulExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)

abbrev M64 : Nat := 18446744073709551616
abbrev cu (x : Nat) : Cell := ⟨u64, (x : Int)⟩

/-- The `t`-th term of the dot product of row `i` of `a` and column `j` of `b`. -/
def term (a b : List Nat) (n i j t : Nat) : Nat := a.getD (i * n + t) 0 * b.getD (t * n + j) 0

/-- The first `m` terms of that dot product (a natural number; the program works modulo `2^64`). -/
def dsum (a b : List Nat) (n i j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => dsum a b n i j m + term a b n i j m

/-- The contents of the three vectors. -/
def VV (a b c : List Nat) : Nat → List Int := fun k =>
  if k = 0 then a.map (fun x : Nat => (x : Int)) else if k = 1 then b.map (fun x : Nat => (x : Int))
  else if k = 2 then c.map (fun x : Nat => (x : Int)) else []

theorem VV_write (a b c : List Nat) (p x : Nat) :
    upd (VV a b c) 2 ((VV a b c 2).set p (x : Int)) = VV a b (c.set p x) := by
  funext k
  unfold upd VV
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp [List.map_set]
      · simp [h0, h1, h2]

theorem VV_get0 (a b c : List Nat) : VV a b c 0 = a.map (fun x : Nat => (x : Int)) := by simp [VV]
theorem VV_get1 (a b c : List Nat) : VV a b c 1 = b.map (fun x : Nat => (x : Int)) := by simp [VV]
theorem VV_get2 (a b c : List Nat) : VV a b c 2 = c.map (fun x : Nat => (x : Int)) := by simp [VV]

theorem vec_getM (v : List Nat) (j : Nat) (hj : j < v.length) :
    (v.map (fun x : Nat => (x : Int)))[j]? = some ((v.getD j 0 : Nat) : Int) := by
  simp [List.getElem?_map, hj, List.getD_eq_getElem?_getD]

/-! ### Expressions (variable `nv + c` is the scalar cell `c`: 0 = n, 1 = i, 2 = j, 3 = s, 4 = k) -/

abbrev mIdx (nv x y : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (nv + x)) (.variable i32 nv)) (.variable i32 (nv + y)))
abbrev rdA (nv : Nat) : NExpr := .read u64 (.local 0) (mIdx nv 1 4)
abbrev rdB (nv : Nat) : NExpr := .read u64 (.local 1) (mIdx nv 4 2)
abbrev accS (nv : Nat) : NStmt :=
  .assign (nv + 3) u64 (.binary u64 .add (.variable u64 (nv + 3)) (.binary u64 .mul (rdA nv) (rdB nv)))
abbrev Bk (nv : Nat) : Command := .sequence (.primitive (accS nv)) (.primitive .skip)

theorem vdenM_binary (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (t : Ty) (op : Binary) (l r : NExpr)
    (h : (NExpr.binary t op l r).scalarOnly = false) :
    vdenM mv vv env (.binary t op l r) =
      (vdenM mv vv env l).bind fun a => (vdenM mv vv env r).bind fun b => t.convert (binaryValue op a b) := by
  rw [vdenM, if_neg (by rw [h]; decide)]

theorem rdM_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (k : Nat) (hk : k < mv.nv) (t : Ty)
    (hty : t = mv.ty k) (index : NExpr) (hs : index.scalarOnly = true) (hrc : (NExpr.read t (.local k) index).scalarOnly = false)
    (idx : Nat) (hd : index.denote env = some (idx : Int)) (x : Nat) (hx : (vv k)[idx]? = some (x : Int))
    (hxv : (mv.ty k).valid (x : Int) = true) :
    vdenM mv vv env (.read t (.local k) index) = some (x : Int) := by
  rw [vdenM, if_neg (by rw [hrc]; decide), if_pos ⟨hk, hty, hs⟩, hd, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg idx), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

theorem mIdx_den (env : Nat → Ty → Option Int) (nv x y na nb n : Nat) (h1 : env nv i32 = some (n : Int))
    (ha : env (nv + x) i32 = some (na : Int)) (hb : env (nv + y) i32 = some (nb : Int)) (hlt : na * n + nb < 2147483648) :
    (mIdx nv x y).denote env = some ((na * n + nb : Nat) : Int) := by
  have hm : na * n < 2147483648 := by omega
  rw [den_cast, den_binary, den_binary, den_variable, ha, Option.bind_some, den_variable, h1, Option.bind_some]
  have e1 : binaryValue .mul (na : Int) (n : Int) = ((na * n : Nat) : Int) := by
    show (na : Int) * (n : Int) = _; push_cast; rfl
  rw [e1, conv_signed i32 rfl rfl _ (validN _ hm), Option.bind_some, den_variable, hb, Option.bind_some]
  have e2 : binaryValue .add ((na * n : Nat) : Int) (nb : Int) = ((na * n + nb : Nat) : Int) := by
    show ((na * n : Nat) : Int) + (nb : Int) = _; push_cast; rfl
  rw [e2, conv_signed i32 rfl rfl _ (validN _ hlt), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem idx_lt (n i k : Nat) (hi : i < n) (hk : k < n) : i * n + k < n * n := by
  have : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  rw [Nat.add_mul] at this
  omega

theorem u64v (x : Nat) (h : x < M64) : u64.valid (x : Int) = true := by
  have h' : x < 18446744073709551616 := h
  rw [valid_u64]; exact decide_eq_true ⟨by omega, by omega⟩

/-- The environment of the cells `[n, i, j, s, k]`. -/
theorem envK (mv : MV) (P : List Cell) (n i j s k : Nat) (hn : n < 2147483648) (hi : i < 2147483648) (hj : j < 2147483648)
    (hs : s < M64) (hk : k < 2147483648) :
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]) mv.nv i32 = some (n : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]) (mv.nv + 1) i32 = some (i : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]) (mv.nv + 2) i32 = some (j : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]) (mv.nv + 3) u64 = some (s : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]) (mv.nv + 4) i32 = some (k : Int) :=
  ⟨gSM_env mv.nv P _ 0 (ci n) rfl (validN n hn), gSM_env mv.nv P _ 1 (ci i) rfl (validN i hi),
   gSM_env mv.nv P _ 2 (ci j) rfl (validN j hj), gSM_env mv.nv P _ 3 (cu s) rfl (u64v s hs),
   gSM_env mv.nv P _ 4 (ci k) rfl (validN k hk)⟩

theorem mulE_val (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i j s k : Nat) (hi : i < n) (hj : j < n) (hk : k < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hs : s < M64) :
    vdenM mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]))
      (.binary u64 .add (.variable u64 (mv.nv + 3)) (.binary u64 .mul (rdA mv.nv) (rdB mv.nv))) =
      some (((s + term a b n i j k % M64) % M64 : Nat) : Int) := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  obtain ⟨E0, E1, E2, E3, E4⟩ := envK mv P n i j s k hn32 (by omega) (by omega) hs (by omega)
  have l1 := idx_lt n i k hi hk
  have l2 := idx_lt n k j hk hj
  have ga : ∀ idx, idx < n * n → a.getD idx 0 < M64 := by
    intro idx hidx
    have : a.getD idx 0 = a[idx]'(by omega) := by simp [List.getD_eq_getElem?_getD, hla, hidx]
    rw [this]; exact haM _ (List.getElem_mem _)
  have gb : ∀ idx, idx < n * n → b.getD idx 0 < M64 := by
    intro idx hidx
    have : b.getD idx 0 = b[idx]'(by omega) := by simp [List.getD_eq_getElem?_getD, hlb, hidx]
    rw [this]; exact hbM _ (List.getElem_mem _)
  have dA := mIdx_den (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k])) mv.nv 1 4 i k n E0 E1 E4 (by omega)
  have dB := mIdx_den (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k])) mv.nv 4 2 k j n E0 E4 E2 (by omega)
  have rA := rdM_val mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k])) 0 (by omega) u64 (hty 0).symm
    (mIdx mv.nv 1 4) rfl rfl (i * n + k) dA (a.getD (i * n + k) 0) (by rw [VV_get0]; exact vec_getM a _ (by omega))
    (by rw [hty]; exact u64v _ (ga _ l1))
  have rB := rdM_val mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k])) 1 (by omega) u64 (hty 1).symm
    (mIdx mv.nv 4 2) rfl rfl (k * n + j) dB (b.getD (k * n + j) 0) (by rw [VV_get1]; exact vec_getM b _ (by omega))
    (by rw [hty]; exact u64v _ (gb _ l2))
  have hmul : vdenM mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k]))
      (.binary u64 .mul (rdA mv.nv) (rdB mv.nv)) = some ((term a b n i j k % M64 : Nat) : Int) := by
    have hb : (NExpr.binary u64 .mul (rdA mv.nv) (rdB mv.nv)).scalarOnly = false := rfl
    rw [vdenM_binary _ _ _ _ _ _ _ hb, rA, rB, Option.bind_some, Option.bind_some]
    have : binaryValue .mul ((a.getD (i * n + k) 0 : Nat) : Int) ((b.getD (k * n + j) 0 : Nat) : Int) =
        ((term a b n i j k : Nat) : Int) := by
      show _ * _ = _; unfold term; push_cast; rfl
    rw [this, convert_u64]
    congr 1
  have hb : (NExpr.binary u64 .add (.variable u64 (mv.nv + 3)) (.binary u64 .mul (rdA mv.nv) (rdB mv.nv))).scalarOnly = false := rfl
  have hv : vdenM mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu s, ci k])) (NExpr.variable u64 (mv.nv + 3)) =
      some (s : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  rw [vdenM_binary _ _ _ _ _ _ _ hb, hv, hmul, Option.bind_some, Option.bind_some]
  have : binaryValue .add (s : Int) ((term a b n i j k % M64 : Nat) : Int) = ((s + term a b n i j k % M64 : Nat) : Int) := by
    show (s : Int) + _ = _; push_cast; rfl
  rw [this, convert_u64]
  congr 1

theorem u64_conv_nat (x : Nat) (h : x < M64) : u64.convert (x : Int) = some (x : Int) := by
  rw [convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have h' : x < 18446744073709551616 := h; omega)

theorem step_lt (s t : Nat) (hs : s < M64) : (s + t % M64) % M64 < M64 := Nat.mod_lt _ (by decide)

/-- One iteration of the innermost loop: `s += a[i*n+k] * b[k*n+j]`. -/
theorem k_body (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i j s k : Nat) (hi : i < n) (hj : j < n) (hk : k < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hs : s < M64) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bk mv.nv) (gS P ([ci n, ci i, ci j, cu s] ++ [ci k])) (VV a b c) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci n, ci i, ci j, cu ((s + term a b n i j k % M64) % M64)] ++ [ci k]) ∧ r.vv = VV a b c ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk = 0 := by
  have hv := mulE_val mv hnv hty a b c haM hbM P n i j s k hi hj hk hnn hla hlb hs
  have asg := gSM_assign mv P [ci n, ci i, ci j, cu s, ci k] (VV a b c) 3 (by simp) u64 _ _ _ hv (cu s) rfl rfl (u64v s hs)
    (u64_conv_nat _ (step_lt s _ hs))
  have q1 := (pexecM_prim mv fu (accS mv.nv) _ _).trans asg
  have q2 := seqM_some q1 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, q2, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]

theorem n_small (n : Nat) (h : n * n < 2147483648) : n < 2147483647 := by
  by_cases h2 : 2 ≤ n
  · have := Nat.mul_le_mul_right n h2
    omega
  · omega

theorem dsum_lt (a b : List Nat) (n i j m : Nat) : dsum a b n i j m % M64 < M64 := Nat.mod_lt _ (by decide)

/-- The whole `for (int k = 0; k < n; k++) s += a[i*n+k] * b[k*n+j];` statement. -/
theorem k_loop (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i j : Nat) (hi : i < n) (hj : j < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmt mv.nv 4 (Bk mv.nv)) (gS P [ci n, ci i, ci j, cu 0]) (VV a b c) = some res ∧
      res.ps = gS P [ci n, ci i, ci j, cu (dsum a b n i j n % M64)] ∧ res.vv = VV a b c ∧ res.ret = none ∧
      res.cost ≤ 420 * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk = 0 := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 4 n (by omega) hn32 (Bk mv.nv)
    (fun t vv C => vv = VV a b c ∧ C = [ci n, ci i, ci j, cu (dsum a b n i j t % M64)]) 400 100 0 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hk := k_body mv hnv hty a b c haM hbM P n i j (dsum a b n i j t % M64) t hi hj ht hnn hla hlb
        (dsum_lt a b n i j t) fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], [ci n, ci i, ci j, cu ((dsum a b n i j t % M64 + term a b n i j t % M64) % M64)], hr, hret, ?_, rfl, rfl, ?_, hc, hnd, ?_⟩
      · simpa using hps
      · refine ⟨hvv, ?_⟩
        show _ = [ci n, ci i, ci j, cu ((dsum a b n i j t + term a b n i j t) % M64)]
        rw [← Nat.add_mod]
      · omega)
    (VV a b c) [ci n, ci i, ci j, cu 0] rfl rfl ⟨rfl, by simp [dsum]⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  refine ⟨res, hr, hps, hvv, hret, ?_, hnd, ?_⟩
  · omega
  · omega

abbrev declS : NStmt := .declare u64 true (.cast u64 (.literal i32 0))
abbrev wrS (nv : Nat) : NStmt := .write (.local 2) u64 (mIdx nv 1 2) (.variable u64 (nv + 3))
abbrev Bj (nv : Nat) : Command :=
  .sequence (.primitive declS) (.sequence (forStmt nv 4 (Bk nv)) (.sequence (.primitive (wrS nv)) (.primitive .skip)))

theorem zero_u64 (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenM mv vv (penvN mv.nv ps) (.cast u64 (.literal i32 0)) = some 0 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  rfl

theorem envW (mv : MV) (P : List Cell) (n i j s : Nat) (hn : n < 2147483648) (hi : i < 2147483648) (hj : j < 2147483648)
    (hs : s < M64) :
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s]) mv.nv i32 = some (n : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s]) (mv.nv + 1) i32 = some (i : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s]) (mv.nv + 2) i32 = some (j : Int) ∧
    penvN mv.nv (gS P [ci n, ci i, ci j, cu s]) (mv.nv + 3) u64 = some (s : Int) :=
  ⟨gSM_env mv.nv P _ 0 (ci n) rfl (validN n hn), gSM_env mv.nv P _ 1 (ci i) rfl (validN i hi),
   gSM_env mv.nv P _ 2 (ci j) rfl (validN j hj), gSM_env mv.nv P _ 3 (cu s) rfl (u64v s hs)⟩

/-- One iteration of the middle loop: `c[i*n+j] = sum_k a[i*n+k] * b[k*n+j]`. -/
theorem j_body (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i j : Nat) (hi : i < n) (hj : j < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (Bj mv.nv) (gS P ([ci n, ci i] ++ [ci j])) (VV a b c) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci n, ci i] ++ [ci j] ++ [cu (dsum a b n i j n % M64)]) ∧
      r.vv = VV a b (c.set (i * n + j) (dsum a b n i j n % M64)) ∧
      r.cost ≤ 420 * n + 200 ∧ r.need ≤ P.length + 100 ∧ r.wk = 1 := by
  have hn32 : n < 2147483647 := n_small n hnn
  have d := gSM_decl mv P [ci n, ci i, ci j] (VV a b c) u64 _ 0 0 (zero_u64 mv _ _) (u64_conv_nat 0 (by decide))
  have q1 := (pexecM_prim mv fu declS _ _).trans d
  obtain ⟨⟨kps, kvv, kret, kcost, kneed, kwk⟩, hkr, hkps, hkvv, hkret, hkc, hknd, hkwk⟩ :=
    k_loop mv hnv hty a b c haM hbM P n i j hi hj hnn hla hlb fu hfu
  simp only at hkps hkvv hkret hkc hknd hkwk
  subst hkps hkvv hkret hkwk
  obtain ⟨E0, E1, E2, E3⟩ := envW mv P n i j (dsum a b n i j n % M64) (by omega) (by omega) (by omega) (dsum_lt a b n i j n)
  have hx : vdenM mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu (dsum a b n i j n % M64)]))
      (NExpr.variable u64 (mv.nv + 3)) = some ((dsum a b n i j n % M64 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have hp : vdenM mv (VV a b c) (penvN mv.nv (gS P [ci n, ci i, ci j, cu (dsum a b n i j n % M64)]))
      (mIdx mv.nv 1 2) = some ((i * n + j : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact mIdx_den _ mv.nv 1 2 i j n E0 E1 E2 (by have := idx_lt n i j hi hj; omega)
  have w := pstmtM_write_ok mv (gS P [ci n, ci i, ci j, cu (dsum a b n i j n % M64)]) (VV a b c) 2 (by omega)
    (mIdx mv.nv 1 2) (.variable u64 (mv.nv + 3)) _ (i * n + j) hx hp
    (by rw [VV_get2]; simp [hlc]; exact idx_lt n i j hi hj) (by rw [hty]; exact u64v _ (dsum_lt a b n i j n))
  rw [hty 2] at w
  have a1 := (pexecM_prim mv fu (wrS mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P [ci n, ci i, ci j, cu (dsum a b n i j n % M64)])
    (upd (VV a b c) 2 ((VV a b c 2).set (i * n + j) ((dsum a b n i j n % M64 : Nat) : Int))))
  have b1 := seqM_some hkr rfl a2
  have b2 := seqM_some q1 rfl b1
  refine ⟨_, b2, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact VV_write a b c (i * n + j) _
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp

/-- `c` after the first `t` entries of row `i` were computed. -/
def rowC (a b : List Nat) (n i : Nat) (c : List Nat) : Nat → List Nat
  | 0 => c
  | t + 1 => (rowC a b n i c t).set (i * n + t) (dsum a b n i t n % M64)

/-- `c` after the first `t` rows were computed. -/
def matC (a b : List Nat) (n : Nat) (c : List Nat) : Nat → List Nat
  | 0 => c
  | t + 1 => rowC a b n t (matC a b n c t) n

theorem rowC_length (a b : List Nat) (n i : Nat) (c : List Nat) : ∀ t, (rowC a b n i c t).length = c.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [rowC, ih]

theorem matC_length (a b : List Nat) (n : Nat) (c : List Nat) : ∀ t, (matC a b n c t).length = c.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [matC, rowC_length, ih]

theorem j_loop (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i : Nat) (hi : i < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 2 * n + 2 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmt mv.nv 2 (Bj mv.nv)) (gS P [ci n, ci i]) (VV a b c) = some res ∧
      res.ps = gS P [ci n, ci i] ∧ res.vv = VV a b (rowC a b n i c n) ∧ res.ret = none ∧
      res.cost ≤ (420 * n + 220) * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 2 n (by omega) hn32 (Bj mv.nv)
    (fun t vv C => vv = VV a b (rowC a b n i c t) ∧ C = [ci n, ci i]) (420 * n + 200) 100 1 (n + 1) (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hvv, hC⟩ hfu'
      subst hvv; subst hC
      have hk := j_body mv hnv hty a b (rowC a b n i c t) haM hbM P n i t hi ht hnn hla hlb
        (by rw [rowC_length]; exact hlc) fu hfu'
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [cu (dsum a b n i t n % M64)], [ci n, ci i], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, by omega⟩
      rw [hvv]; rfl)
    (VV a b c) [ci n, ci i] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  exact ⟨res, hr, hps, hvv, hret, hc, hnd, by omega⟩

def cj (n : Nat) : Nat := (420 * n + 220) * n + 30
def cI (n : Nat) : Nat := (cj n + 20) * n + 30

abbrev Bi (nv : Nat) : Command := .sequence (forStmt nv 2 (Bj nv)) (.primitive .skip)
abbrev bodyMM (nv : Nat) : Command := .sequence (forStmt nv 1 (Bi nv)) (.primitive .skip)

theorem i_body (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n i : Nat) (hi : i < n)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 2 * n + 2 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (Bi mv.nv) (gS P ([ci n] ++ [ci i])) (VV a b c) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci n] ++ [ci i] ++ []) ∧ r.vv = VV a b (rowC a b n i c n) ∧
      r.cost ≤ cj n ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ n := by
  obtain ⟨⟨jps, jvv, jret, jcost, jneed, jwk⟩, hj, hps, hvv, hret, hc, hnd, hw⟩ :=
    j_loop mv hnv hty a b c haM hbM P n i hi hnn hla hlb hlc fu hfu
  simp only at hps hvv hret hc hnd hw
  subst hps hvv hret
  have b1 := seqM_some hj rfl (pexecM_skip mv fu (gS P [ci n, ci i]) (VV a b (rowC a b n i c n)))
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [cj] using hc
  · simp [gS_size]; omega
  · simpa using hw

theorem i_loop (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n : Nat)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 3 * n + 4 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmt mv.nv 1 (Bi mv.nv)) (gS P [ci n]) (VV a b c) = some res ∧
      res.ps = gS P [ci n] ∧ res.vv = VV a b (matC a b n c n) ∧ res.ret = none ∧
      res.cost ≤ cI n ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n * n := by
  have hn32 : n < 2147483647 := n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 1 n (by omega) hn32 (Bi mv.nv)
    (fun t vv C => vv = VV a b (matC a b n c t) ∧ C = [ci n]) (cj n) 100 n (2 * n + 2) (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hvv, hC⟩ hfu'
      subst hvv; subst hC
      have hk := i_body mv hnv hty a b (matC a b n c t) haM hbM P n t ht hnn hla hlb
        (by rw [matC_length]; exact hlc) fu hfu'
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], [ci n], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv]; rfl)
    (VV a b c) [ci n] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hI
  subst hC
  exact ⟨res, hr, hps, hvv, hret, hc, hnd, hw⟩

theorem body_exec (mv : MV) (hnv : mv.nv = 3) (hty : ∀ k, mv.ty k = u64) (a b c : List Nat) (haM : ∀ x ∈ a, x < M64)
    (hbM : ∀ x ∈ b, x < M64) (P : List Cell) (n : Nat)
    (hnn : n * n < 2147483648) (hla : a.length = n * n) (hlb : b.length = n * n) (hlc : c.length = n * n)
    (fu : Nat) (hfu : 3 * n + 4 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyMM mv.nv) (gS P [ci n]) (VV a b c) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n] ∧ r.vv = VV a b (matC a b n c n) ∧
      r.cost ≤ cI n ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ n * n := by
  obtain ⟨⟨ips, ivv, iret, icost, ineed, iwk⟩, hi, hps, hvv, hret, hc, hnd, hw⟩ :=
    i_loop mv hnv hty a b c haM hbM P n hnn hla hlb hlc fu hfu
  simp only at hps hvv hret hc hnd hw
  subst hps hvv hret
  have b1 := seqM_some hi rfl (pexecM_skip mv fu (gS P [ci n]) (VV a b (matC a b n c n)))
  refine ⟨_, b1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa using hc
  · simp [gS_size]; omega
  · simpa using hw

theorem getD_setM (v : List Nat) (i x j : Nat) :
    (v.set i x).getD j 0 = if j = i ∧ i < v.length then x else v.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

/-- The reduced dot product that entry `idx` of the product holds. -/
def Fm (a b : List Nat) (n idx : Nat) : Nat := dsum a b n (idx / n) (idx % n) n % M64

theorem divmod_iff (n i t idx : Nat) (ht : t < n) : idx = i * n + t ↔ (idx / n = i ∧ idx % n = t) := by
  constructor
  · intro h
    subst h
    have hn : 0 < n := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht]; omega
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · rintro ⟨h1, h2⟩
    have := Nat.div_add_mod idx n
    rw [h1, h2] at this
    rw [← this, Nat.mul_comm]

theorem rowC_getD (a b : List Nat) (n i : Nat) (c : List Nat) (hlc : c.length = n * n) (hi : i < n) :
    ∀ t, t ≤ n → ∀ idx, idx < n * n →
      (rowC a b n i c t).getD idx 0 = if idx / n = i ∧ idx % n < t then Fm a b n idx else c.getD idx 0 := by
  intro t
  induction t with
  | zero => intro _ idx _; simp [rowC]
  | succ t ih =>
    intro ht idx hidx
    have hlt : i * n + t < n * n := idx_lt n i t hi (by omega)
    rw [rowC, getD_setM, rowC_length, ih (by omega) idx hidx]
    by_cases h : idx = i * n + t
    · have h' := (divmod_iff n i t idx (by omega)).mp h
      rw [if_pos ⟨h, by omega⟩, if_pos ⟨h'.1, by omega⟩]
      subst h
      unfold Fm
      rw [h'.1, h'.2]
    · have h' : ¬ (idx / n = i ∧ idx % n = t) := fun hh => h ((divmod_iff n i t idx (by omega)).mpr hh)
      rw [if_neg (fun hh => h hh.1)]
      by_cases hc : idx / n = i ∧ idx % n < t + 1
      · have : idx % n < t := by
          by_cases e : idx % n = t
          · exact absurd ⟨hc.1, e⟩ h'
          · omega
        rw [if_pos hc, if_pos ⟨hc.1, this⟩]
      · rw [if_neg hc, if_neg (fun hh => hc ⟨hh.1, by omega⟩)]

theorem matC_getD (a b : List Nat) (n : Nat) (c : List Nat) (hlc : c.length = n * n) :
    ∀ t, t ≤ n → ∀ idx, idx < n * n →
      (matC a b n c t).getD idx 0 = if idx / n < t then Fm a b n idx else c.getD idx 0 := by
  intro t
  induction t with
  | zero => intro _ idx _; simp [matC]
  | succ t ih =>
    intro ht idx hidx
    have hl : (matC a b n c t).length = n * n := by rw [matC_length]; exact hlc
    rw [matC, rowC_getD a b n t _ hl (by omega) n (Nat.le_refl _) idx hidx, ih (by omega) idx hidx]
    by_cases h : idx / n = t
    · have hm : idx % n < n := Nat.mod_lt _ (by omega)
      rw [if_pos ⟨h, hm⟩, if_pos (by omega)]
    · rw [if_neg (fun hh => h hh.1)]
      by_cases hc : idx / n < t
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]

theorem matC_spec (a b : List Nat) (n : Nat) (c : List Nat) (hlc : c.length = n * n) :
    (matC a b n c n).length = n * n ∧ ∀ idx, idx < n * n → (matC a b n c n).getD idx 0 = Fm a b n idx := by
  refine ⟨by rw [matC_length]; exact hlc, ?_⟩
  intro idx hidx
  rw [matC_getD a b n c hlc n (Nat.le_refl _) idx hidx, if_pos]
  have : 0 < n := by
    by_cases h : n = 0
    · subst h; omega
    · omega
  exact (Nat.div_lt_iff_lt_mul this).mpr (by rw [Nat.mul_comm]; exact hidx)

end Proofs.MatMulExec
