import Proofs.ForLoopB
import Proofs.Mul61Body

namespace Proofs.RollingHashCore
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.ForLoopC (gS_takeC)
open Proofs.Mul61Body (midOf retOf mul_bounds mul_vars shr_lit band_pow denote_nat_bin add_hf mul_hf sub_hf shl_hf litN_value)
open Proofs.Mod61Body (M61 u64_lt res_final)

/-- A cell holding an `unsigned long long`. -/
abbrev cu (x : Nat) : Cell := ⟨u64, (x : Int)⟩

/-! ### The program blocks (variable `nv + c` is the scalar cell `c`) -/

abbrev vu (nv c : Nat) : NExpr := .variable u64 (nv + c)
abbrev auS (nv ia : Nat) : NStmt := .declare u64 true (.binary u64 .shr (vu nv ia) (.literal i32 31))
abbrev adS (nv ia i31 : Nat) : NStmt := .declare u64 true (.binary u64 .band (vu nv ia) (vu nv i31))
abbrev buS (nv ib : Nat) : NStmt := .declare u64 true (.binary u64 .shr (vu nv ib) (.literal i32 31))
abbrev bdS (nv ib i31 : Nat) : NStmt := .declare u64 true (.binary u64 .band (vu nv ib) (vu nv i31))
abbrev midS (nv c0 : Nat) : NStmt :=
  .declare u64 true (.binary u64 .add (.binary u64 .mul (vu nv (c0 + 1)) (vu nv (c0 + 2)))
    (.binary u64 .mul (vu nv c0) (vu nv (c0 + 3))))
abbrev miduS (nv c0 : Nat) : NStmt := .declare u64 true (.binary u64 .shr (vu nv (c0 + 4)) (.literal i32 30))
abbrev middS (nv c0 i30 : Nat) : NStmt := .declare u64 true (.binary u64 .band (vu nv (c0 + 4)) (vu nv i30))
abbrev mulvS (nv c0 : Nat) : NStmt :=
  .declare u64 true (.binary u64 .add (.binary u64 .add (.binary u64 .add (.binary u64 .mul (.binary u64 .mul (vu nv c0) (vu nv (c0 + 2)))
    (.cast u64 (.literal i32 2))) (vu nv (c0 + 5))) (.binary u64 .shl (vu nv (c0 + 6)) (.literal i32 31)))
    (.binary u64 .mul (vu nv (c0 + 1)) (vu nv (c0 + 3))))

/-- The eight declarations computing `mul61(a, b)` in the cell `c0 + 7`, followed by `k`. -/
abbrev coreCmd (nv ia ib i31 i30 c0 : Nat) (k : Command) : Command :=
  .sequence (.primitive (auS nv ia)) (.sequence (.primitive (adS nv ia i31)) (.sequence (.primitive (buS nv ib))
  (.sequence (.primitive (bdS nv ib i31)) (.sequence (.primitive (midS nv c0)) (.sequence (.primitive (miduS nv c0))
  (.sequence (.primitive (middS nv c0 i30)) (.sequence (.primitive (mulvS nv c0)) k)))))))

/-- The cells declared by `coreCmd`. -/
def mulCells (a b : Nat) : List Cell :=
  [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30),
   cu (midOf a b % 2^30), cu (retOf a b)]


theorem retOf_small (a b : Nat) (ha : a < 2^61) (hb : b < 2^61) : retOf a b ≤ 9223372030412324861 := by
  have au_lt : a / 2^31 ≤ 2^30 - 1 := by omega
  have bu_lt : b / 2^31 ≤ 2^30 - 1 := by omega
  have ad_lt : a % 2^31 ≤ 2^31 - 1 := by omega
  have bd_lt : b % 2^31 ≤ 2^31 - 1 := by omega
  have p1 : (a / 2^31) * (b / 2^31) ≤ (2^30-1) * (2^30-1) := Nat.mul_le_mul au_lt bu_lt
  have p2 : (a % 2^31) * (b / 2^31) ≤ (2^31-1) * (2^30-1) := Nat.mul_le_mul ad_lt bu_lt
  have p3 : (a / 2^31) * (b % 2^31) ≤ (2^30-1) * (2^31-1) := Nat.mul_le_mul au_lt bd_lt
  have p4 : (a % 2^31) * (b % 2^31) ≤ (2^31-1) * (2^31-1) := Nat.mul_le_mul ad_lt bd_lt
  unfold retOf midOf
  omega

theorem env_at (mv : MV) (P cs : List Cell) (k x : Nat) (hk : cs[k]? = some (cu x)) (hx : x < 18446744073709551616) :
    penvN mv.nv (gS P cs) (mv.nv + k) u64 = some (x : Int) := gSM_env mv.nv P cs k (cu x) hk (u64_lt x hx)

theorem decl_u64 (mv : MV) (fu : Nat) (P cs : List Cell) (vv : Nat → List Int) (e : NExpr) (v : Nat)
    (hs : e.scalarOnly = true) (hv : e.denote (penvN mv.nv (gS P cs)) = some (v : Int)) (hlt : v < 18446744073709551616) :
    pexecM mv fu (.primitive (.declare u64 true e)) (gS P cs) vv =
      some ⟨gS P (cs ++ [cu v]), vv, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 4, 0⟩ := by
  have := gSM_decl mv P cs vv u64 e v v (by rw [vdenM_scalar _ _ _ _ hs]; exact hv)
    (Ty.convert_of_valid u64 _ (u64_lt v hlt))
  exact (pexecM_prim mv fu _ _ _).trans this

theorem decl_u64_x (mv : MV) (fu : Nat) (P cs cs' : List Cell) (vv : Nat → List Int) (e : NExpr) (v : Nat)
    (hs : e.scalarOnly = true) (hv : e.denote (penvN mv.nv (gS P cs)) = some (v : Int)) (hlt : v < 18446744073709551616)
    (hcs : cs ++ [cu v] = cs') :
    pexecM mv fu (.primitive (.declare u64 true e)) (gS P cs) vv =
      some ⟨gS P cs', vv, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 4, 0⟩ := by
  rw [← hcs]; exact decl_u64 mv fu P cs vv e v hs hv hlt

theorem at_new (L xs : List Cell) (t : Nat) (c : Cell) (hv : xs[t]? = some c) : (L ++ xs)[L.length + t]? = some c := by
  rw [List.getElem?_append_right (by omega)]; simpa using hv

theorem get_lt (L : List Cell) (e : List Cell) (k : Nat) (hk : k < L.length) : (L ++ e)[k]? = L[k]? := by
  rw [List.getElem?_append_left hk]

theorem get_new (L e : List Cell) (j : Nat) : (L ++ e)[L.length + j]? = e[j]? := by
  rw [List.getElem?_append_right (by omega)]; simp


theorem two_value (env : Nat → Ty → Option Int) : (NExpr.cast u64 (.literal i32 2)).denote env = some 2 := by
  have a : i32.valid 2 = true := by simp [Ty.valid]
  have b : u64.valid 2 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

/-- The value of the `mulv` expression. -/
theorem mulv_value (env : Nat → Ty → Option Int) (nv c0 a b : Nat) (ha : a < 2^61) (hb : b < 2^61)
    (e0 : env (nv + c0) u64 = some ((a / 2^31 : Nat) : Int)) (e1 : env (nv + (c0 + 1)) u64 = some ((a % 2^31 : Nat) : Int))
    (e2 : env (nv + (c0 + 2)) u64 = some ((b / 2^31 : Nat) : Int)) (e3 : env (nv + (c0 + 3)) u64 = some ((b % 2^31 : Nat) : Int))
    (e5 : env (nv + (c0 + 5)) u64 = some ((midOf a b / 2^30 : Nat) : Int))
    (e6 : env (nv + (c0 + 6)) u64 = some ((midOf a b % 2^30 : Nat) : Int)) :
    (match (mulvS nv c0) with | .declare _ _ e => e | _ => .literal u64 0).denote env = some ((retOf a b : Nat) : Int) := by
  obtain ⟨bd1, bd2, bd3, bd4, bd5, bd6, bd7, bd8⟩ := mul_bounds a b ha hb
  show (NExpr.binary u64 .add (.binary u64 .add (.binary u64 .add (.binary u64 .mul (.binary u64 .mul (vu nv c0) (vu nv (c0 + 2)))
    (.cast u64 (.literal i32 2))) (vu nv (c0 + 5))) (.binary u64 .shl (vu nv (c0 + 6)) (.literal i32 31)))
    (.binary u64 .mul (vu nv (c0 + 1)) (vu nv (c0 + 3)))).denote env = _
  have m1 := mul_vars env (nv + c0) (nv + (c0 + 2)) _ _ e0 e2 (by omega)
  have m2 := denote_nat_bin env .mul (fun x y => x * y) mul_hf _ _ _ 2 m1 (two_value env) (by omega)
  have m3 := denote_nat_bin env .add (fun x y => x + y) add_hf _ _ _ _ m2 (by rw [den_variable]; exact e5) (by omega)
  have m4 := denote_nat_bin env .shl (fun x y => x * 2^y) shl_hf (.variable u64 (nv + (c0 + 6))) (.literal i32 31) _ 31
    (by rw [den_variable]; exact e6) (litN_value env 31 (by decide)) (by omega)
  have m5 := denote_nat_bin env .add (fun x y => x + y) add_hf _ _ _ _ m3 m4 (by omega)
  have m6 := mul_vars env (nv + (c0 + 1)) (nv + (c0 + 3)) _ _ e1 e3 (by omega)
  have m7 := denote_nat_bin env .add (fun x y => x + y) add_hf _ _ _ _ m5 m6 (by unfold retOf midOf at *; omega)
  convert m7 using 3
  unfold retOf midOf
  push_cast
  ring_nf


theorem pow31 : (2147483647 : Nat) = 2^31 - 1 := by decide
theorem pow30 : (1073741823 : Nat) = 2^30 - 1 := by decide

set_option maxHeartbeats 4000000 in
/-- The eight declarations of `coreCmd`, followed by `k`. -/
theorem mul_core (mv : MV) (fu : Nat) (P L : List Cell) (vv : Nat → List Int) (ia ib i31 i30 a b : Nat)
    (ha : a < 2^61) (hb : b < 2^61) (hLa : L[ia]? = some (cu a)) (hLb : L[ib]? = some (cu b))
    (h31 : L[i31]? = some (cu 2147483647)) (h30 : L[i30]? = some (cu 1073741823)) (k : Command) (rr : PRM)
    (hk : pexecM mv fu k (gS P (L ++ mulCells a b)) vv = some rr) :
    ∃ r : PRM, pexecM mv fu (coreCmd mv.nv ia ib i31 i30 L.length k) (gS P L) vv = some r ∧ r.ret = rr.ret ∧
      r.ps = rr.ps ∧ r.vv = rr.vv ∧ r.cost ≤ 400 + rr.cost ∧ r.need ≤ max (P.length + 2 * L.length + 60) rr.need ∧
      r.wk = rr.wk := by
  obtain ⟨bd1, bd2, bd3, bd4, bd5, bd6, bd7, bd8⟩ := mul_bounds a b ha hb
  have haL : ia < L.length := (List.getElem?_eq_some_iff.mp hLa).1
  have hbL : ib < L.length := (List.getElem?_eq_some_iff.mp hLb).1
  have h31L : i31 < L.length := (List.getElem?_eq_some_iff.mp h31).1
  have h30L : i30 < L.length := (List.getElem?_eq_some_iff.mp h30).1
  have a64 : a < 18446744073709551616 := by omega
  have b64 : b < 18446744073709551616 := by omega
  -- the cells after each step
  have g1 : ∀ e, (L ++ e)[ia]? = some (cu a) := fun e => by rw [List.getElem?_append_left haL]; exact hLa
  have g2 : ∀ e, (L ++ e)[ib]? = some (cu b) := fun e => by rw [List.getElem?_append_left hbL]; exact hLb
  have g3 : ∀ e, (L ++ e)[i31]? = some (cu 2147483647) := fun e => by rw [List.getElem?_append_left h31L]; exact h31
  have g4 : ∀ e, (L ++ e)[i30]? = some (cu 1073741823) := fun e => by rw [List.getElem?_append_left h30L]; exact h30
  have n31 : ((2147483647 : Nat) : Int) = (((2^31 - 1 : Nat)) : Int) := by rw [pow31]
  have n30 : ((1073741823 : Nat) : Int) = (((2^30 - 1 : Nat)) : Int) := by rw [pow30]
  -- step 1: au
  have s1 := decl_u64_x mv fu P L (L ++ [cu (a / 2^31)]) vv (.binary u64 .shr (vu mv.nv ia) (.literal i32 31)) (a / 2^31) rfl
    (shr_lit _ (mv.nv + ia) a 31 a64 (by decide) (env_at mv P L ia a hLa a64)) (by omega) rfl
  -- step 2: ad
  have s2 := decl_u64_x mv fu P (L ++ [cu (a / 2^31)]) (L ++ [cu (a / 2^31), cu (a % 2^31)]) vv
    (.binary u64 .band (vu mv.nv ia) (vu mv.nv i31)) (a % 2^31) rfl
    (band_pow _ (mv.nv + ia) (mv.nv + i31) a 31 a64 (env_at mv P _ ia a (g1 _) a64)
      (by have := env_at mv P (L ++ [cu (a / 2^31)]) i31 2147483647 (g3 _) (by omega); rw [pow31] at this; simpa using this))
    (by omega) (by simp)
  -- step 3: bu
  have s3 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31)]) (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31)]) vv
    (.binary u64 .shr (vu mv.nv ib) (.literal i32 31)) (b / 2^31) rfl
    (shr_lit _ (mv.nv + ib) b 31 b64 (by decide) (env_at mv P _ ib b (g2 _) b64)) (by omega) (by simp)
  -- step 4: bd
  have s4 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31)])
    (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]) vv
    (.binary u64 .band (vu mv.nv ib) (vu mv.nv i31)) (b % 2^31) rfl
    (band_pow _ (mv.nv + ib) (mv.nv + i31) b 31 b64 (env_at mv P _ ib b (g2 _) b64)
      (by have := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31)]) i31 2147483647 (g3 _) (by omega)
          rw [pow31] at this; simpa using this))
    (by omega) (by simp)
  -- step 5: mid
  have x4 : ∀ t c, ([cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)] : List Cell)[t]? = some c →
      (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)])[L.length + t]? = some c :=
    fun t c h => at_new L _ t c h
  have v5 : (NExpr.binary u64 .add (.binary u64 .mul (vu mv.nv (L.length + 1)) (vu mv.nv (L.length + 2)))
      (.binary u64 .mul (vu mv.nv L.length) (vu mv.nv (L.length + 3)))).denote
      (penvN mv.nv (gS P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]))) = some ((midOf a b : Nat) : Int) := by
    have e1 := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]) (L.length + 1) (a % 2^31)
      (x4 1 _ rfl) (by omega)
    have e2 := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]) (L.length + 2) (b / 2^31)
      (x4 2 _ rfl) (by omega)
    have e0 := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]) L.length (a / 2^31)
      (by simpa using x4 0 _ rfl) (by omega)
    have e3 := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)]) (L.length + 3) (b % 2^31)
      (x4 3 _ rfl) (by omega)
    have m1 := mul_vars _ (mv.nv + (L.length + 1)) (mv.nv + (L.length + 2)) _ _ e1 e2 (by omega)
    have m2 := mul_vars _ (mv.nv + L.length) (mv.nv + (L.length + 3)) _ _ e0 e3 (by omega)
    have m3 := denote_nat_bin _ .add (fun x y => x + y) add_hf _ _ _ _ m1 m2 (by omega)
    unfold midOf
    exact m3
  have s5 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31)])
    (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b)]) vv _ (midOf a b) rfl v5 (by omega) (by simp)
  -- step 6: midu
  have x5 : ∀ t c, ([cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b)] : List Cell)[t]? = some c →
      (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b)])[L.length + t]? = some c :=
    fun t c h => at_new L _ t c h
  have s6 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b)])
    (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30)]) vv
    (.binary u64 .shr (vu mv.nv (L.length + 4)) (.literal i32 30)) (midOf a b / 2^30) rfl
    (shr_lit _ (mv.nv + (L.length + 4)) (midOf a b) 30 (by omega) (by decide)
      (env_at mv P _ (L.length + 4) (midOf a b) (x5 4 _ rfl) (by omega))) (by omega) (by simp)
  -- step 7: midd
  have x6 : ∀ t c, ([cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30)] : List Cell)[t]? = some c →
      (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30)])[L.length + t]? = some c :=
    fun t c h => at_new L _ t c h
  have s7 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30)])
    (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30)]) vv
    (.binary u64 .band (vu mv.nv (L.length + 4)) (vu mv.nv i30)) (midOf a b % 2^30) rfl
    (band_pow _ (mv.nv + (L.length + 4)) (mv.nv + i30) (midOf a b) 30 (by omega)
      (env_at mv P _ (L.length + 4) (midOf a b) (x6 4 _ rfl) (by omega))
      (by have := env_at mv P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30)])
            i30 1073741823 (g4 _) (by omega)
          rw [pow30] at this; simpa using this))
    (by omega) (by simp)
  -- step 8: mulv
  have x7 : ∀ t c, ([cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30)] : List Cell)[t]? = some c →
      (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30)])[L.length + t]? = some c :=
    fun t c h => at_new L _ t c h
  have v8 := mulv_value (penvN mv.nv (gS P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b),
      cu (midOf a b / 2^30), cu (midOf a b % 2^30)]))) mv.nv L.length a b ha hb
    (env_at mv P _ L.length (a / 2^31) (by simpa using x7 0 _ rfl) (by omega))
    (env_at mv P _ (L.length + 1) (a % 2^31) (x7 1 _ rfl) (by omega))
    (env_at mv P _ (L.length + 2) (b / 2^31) (x7 2 _ rfl) (by omega))
    (env_at mv P _ (L.length + 3) (b % 2^31) (x7 3 _ rfl) (by omega))
    (env_at mv P _ (L.length + 5) (midOf a b / 2^30) (x7 5 _ rfl) (by omega))
    (env_at mv P _ (L.length + 6) (midOf a b % 2^30) (x7 6 _ rfl) (by omega))
  have s8 := decl_u64_x mv fu P (L ++ [cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30)])
    (L ++ mulCells a b) vv _ (retOf a b) rfl v8 bd8 (by simp [mulCells])
  -- compose
  have c8 := seqM_some s8 rfl hk
  have c7 := seqM_some s7 rfl c8
  have c6 := seqM_some s6 rfl c7
  have c5 := seqM_some s5 rfl c6
  have c4 := seqM_some s4 rfl c5
  have c3 := seqM_some s3 rfl c4
  have c2 := seqM_some s2 rfl c3
  have c1 := seqM_some s1 rfl c2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, by simp⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega


theorem pexecM_branch_true (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some v) (hne : v ≠ 0) (r : PRM) (hr : pexecM mv fu y ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hne, hr]

theorem pexecM_branch_false (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some 0) (r : PRM) (hr : pexecM mv fu n ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hr]

/-! ### The reduction modulo `2^61 - 1` -/

abbrev xuS (nv cx : Nat) : NStmt := .declare u64 true (.binary u64 .shr (vu nv cx) (.literal i32 61))
abbrev xdS (nv cx im : Nat) : NStmt := .declare u64 true (.binary u64 .band (vu nv cx) (vu nv im))
abbrev resS (nv c0 : Nat) : NStmt := .declare u64 true (.binary u64 .add (vu nv c0) (vu nv (c0 + 1)))
abbrev geC (nv c0 im : Nat) : NExpr := .binary bl .ge (vu nv (c0 + 2)) (vu nv im)
abbrev subA (nv c0 im : Nat) : NStmt := .assign (nv + (c0 + 2)) u64 (.binary u64 .sub (vu nv (c0 + 2)) (vu nv im))
abbrev yesC (nv c0 im : Nat) : Command := .sequence (.scope (.sequence (.primitive (subA nv c0 im)) Sk)) Sk
abbrev tailCmd (nv cx im c0 : Nat) (k : Command) : Command :=
  .sequence (.primitive (xuS nv cx)) (.sequence (.primitive (xdS nv cx im)) (.sequence (.primitive (resS nv c0))
    (.sequence (.branch (geC nv c0 im) (yesC nv c0 im) Sk) k)))

theorem pow61 : (2305843009213693951 : Nat) = 2^61 - 1 := by decide


theorem ge_value (env : Nat → Ty → Option Int) (i j r : Nat) (hi : env i u64 = some (r : Int))
    (hj : env j u64 = some (M61 : Int)) :
    (NExpr.binary bl .ge (.variable u64 i) (.variable u64 j)).denote env = some (if M61 ≤ r then 1 else 0) := by
  rw [den_binary,den_variable,den_variable,hi,hj]
  simp only [Option.bind_some,binaryValue]
  by_cases c : M61 ≤ r
  · have : (r : Int) ≥ (M61 : Int) := by omega
    simp [this,c]
  · have : ¬ ((r : Int) ≥ (M61 : Int)) := by omega
    simp [this,c]

set_option maxHeartbeats 4000000 in
/-- `xu = x >> 61; xd = x & m; res = xu + xd; if (res >= m) res = res - m;` followed by `k`. -/
theorem tail_core (mv : MV) (hnv : True) (fu : Nat) (P L : List Cell) (vv : Nat → List Int) (cx im x : Nat)
    (hx : x < 18446744073709551616) (hLx : L[cx]? = some (cu x)) (hLm : L[im]? = some (cu M61)) (k : Command) (rr : PRM)
    (hk : pexecM mv fu k (gS P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x % M61)])) vv = some rr) :
    ∃ r : PRM, pexecM mv fu (tailCmd mv.nv cx im L.length k) (gS P L) vv = some r ∧ r.ret = rr.ret ∧
      r.ps = rr.ps ∧ r.vv = rr.vv ∧ r.cost ≤ 200 + rr.cost ∧ r.need ≤ max (P.length + 2 * L.length + 60) rr.need ∧
      r.wk = rr.wk := by
  have hxL : cx < L.length := (List.getElem?_eq_some_iff.mp hLx).1
  have hmL : im < L.length := (List.getElem?_eq_some_iff.mp hLm).1
  have hM : M61 < 2^61 := by unfold M61; omega
  have hmv : ∀ e : List Cell, (L ++ e)[im]? = some (cu M61) := fun e => by rw [List.getElem?_append_left hmL]; exact hLm
  have hxv : ∀ e : List Cell, (L ++ e)[cx]? = some (cu x) := fun e => by rw [List.getElem?_append_left hxL]; exact hLx
  have hdiv : x / 2^61 ≤ 7 := by omega
  have hmod : x % 2^61 < 2^61 := Nat.mod_lt x (by decide)
  have s1 := decl_u64_x mv fu P L (L ++ [cu (x / 2^61)]) vv (.binary u64 .shr (vu mv.nv cx) (.literal i32 61)) (x / 2^61) rfl
    (shr_lit _ (mv.nv + cx) x 61 hx (by decide) (env_at mv P L cx x hLx hx)) (by omega) rfl
  have s2 := decl_u64_x mv fu P (L ++ [cu (x / 2^61)]) (L ++ [cu (x / 2^61), cu (x % 2^61)]) vv
    (.binary u64 .band (vu mv.nv cx) (vu mv.nv im)) (x % 2^61) rfl
    (band_pow _ (mv.nv + cx) (mv.nv + im) x 61 hx (env_at mv P _ cx x (hxv _) hx)
      (by have := env_at mv P (L ++ [cu (x / 2^61)]) im M61 (hmv _) (by omega)
          have e : M61 = 2^61 - 1 := rfl
          rw [e] at this; simpa using this)) (by omega) (by simp)
  have s3 := decl_u64_x mv fu P (L ++ [cu (x / 2^61), cu (x % 2^61)]) (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]) vv
    (.binary u64 .add (vu mv.nv L.length) (vu mv.nv (L.length + 1))) (x / 2^61 + x % 2^61) rfl
    (denote_nat_bin _ .add (fun a b => a + b) add_hf (.variable u64 (mv.nv + L.length)) (.variable u64 (mv.nv + (L.length + 1))) _ _
      (by rw [den_variable]; exact env_at mv P _ L.length (x / 2^61) (by simpa using at_new L [cu (x / 2^61), cu (x % 2^61)] 0 _ rfl) (by omega))
      (by rw [den_variable]; exact env_at mv P _ (L.length + 1) (x % 2^61) (at_new L [cu (x / 2^61), cu (x % 2^61)] 1 _ rfl) (by omega))
      (by omega)) (by omega) (by simp)
  have hc3 : (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)])[L.length + 2]? = some (cu (x / 2^61 + x % 2^61)) :=
    at_new L [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)] 2 _ rfl
  have hgeV := ge_value (penvN mv.nv (gS P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]))) (mv.nv + (L.length + 2))
    (mv.nv + im) (x / 2^61 + x % 2^61)
    (env_at mv P _ (L.length + 2) _ hc3 (by omega)) (env_at mv P _ im M61 (hmv _) (by omega))
  have hres := res_final x hx
  have hvc : vdenM mv vv (penvN mv.nv (gS P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]))) (geC mv.nv L.length im) =
      some (if M61 ≤ x / 2^61 + x % 2^61 then 1 else 0) := by
    rw [vdenM_scalar mv vv _ (geC mv.nv L.length im) rfl]; exact hgeV
  by_cases hge : M61 ≤ x / 2^61 + x % 2^61
  · rw [if_pos hge] at hvc hres
    -- res = res - m
    have hsub : (NExpr.binary u64 .sub (vu mv.nv (L.length + 2)) (vu mv.nv im)).denote
        (penvN mv.nv (gS P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]))) =
        some (((x / 2^61 + x % 2^61 - M61 : Nat)) : Int) := by
      have e1 := env_at mv P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]) (L.length + 2)
        (x / 2^61 + x % 2^61) hc3 (by omega)
      have e2 := env_at mv P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]) im M61 (hmv _) (by omega)
      rw [den_binary, den_variable, den_variable, e1, e2]
      simp only [Option.bind_some]
      rw [sub_hf _ _ hge]
      exact Ty.convert_of_valid _ _ (u64_lt (x / 2^61 + x % 2^61 - M61) (by omega))
    have as := gSM_assign mv P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]) vv (L.length + 2)
      (by simp) u64 (.binary u64 .sub (vu mv.nv (L.length + 2)) (vu mv.nv im)) (((x / 2^61 + x % 2^61 - M61 : Nat)) : Int)
      (((x / 2^61 + x % 2^61 - M61 : Nat)) : Int)
      (by rw [vdenM_scalar mv vv _ (.binary u64 .sub (vu mv.nv (L.length + 2)) (vu mv.nv im)) rfl]; exact hsub) (cu (x / 2^61 + x % 2^61)) hc3 rfl (u64_lt _ (by omega))
      (Ty.convert_of_valid _ _ (u64_lt _ (by omega)))
    have hset : (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)]).set (L.length + 2)
        ⟨u64, (((x / 2^61 + x % 2^61 - M61 : Nat)) : Int)⟩ = L ++ [cu (x / 2^61), cu (x % 2^61), cu (x % M61)] := by
      rw [List.set_append_right _ _ (by omega)]
      simp [hres]
    rw [hset] at as
    have a1 := (pexecM_prim mv fu (subA mv.nv L.length im) _ _).trans as
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    have tk := gS_takeC P (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x / 2^61 + x % 2^61)])
      (L ++ [cu (x / 2^61), cu (x % 2^61), cu (x % M61)]) [] (by simp)
    simp only [List.append_nil] at tk
    rw [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (geC mv.nv L.length im) (yesC mv.nv L.length im) Sk _ _ 1 hvc (by decide) _ a4
    have b2 := seqM_some b1 rfl hk
    have c3 := seqM_some s3 rfl b2
    have c2 := seqM_some s2 rfl c3
    have c1 := seqM_some s1 rfl c2
    refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, by simp⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega
  · rw [if_neg hge] at hvc hres
    have b1 := pexecM_branch_false mv fu (geC mv.nv L.length im) (yesC mv.nv L.length im) Sk _ _ hvc _ (pexecM_skip mv fu _ _)
    rw [← hres] at hk
    have b2 := seqM_some b1 rfl hk
    have c3 := seqM_some s3 rfl b2
    have c2 := seqM_some s2 rfl c3
    have c1 := seqM_some s1 rfl c2
    refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, by simp⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega

end Proofs.RollingHashCore
