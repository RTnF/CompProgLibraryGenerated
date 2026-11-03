import Proofs.BeatsCtorIter
import Proofs.BeatsLoopExec
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

/-- The first loop of the constructor. -/
abbrev CtLoop1 (o : Nat) : Command :=
  .whileLoop (.binary bT .lt (.variable i32 (o + 3)) (.binary i32 .mul (.literal i32 4) (.variable i32 (o + 1))))
    (.sequence (.scope (CtLoopBody o)) Sk)

theorem ct_cond (mv : MV) (hnv : mv.nv = 16) (P pre : List Cell) (vv : Nat → List Int) (inf : Int) (n ne k : Nat)
    (hn : 4 * n < M31) (hk : k < M31) :
    vdenM mv vv (penvN mv.nv (gS P (pre ++ CtCells inf n ne k)))
      (.binary bT .lt (.variable i32 (mv.nv + pre.length + 3)) (.binary i32 .mul (.literal i32 4) (.variable i32 (mv.nv + pre.length + 1))))
      = some (if (k : Int) < 4 * (n : Int) then 1 else 0) := by
  have h3 : (pre ++ CtCells inf n ne k)[pre.length + 3]? = some (ci k) := cell_at0 pre (CtCells inf n ne k) 3 (ci k) rfl
  have h1 : (pre ++ CtCells inf n ne k)[pre.length + 1]? = some (ci n) := cell_at0 pre (CtCells inf n ne k) 1 (ci n) rfl
  have hn' : n < M31 := by omega
  have hv4 : i32.valid (4 * (n : Int)) = true := by simp only [Ty.valid, i32]; simp; unfold M31 at *; omega
  refine den_cmpw mv vv _ .lt _ _ (k : Int) (4 * (n : Int)) ((k : Int) < 4 * (n : Int)) (lt_conv _ _) ?_ ?_ rfl rfl
  · exact den_cellvar_t mv P _ i32 (pre.length + 3) _ (by omega) (k : Int) h3 (Proofs.BellmanFordExec.i32_valid_nat k hk) vv
  · have := den_binw mv vv (penvN mv.nv (gS P (pre ++ CtCells inf n ne k))) i32 .mul (.literal i32 4) (.variable i32 (mv.nv + pre.length + 1)) 4 (n : Int)
      (den_lit32 mv vv _ 4 (by decide))
      (den_cellvar_t mv P _ i32 (pre.length + 1) _ (by omega) (n : Int) h1 (Proofs.BellmanFordExec.i32_valid_nat n hn') vv)
      (by simp [NExpr.scalarOnly]) (by simp [NExpr.scalarOnly]) (conv_i32 _ (by simpa [binaryValue] using hv4))
    simpa [binaryValue] using this


theorem ct_loop (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (inf : Int) (hinfI : inf = INF) (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31)
    (hAlen : a.length = n) (hAv : ∀ w ∈ a, s64.valid w = true) :
    ∀ (d ne k : Nat) (b : BS), k + d = 4 * n → CtInv a n inf b k ne → ValidOK b → Lens b L → L ≤ b.lo.length → L ≤ b.hi.length →
      ∃ (bf : BS) (nef F : Nat) (r : PRM), F ≤ d + 1 ∧
        pexecM mv F (CtLoop1 (mv.nv + pre.length)) (gS P (pre ++ CtCells inf n ne k)) (VVA a b) = some r ∧ r.ret = none ∧
        r.ps = gS P (pre ++ CtCells inf n nef (4 * n)) ∧ r.vv = VVA a bf ∧ r.cost ≤ d * 20620 + 20 ∧ r.wk ≤ d * 12 ∧
        CtInv a n inf bf (4 * n) nef ∧ ValidOK bf ∧ Lens bf L ∧ L ≤ bf.lo.length ∧ L ≤ bf.hi.length := by
  have hM : M31 = 2147483648 := rfl
  intro d
  induction d with
  | zero =>
    intro ne k b hk hI hV hLens hlo hhi
    have hk' : k = 4 * n := by omega
    subst hk'
    have hc := ct_cond mv hnv P pre (VVA a b) inf n ne (4 * n) (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    refine ⟨b, ne, 1, _, le_refl _, while_exit_p mv 0 _ _ _ _ hc, rfl, rfl, rfl, ?_, ?_, hI, hV, hLens, hlo, hhi⟩
    · simp [vwp, NExpr.nodes]
    · simp
  | succ d ih =>
    intro ne k b hk hI hV hLens hlo hhi
    have hkn : k < 4 * n := by omega
    obtain ⟨b1, hI1, hLens1, hlo1, hhi1, hV1, hit⟩ :=
      ct_iter mv hnv pre hty hty32 hty15 P inf hinfI a n ne k L b hI hV hLens hlo hhi hn hL8 hLM hkn hAlen hAv
    obtain ⟨bf, nef, F, r2, hF, h2, hr2, hp2, hv2, hc2, hw2, hIf, hVf, hLf, hlof, hhif⟩ :=
      ih (ne + (if isInnerAt n k then 1 else 0)) (k + 1) b1 (by omega) hI1 hV1 hLens1 hlo1 hhi1
    obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hit (F + 1)
    have hc := ct_cond mv hnv P pre (VVA a b) inf n ne k (by omega) (by omega)
    rw [if_pos (by omega)] at hc
    have h2' : pexecM mv F (CtLoop1 (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2
    refine ⟨bf, nef, F + 1, _, by omega, while_step_p mv F _ _ _ _ hc r1 r2 h1 hr1 h2', hr2, hp2, hv2, ?_, ?_, hIf, hVf, hLf, hlof, hhif⟩
    · simp [vwp, NExpr.nodes]; omega
    · simp; omega

end Proofs.BeatsRep
