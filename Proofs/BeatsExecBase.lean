import Proofs.BellmanFordPExec
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false cs)

/-- The contents of the 15 member vectors, in declaration order. -/
structure BS where
  mxv : List Int
  smx : List Int
  mxc : List Int
  mnv : List Int
  smn : List Int
  mnc : List Int
  len : List Int
  ladd : List Int
  lval : List Int
  lo : List Int
  hi : List Int
  sk : List Int
  sl : List Int
  sr : List Int
  ent : List Int

/-- Vector number `k` of the state. -/
def VVB (b : BS) : Nat → List Int := fun k =>
  if k = 0 then b.mxv else   if k = 1 then b.smx else   if k = 2 then b.mxc else   if k = 3 then b.mnv else   if k = 4 then b.smn else   if k = 5 then b.mnc else   if k = 6 then b.len else   if k = 7 then b.ladd else   if k = 8 then b.lval else   if k = 9 then b.lo else   if k = 10 then b.hi else   if k = 11 then b.sk else   if k = 12 then b.sl else   if k = 13 then b.sr else   if k = 14 then b.ent else []

theorem VVB_get0 (b : BS) : VVB b 0 = b.mxv := by simp [VVB]
theorem VVB_get1 (b : BS) : VVB b 1 = b.smx := by simp [VVB]
theorem VVB_get2 (b : BS) : VVB b 2 = b.mxc := by simp [VVB]
theorem VVB_get3 (b : BS) : VVB b 3 = b.mnv := by simp [VVB]
theorem VVB_get4 (b : BS) : VVB b 4 = b.smn := by simp [VVB]
theorem VVB_get5 (b : BS) : VVB b 5 = b.mnc := by simp [VVB]
theorem VVB_get6 (b : BS) : VVB b 6 = b.len := by simp [VVB]
theorem VVB_get7 (b : BS) : VVB b 7 = b.ladd := by simp [VVB]
theorem VVB_get8 (b : BS) : VVB b 8 = b.lval := by simp [VVB]
theorem VVB_get9 (b : BS) : VVB b 9 = b.lo := by simp [VVB]
theorem VVB_get10 (b : BS) : VVB b 10 = b.hi := by simp [VVB]
theorem VVB_get11 (b : BS) : VVB b 11 = b.sk := by simp [VVB]
theorem VVB_get12 (b : BS) : VVB b 12 = b.sl := by simp [VVB]
theorem VVB_get13 (b : BS) : VVB b 13 = b.sr := by simp [VVB]
theorem VVB_get14 (b : BS) : VVB b 14 = b.ent := by simp [VVB]

theorem VVB_upd0 (b : BS) (x : List Int) : upd (VVB b) 0 x = VVB { b with mxv := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 0
  · subst h; simp
  · simp [h]

theorem VVB_upd1 (b : BS) (x : List Int) : upd (VVB b) 1 x = VVB { b with smx := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 1
  · subst h; simp
  · simp [h]

theorem VVB_upd2 (b : BS) (x : List Int) : upd (VVB b) 2 x = VVB { b with mxc := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 2
  · subst h; simp
  · simp [h]

theorem VVB_upd3 (b : BS) (x : List Int) : upd (VVB b) 3 x = VVB { b with mnv := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 3
  · subst h; simp
  · simp [h]

theorem VVB_upd4 (b : BS) (x : List Int) : upd (VVB b) 4 x = VVB { b with smn := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 4
  · subst h; simp
  · simp [h]

theorem VVB_upd5 (b : BS) (x : List Int) : upd (VVB b) 5 x = VVB { b with mnc := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 5
  · subst h; simp
  · simp [h]

theorem VVB_upd6 (b : BS) (x : List Int) : upd (VVB b) 6 x = VVB { b with len := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 6
  · subst h; simp
  · simp [h]

theorem VVB_upd7 (b : BS) (x : List Int) : upd (VVB b) 7 x = VVB { b with ladd := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 7
  · subst h; simp
  · simp [h]

theorem VVB_upd8 (b : BS) (x : List Int) : upd (VVB b) 8 x = VVB { b with lval := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 8
  · subst h; simp
  · simp [h]

theorem VVB_upd9 (b : BS) (x : List Int) : upd (VVB b) 9 x = VVB { b with lo := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 9
  · subst h; simp
  · simp [h]

theorem VVB_upd10 (b : BS) (x : List Int) : upd (VVB b) 10 x = VVB { b with hi := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 10
  · subst h; simp
  · simp [h]

theorem VVB_upd11 (b : BS) (x : List Int) : upd (VVB b) 11 x = VVB { b with sk := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 11
  · subst h; simp
  · simp [h]

theorem VVB_upd12 (b : BS) (x : List Int) : upd (VVB b) 12 x = VVB { b with sl := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 12
  · subst h; simp
  · simp [h]

theorem VVB_upd13 (b : BS) (x : List Int) : upd (VVB b) 13 x = VVB { b with sr := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 13
  · subst h; simp
  · simp [h]

theorem VVB_upd14 (b : BS) (x : List Int) : upd (VVB b) 14 x = VVB { b with ent := x } := by
  funext k
  unfold upd VVB
  by_cases h : k = 14
  · subst h; simp
  · simp [h]

end Proofs.BeatsExec
