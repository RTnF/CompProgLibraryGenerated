import Proofs.BeatsExecL0
import Proofs.BeatsExecP0
import Proofs.BeatsExecP1
namespace Proofs.BeatsExec
open Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.BellmanFordExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.DoublingNested (i32)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall

theorem s64_of_i32 (v : Int) (h : i32.valid v = true) : s64.valid v = true := by
  simp only [Ty.valid, i32, s64] at h ⊢
  simp at h ⊢
  omega

/-- The vectors of the constructor: the 15 members and the argument `A` (vector 15). -/
def VVA (A : List Int) (b : BS) : Nat → List Int := fun k => if k = 15 then A else VVB b k

theorem VVA_get15 (A : List Int) (b : BS) : VVA A b 15 = A := by simp [VVA]
theorem VVA_get0 (A : List Int) (b : BS) : VVA A b 0 = b.mxv := by simp [VVA, VVB]
theorem VVA_get1 (A : List Int) (b : BS) : VVA A b 1 = b.smx := by simp [VVA, VVB]
theorem VVA_get2 (A : List Int) (b : BS) : VVA A b 2 = b.mxc := by simp [VVA, VVB]
theorem VVA_get3 (A : List Int) (b : BS) : VVA A b 3 = b.mnv := by simp [VVA, VVB]
theorem VVA_get4 (A : List Int) (b : BS) : VVA A b 4 = b.smn := by simp [VVA, VVB]
theorem VVA_get5 (A : List Int) (b : BS) : VVA A b 5 = b.mnc := by simp [VVA, VVB]
theorem VVA_get6 (A : List Int) (b : BS) : VVA A b 6 = b.len := by simp [VVA, VVB]
theorem VVA_get7 (A : List Int) (b : BS) : VVA A b 7 = b.ladd := by simp [VVA, VVB]
theorem VVA_get8 (A : List Int) (b : BS) : VVA A b 8 = b.lval := by simp [VVA, VVB]
theorem VVA_get9 (A : List Int) (b : BS) : VVA A b 9 = b.lo := by simp [VVA, VVB]
theorem VVA_get10 (A : List Int) (b : BS) : VVA A b 10 = b.hi := by simp [VVA, VVB]
theorem VVA_get11 (A : List Int) (b : BS) : VVA A b 11 = b.sk := by simp [VVA, VVB]
theorem VVA_get12 (A : List Int) (b : BS) : VVA A b 12 = b.sl := by simp [VVA, VVB]
theorem VVA_get13 (A : List Int) (b : BS) : VVA A b 13 = b.sr := by simp [VVA, VVB]
theorem VVA_get14 (A : List Int) (b : BS) : VVA A b 14 = b.ent := by simp [VVA, VVB]
theorem VVA_upd0 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 0 x = VVA A { b with mxv := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 0
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd1 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 1 x = VVA A { b with smx := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 1
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd2 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 2 x = VVA A { b with mxc := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 2
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd3 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 3 x = VVA A { b with mnv := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 3
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd4 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 4 x = VVA A { b with smn := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 4
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd5 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 5 x = VVA A { b with mnc := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 5
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd6 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 6 x = VVA A { b with len := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 6
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd7 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 7 x = VVA A { b with ladd := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 7
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd8 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 8 x = VVA A { b with lval := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 8
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd9 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 9 x = VVA A { b with lo := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 9
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd10 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 10 x = VVA A { b with hi := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 10
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd11 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 11 x = VVA A { b with sk := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 11
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd12 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 12 x = VVA A { b with sl := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 12
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd13 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 13 x = VVA A { b with sr := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 13
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]
theorem VVA_upd14 (A : List Int) (b : BS) (x : List Int) : upd (VVA A b) 14 x = VVA A { b with ent := x } := by
  funext k
  unfold upd VVA VVB
  by_cases h : k = 14
  · subst h; simp
  · by_cases h2 : k = 15
    · simp [h2, h]
    · simp [h, h2]

end Proofs.BeatsExec
