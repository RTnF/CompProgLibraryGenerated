import Proofs.BeatsRep
import Proofs.BeatsExec_CtUpdDefs
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

/-- The state after the six writes of `update` at node `k`. -/
def UCl (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : BS :=
  ul6 (ul5 (ul4 (ul3 (ul2 (ul1 b k a1) k a2) k a3) k a4) k a5) k a6

theorem UCl_mxv (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).mxv = b.mxv.set k a1 := rfl
theorem UCl_mxc (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).mxc = b.mxc.set k a2 := rfl
theorem UCl_smx (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).smx = b.smx.set k a3 := rfl
theorem UCl_mnv (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).mnv = b.mnv.set k a4 := rfl
theorem UCl_mnc (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).mnc = b.mnc.set k a5 := rfl
theorem UCl_smn (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).smn = b.smn.set k a6 := rfl

theorem UCl_decNd_self (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) (h0 : k < b.mxv.length) (h1 : k < b.smx.length)
    (h2 : k < b.mxc.length) (h3 : k < b.mnv.length) (h4 : k < b.smn.length) (h5 : k < b.mnc.length) :
    decNd (UCl b k a1 a2 a3 a4 a5 a6) k = ⟨a1, a3, a2, a4, a6, a5⟩ := by
  unfold decNd
  rw [UCl_mxv, UCl_mxc, UCl_smx, UCl_mnv, UCl_mnc, UCl_smn, getD_set_same _ _ _ h0, getD_set_same _ _ _ h2, getD_set_same _ _ _ h1,
    getD_set_same _ _ _ h3, getD_set_same _ _ _ h5, getD_set_same _ _ _ h4]

theorem UCl_decNd_other (b : BS) (k i : Nat) (a1 a2 a3 a4 a5 a6 : Int) (h : i ≠ k) :
    decNd (UCl b k a1 a2 a3 a4 a5 a6) i = decNd b i := by
  unfold decNd
  rw [UCl_mxv, UCl_mxc, UCl_smx, UCl_mnv, UCl_mnc, UCl_smn, getD_set_diff _ _ _ _ h.symm, getD_set_diff _ _ _ _ h.symm,
    getD_set_diff _ _ _ _ h.symm, getD_set_diff _ _ _ _ h.symm, getD_set_diff _ _ _ _ h.symm, getD_set_diff _ _ _ _ h.symm]

theorem UCl_decTag (inf : Int) (b : BS) (k i : Nat) (a1 a2 a3 a4 a5 a6 : Int) :
    decTag inf (UCl b k a1 a2 a3 a4 a5 a6) i = decTag inf b i := rfl

theorem UCl_len (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).len = b.len := rfl
theorem UCl_ent (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).ent = b.ent := rfl
theorem UCl_sk (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).sk = b.sk := rfl
theorem UCl_sl (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).sl = b.sl := rfl
theorem UCl_sr (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : (UCl b k a1 a2 a3 a4 a5 a6).sr = b.sr := rfl

theorem UCl_sameLen (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) : SameLen b (UCl b k a1 a2 a3 a4 a5 a6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [UCl_mxv]; simp
  · rw [UCl_smx]; simp
  · rw [UCl_mxc]; simp
  · rw [UCl_mnv]; simp
  · rw [UCl_smn]; simp
  · rw [UCl_mnc]; simp

theorem UCl_valid (b : BS) (k : Nat) (a1 a2 a3 a4 a5 a6 : Int) (hV : ValidOK b) (v1 : s64.valid a1 = true) (v2 : s64.valid a2 = true)
    (v3 : s64.valid a3 = true) (v4 : s64.valid a4 = true) (v5 : s64.valid a5 = true) (v6 : s64.valid a6 = true) :
    ValidOK (UCl b k a1 a2 a3 a4 a5 a6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hV.v6, hV.v7, hV.v8, hV.v9, hV.v10, hV.v11, hV.v12, hV.v13, hV.v14⟩
  · rw [UCl_mxv]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v0 v1
  · rw [UCl_smx]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v1 v3
  · rw [UCl_mxc]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v2 v2
  · rw [UCl_mnv]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v3 v4
  · rw [UCl_smn]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v4 v6
  · rw [UCl_mnc]; exact valid_set (fun w => s64.valid w = true) _ _ _ hV.v5 v5

/-- One `update` step on the heap model. -/
theorem HRel_UCl (inf : Int) (b : BS) (H : Heap) (k : Nat) (hH : HRel inf b H) (hk : 2 * k + 2 < b.mxv.length)
    (hk1 : 2 * k + 2 < b.smx.length) (hk2 : 2 * k + 2 < b.mxc.length) (hk3 : 2 * k + 2 < b.mnv.length)
    (hk4 : 2 * k + 2 < b.smn.length) (hk5 : 2 * k + 2 < b.mnc.length) (a1 a2 a3 a4 a5 a6 : Int)
    (hn : (⟨a1, a3, a2, a4, a6, a5⟩ : Nd) = (mergeNd (H (2 * k + 1)).1 (H (2 * k + 2)).1)) :
    HRel inf (UCl b k a1 a2 a3 a4 a5 a6) (updateH H k) := by
  unfold updateH
  refine HRel_set inf b _ H k _ hH (fun i hi => ⟨UCl_decNd_other b k i _ _ _ _ _ _ hi, rfl⟩) rfl ?_ ?_ ?_
  · show decNd _ k = mergeNd _ _
    rw [UCl_decNd_self b k _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hn
  · intro hl; show decTag inf b k = (H k).2; exact ((hH k).2.1 hl)
  · intro hl; exact (hH k).2.2 hl

end Proofs.BeatsRep
