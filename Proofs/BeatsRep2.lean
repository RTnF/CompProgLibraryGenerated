import Proofs.BeatsMethods
import Proofs.BeatsCalcMethods
import Proofs.BeatsTravProps
import Proofs.BeatsCtorTop
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.BellmanFordExec (M31)

/-- The tree `t` (with its heap image `H`) and the vectors `b` represent the array `ys` of length `n`. -/
structure BRep (n L : Nat) (ys : List Int) (b : BS) (t : BT) (H : Heap) : Prop where
  agree : Agree H t 0
  shape : Shape 0 n t.skel
  leaf : LeafOK t
  inv : BeatsModel.Inv t ys
  hrel : HRel INF b H
  valid : ValidOK b
  lens : Lens b L
  idx : IdxOK t 0 L
  lenok : LenOK b t 0 0 n
  sp : 1 + t.height + 2 ≤ L
  ne : innerOf t + 1 < L
  nM : 2 * n < M31

theorem height_eq_of_skel : ∀ (t t' : BT), t.skel = t'.skel → t.height = t'.height
  | .leaf _, .leaf _, _ => rfl
  | .leaf _, .node _ _ _ _, h => by simp [BT.skel] at h
  | .node _ _ _ _, .leaf _, h => by simp [BT.skel] at h
  | .node _ _ l r, .node _ _ l' r', h => by
    simp only [BT.skel, Sk.node.injEq] at h
    simp only [BT.height, height_eq_of_skel l l' h.1, height_eq_of_skel r r' h.2]

/-- A representation survives an operation that keeps the skeleton and the `len` array. -/
theorem BRep.step {n L : Nat} {ys ys' : List Int} {b bf : BS} {t t' : BT} {H Hf : Heap} (R : BRep n L ys b t H)
    (hsk : t'.skel = t.skel) (hleaf : LeafOK t') (hinv : BeatsModel.Inv t' ys') (hag : Agree Hf t' 0)
    (hH : HRel INF bf Hf) (hV : ValidOK bf) (hSL : SameLen b bf) (hlen : bf.len = b.len) : BRep n L ys' bf t' Hf where
  agree := hag
  shape := by rw [hsk]; exact R.shape
  leaf := hleaf
  inv := hinv
  hrel := hH
  valid := hV
  lens := Lens_of_same R.lens hSL
  idx := by unfold IdxOK; rw [hsk]; exact R.idx
  lenok := by
    have h := R.lenok
    unfold LenOK at h ⊢
    rw [hsk]; exact LenOKs_of_eq hlen _ _ _ _ h
  sp := by rw [height_eq_of_skel t' t hsk]; exact R.sp
  ne := by have h := R.ne; unfold innerOf at h ⊢; rw [hsk]; exact h
  nM := R.nM

end Proofs.BeatsRep
