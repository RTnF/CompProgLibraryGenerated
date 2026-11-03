import Proofs.BeatsRep
import Proofs.BeatsSafe
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)

theorem s64_valid_of_bounds (v : Int) (h1 : -(2 * INF) < v) (h2 : v < 2 * INF) : s64.valid v = true := by
  unfold INF at h1 h2
  show Ty.valid ⟨64, true, false⟩ v = true
  simp [Ty.valid]
  omega

/-- Array indices touched by the loop body stay inside the arrays (depends only on the skeleton). -/
def IdxOKs : Sk → Nat → Nat → Prop
  | .leaf, k, L => 2 * k + 2 < L
  | .node l r, k, L => 2 * k + 2 < L ∧ IdxOKs l (2 * k + 1) L ∧ IdxOKs r (2 * k + 2) L

abbrev IdxOK (t : BT) (k L : Nat) : Prop := IdxOKs t.skel k L

/-- The `len` array holds the lengths of the ranges. -/
def LenOKs (b : BS) : Sk → Nat → Nat → Nat → Prop
  | .leaf, k, lo, hi => b.len.getD k 0 = ((hi - lo : Nat) : Int)
  | .node l r, k, lo, hi =>
    b.len.getD k 0 = ((hi - lo : Nat) : Int) ∧ LenOKs b l (2 * k + 1) lo ((lo + hi) / 2) ∧ LenOKs b r (2 * k + 2) ((lo + hi) / 2) hi

abbrev LenOK (b : BS) (t : BT) (k lo hi : Nat) : Prop := LenOKs b t.skel k lo hi

theorem LenOK_root {b : BS} {t : BT} {k lo hi : Nat} (h : LenOK b t k lo hi) : b.len.getD k 0 = ((hi - lo : Nat) : Int) := by
  cases t with
  | leaf nd => exact h
  | node nd tg l r => exact h.1

def nodesS : Sk → Nat
  | .leaf => 1
  | .node l r => nodesS l + nodesS r + 1

def innerS : Sk → Nat
  | .leaf => 0
  | .node l r => innerS l + innerS r + 1

abbrev nodesOf (t : BT) : Nat := nodesS t.skel
abbrev innerOf (t : BT) : Nat := innerS t.skel

/-- The cell of node `k` describes the tree `t` (node summary and tag; a leaf has no tag). -/
theorem cell_of_agree (inf : Int) (b : BS) (H : Heap) (hH : HRel inf b H) (t : BT) (k lo hi : Nat) (hag : Agree H t k)
    (hsh : Shape lo hi t.skel) (hl : LenOK b t k lo hi) :
    decNd b k = t.nd ∧ decTag inf b k = ({ lval := t.lval, ladd := t.ladd } : Tag) := by
  obtain ⟨h1, h2, h3⟩ := hH k
  cases t with
  | leaf nd =>
    have hl' : b.len.getD k 0 = 1 := by
      have : hi = lo + 1 := hsh
      rw [hl, this]; simp
    have := (agree_leaf H nd k).mp hag
    refine ⟨by rw [h1, this]; rfl, ?_⟩
    rw [h3 hl']
    simp [noTag, BT.lval, BT.ladd]
  | node nd tg l r =>
    obtain ⟨hlo, _, _⟩ := hsh
    have hl' : b.len.getD k 0 ≠ 1 := by
      have := hl.1
      intro h
      rw [h] at this
      omega
    have := (agree_node H nd tg l r k).mp hag
    refine ⟨by rw [h1, this.1]; rfl, ?_⟩
    rw [h2 hl', this.1]
    simp [BT.lval, BT.ladd]

theorem child_cell_sums (inf : Int) (hinfI : inf = INF) (b : BS) (idx : Nat) (c : BT) (xc : List Int) (a : Int) (hc : Inv c xc)
    (hN : decNd b idx = c.nd) (hT : decTag inf b idx = ({ lval := c.lval, ladd := c.ladd } : Tag))
    (hra : ∀ w ∈ xc, -INF < w + a ∧ w + a < INF)
    (hov1 : ∀ v, c.lval = some v → -INF < v + a ∧ v + a < INF)
    (hov2 : c.lval = none → ∀ w ∈ c.kids, -INF < w + (c.ladd + a) ∧ w + (c.ladd + a) < INF) :
    s64.valid (b.mxv.getD idx 0 + a) = true ∧
    (b.smx.getD idx 0 ≠ -inf → s64.valid (b.smx.getD idx 0 + a) = true) ∧
    s64.valid (b.mnv.getD idx 0 + a) = true ∧
    (b.smn.getD idx 0 ≠ inf → s64.valid (b.smn.getD idx 0 + a) = true) ∧
    ((b.lval.getD idx 0 = inf ∧ b.len.getD idx 0 ≠ 1) → s64.valid (b.ladd.getD idx 0 + a) = true) ∧
    (b.lval.getD idx 0 ≠ inf → s64.valid (b.lval.getD idx 0 + a) = true) ∧
    (b.lval.getD idx 0 ≠ inf → b.lval.getD idx 0 + a ≠ inf) := by
  subst hinfI
  obtain ⟨hmx, hmn, hsmx, hsmn, hla, hlv⟩ := child_bounds c xc hc a hra hov1 hov2
  have e1 : b.mxv.getD idx 0 = c.nd.mx := by have := congrArg Nd.mx hN; simpa [decNd] using this
  have e2 : b.smx.getD idx 0 = c.nd.smx := by have := congrArg Nd.smx hN; simpa [decNd] using this
  have e3 : b.mnv.getD idx 0 = c.nd.mn := by have := congrArg Nd.mn hN; simpa [decNd] using this
  have e4 : b.smn.getD idx 0 = c.nd.smn := by have := congrArg Nd.smn hN; simpa [decNd] using this
  have e5 : b.ladd.getD idx 0 = c.ladd := by have := congrArg Tag.ladd hT; simpa [decTag] using this
  have e6 : (if b.lval.getD idx 0 = INF then none else some (b.lval.getD idx 0)) = c.lval := by
    have := congrArg Tag.lval hT; simpa [decTag] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; apply s64_valid_of_bounds <;> omega
  · intro h; rw [e2] at h ⊢; have := hsmx h; apply s64_valid_of_bounds <;> omega
  · rw [e3]; apply s64_valid_of_bounds <;> omega
  · intro h; rw [e4] at h ⊢; have := hsmn h; apply s64_valid_of_bounds <;> omega
  · intro ⟨h7, _⟩
    rw [h7] at e6
    simp at e6
    rw [e5]
    have := hla e6.symm
    apply s64_valid_of_bounds <;> omega
  · intro h
    rw [if_neg h] at e6
    have := hov1 _ e6.symm
    apply s64_valid_of_bounds <;> omega
  · intro h
    rw [if_neg h] at e6
    have := hov1 _ e6.symm
    omega

/-- The arrays that the loop touches have at least `L` entries. -/
structure Lens (b : BS) (L : Nat) : Prop where
  l0 : L ≤ b.mxv.length
  l1 : L ≤ b.smx.length
  l2 : L ≤ b.mxc.length
  l3 : L ≤ b.mnv.length
  l4 : L ≤ b.smn.length
  l5 : L ≤ b.mnc.length
  l6 : L ≤ b.len.length
  l7 : L ≤ b.ladd.length
  l8 : L ≤ b.lval.length
  lsk : L ≤ b.sk.length
  lsl : L ≤ b.sl.length
  lsr : L ≤ b.sr.length
  lent : L ≤ b.ent.length

theorem Lens_of_same {b b' : BS} {L : Nat} (h : Lens b L) (hs : SameLen b b') : Lens b' L :=
  ⟨by rw [hs.l0]; exact h.l0, by rw [hs.l1]; exact h.l1, by rw [hs.l2]; exact h.l2, by rw [hs.l3]; exact h.l3,
   by rw [hs.l4]; exact h.l4, by rw [hs.l5]; exact h.l5, by rw [hs.l6]; exact h.l6, by rw [hs.l7]; exact h.l7,
   by rw [hs.l8]; exact h.l8, by rw [hs.l11]; exact h.lsk, by rw [hs.l12]; exact h.lsl, by rw [hs.l13]; exact h.lsr,
   by rw [hs.l14]; exact h.lent⟩

theorem mk_ctx (b : BS) (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (W0 W1 W2 L : Nat) (hinf : s64.valid inf = true)
    (hninf : s64.valid (-inf) = true) (hnM : n < Proofs.BellmanFordExec.M31) (hopM : op < Proofs.BellmanFordExec.M31)
    (hqaM : qa < Proofs.BellmanFordExec.M31) (hqbM : qb < Proofs.BellmanFordExec.M31) (hx : s64.valid x = true)
    (hV : ValidOK b) (hLens : Lens b L) (hLM : L < Proofs.BellmanFordExec.M31) (hk : 2 * W0 + 2 < L) (hsp : 0 < sp)
    (hspL : sp + 2 ≤ L) (hneL : ne + 1 < L) (hlohi : W1 + W2 < Proofs.BellmanFordExec.M31) :
    IterCtx b inf n op qa qb sp ne x W0 W1 W2 :=
  ⟨hinf, hninf, hnM, hopM, hqaM, hqbM, by omega, by omega, hsp, hx, hV, by omega, by omega, by omega, by omega, hlohi,
   by omega, by omega,
   by have := hLens.l0; omega, by have := hLens.l1; omega, by have := hLens.l2; omega, by have := hLens.l3; omega,
   by have := hLens.l4; omega, by have := hLens.l5; omega, by have := hLens.l6; omega, by have := hLens.l7; omega,
   by have := hLens.l8; omega, by have := hLens.lsk; omega, by have := hLens.lsl; omega, by have := hLens.lsr; omega,
   by have := hLens.lent; omega⟩

end Proofs.BeatsRep
