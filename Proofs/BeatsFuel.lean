import Proofs.BeatsExecBase
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB

/-- More fuel never changes a successful run. -/
theorem pexecM_succ (mv : MV) : ∀ (c : Command) (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM),
    pexecM mv fu c ps vv = some r → pexecM mv (fu + 1) c ps vv = some r := by
  intro c
  induction c with
  | primitive st =>
    intro fu ps vv r h
    rw [pexecM_prim] at h ⊢; exact h
  | sequence a b iha ihb =>
    intro fu ps vv r h
    rw [pexecM_seq] at h ⊢
    cases h1 : pexecM mv fu a ps vv with
    | none => rw [h1] at h; simp [Bind.bind, Option.bind] at h
    | some r1 =>
      rw [h1] at h
      rw [iha _ _ _ _ h1]
      cases hr : r1.ret with
      | some v => simpa [Bind.bind, Option.bind, hr] using h
      | none =>
        simp only [Bind.bind, Option.bind, hr] at h ⊢
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => rw [h2] at h; simp at h
        | some r2 => rw [h2] at h; rw [ihb _ _ _ _ h2]; exact h
  | scope body ih =>
    intro fu ps vv r h
    have : ∃ r0, pexecM mv fu body ps vv = some r0 := by
      rw [pexecM] at h
      cases h0 : pexecM mv fu body ps vv with
      | none => rw [h0] at h; simp [Bind.bind, Option.bind] at h
      | some r0 => exact ⟨r0, rfl⟩
    obtain ⟨r0, h0⟩ := this
    rw [pexecM_scope mv fu body ps vv r0 h0] at h
    rw [pexecM_scope mv (fu + 1) body ps vv r0 (ih _ _ _ _ h0)]; exact h
  | branch c y n ihy ihn =>
    intro fu ps vv r h
    rw [pexecM] at h ⊢
    cases hv : vdenM mv vv (penvN mv.nv ps) c with
    | none => rw [hv] at h; simp [Bind.bind, Option.bind] at h
    | some v =>
      rw [hv] at h
      simp only [Bind.bind, Option.bind] at h ⊢
      by_cases h0 : v = 0
      · rw [if_pos h0] at h ⊢
        cases h1 : pexecM mv fu n ps vv with
        | none => rw [h1] at h; simp at h
        | some r1 => rw [h1] at h; rw [ihn _ _ _ _ h1]; exact h
      · rw [if_neg h0] at h ⊢
        cases h1 : pexecM mv fu y ps vv with
        | none => rw [h1] at h; simp at h
        | some r1 => rw [h1] at h; rw [ihy _ _ _ _ h1]; exact h
  | whileLoop c body ih =>
    intro fu
    induction fu with
    | zero => intro ps vv r h; rw [pexecM] at h; simp at h
    | succ fu ihf =>
      intro ps vv r h
      rw [pexecM_while] at h ⊢
      cases hv : vdenM mv vv (penvN mv.nv ps) c with
      | none => rw [hv] at h; simp [Bind.bind, Option.bind] at h
      | some v =>
        rw [hv] at h
        simp only [Bind.bind, Option.bind] at h ⊢
        by_cases h0 : v = 0
        · rw [if_pos h0] at h ⊢; exact h
        · rw [if_neg h0] at h ⊢
          cases h1 : pexecM mv (fu + 1) body ps vv with
          | none => rw [h1] at h; simp at h
          | some r1 =>
            rw [h1] at h
            rw [ih _ _ _ _ h1]
            simp only [Bind.bind, Option.bind] at h ⊢
            cases hr : r1.ret with
            | some _ => rw [hr] at h; simp at h
            | none =>
              rw [hr] at h
              simp only [hr]
              cases h2 : pexecM mv fu (.whileLoop c body) r1.ps r1.vv with
              | none => rw [h2] at h; simp at h
              | some r2 => rw [h2] at h; rw [ihf _ _ _ h2]; exact h
  | breakLoop =>
    intro fu ps vv r h
    simp [pexecM] at h
  | invokeScalar p a =>
    intro fu ps vv r h
    simp [pexecM] at h

theorem pexecM_mono (mv : MV) (c : Command) (ps : PS) (vv : Nat → List Int) (r : PRM) :
    ∀ (fu k : Nat), pexecM mv fu c ps vv = some r → pexecM mv (fu + k) c ps vv = some r := by
  intro fu k
  induction k with
  | zero => exact id
  | succ k ih => intro h; exact pexecM_succ mv c _ ps vv r (ih h)

end Proofs.BeatsExec
