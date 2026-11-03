import Proofs.MultiKit
namespace Proofs.BeatsRep
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit

/-- The scalar-state size. -/
def szP (ps : PS) : Nat := ps.mem.length + ps.bs.length

/-- The extra `need` a statement can add on top of the current state size. -/
def exS : NStmt → Nat
  | .declare _ _ e => (vwp e).2 + 4
  | .assign _ _ e => (vwp e).2 + 2
  | .ret e => (vwp e).2 + 2
  | .check e => (vwp e).2 + 2
  | .write _ _ iE vE => iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5
  | .sortVec _ _ => 3
  | .dedupVec _ _ => 3
  | _ => 0

def grS : NStmt → Nat
  | .declare _ _ _ => 2
  | _ => 0

def grC : Command → Nat
  | .primitive st => grS st
  | .sequence a b => grC a + grC b
  | .scope _ => 0
  | .branch _ y n => max (grC y) (grC n)
  | _ => 0

def Nb : Command → Nat
  | .primitive st => exS st
  | .sequence a b => max (Nb a) (grC a + Nb b)
  | .scope b => Nb b
  | .branch c y n => max ((vwp c).2 + 2) (max (Nb y) (Nb n))
  | .whileLoop c b => max ((vwp c).2 + 2) (Nb b)
  | _ => 0

def Wf : Command → Bool
  | .primitive _ => true
  | .sequence a b => Wf a && Wf b
  | .scope b => Wf b
  | .branch _ y n => Wf y && Wf n
  | .whileLoop _ b => grC b == 0 && Wf b
  | _ => true

theorem prim_need (mv : MV) (st : NStmt) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (h : pstmtM mv st ps vv = some r) : r.need ≤ szP ps + exS st ∧ szP r.ps ≤ szP ps + grS st := by
  cases st with
  | declare ty w e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    cases h; simp [szP, exS, grS]; omega
  | assign s ty e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    obtain ⟨_, rfl⟩ := h; simp [szP, exS, grS]; try omega
  | ret e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    cases h; simp [szP, exS, grS]; omega
  | check e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    obtain ⟨_, rfl⟩ := h; simp [szP, exS, grS]; try omega
  | skip => simp [pstmtM] at h; cases h; simp [szP, exS, grS]
  | write c ty iE vE =>
    obtain ⟨h1, h2⟩ := pstmtM_write_inv mv c ty iE vE ps vv r h
    rw [h2, h1]; simp [szP, exS, grS]; try omega
  | sortVec c ty =>
    obtain ⟨h1, h2⟩ := pstmtM_sort_inv mv c ty ps vv r h
    rw [h2, h1]; simp [szP, exS, grS]; try omega
  | dedupVec c ty =>
    obtain ⟨h1, h2⟩ := pstmtM_dedup_inv mv c ty ps vv r h
    rw [h2, h1]; simp [szP, exS, grS]; try omega
  | _ => simp [pstmtM] at h


theorem cmd_need (mv : MV) : ∀ (c : Command), Wf c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM),
    pexecM mv fu c ps vv = some r → r.need ≤ szP ps + Nb c ∧ szP r.ps ≤ szP ps + grC c := by
  intro c
  induction c with
  | primitive st =>
    intro _ fu ps vv r h
    rw [pexecM] at h
    exact prim_need mv st ps vv r h
  | sequence a b iha ihb =>
    intro hw fu ps vv r h
    simp only [Wf, Bool.and_eq_true] at hw
    cases h1 : pexecM mv fu a ps vv with
    | none => rw [pexecM_seq, h1] at h; simp at h
    | some r1 =>
      have i1 := iha hw.1 fu ps vv r1 h1
      rw [pexecM_seq, h1] at h
      simp only [Bind.bind, Option.bind] at h
      cases hr : r1.ret with
      | some v => simp only [hr] at h; cases h; simp only [Nb, grC]; constructor <;> omega
      | none =>
        simp only [hr] at h
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at h
        | some r2 =>
          simp only [h2] at h
          cases h
          have i2 := ihb hw.2 fu r1.ps r1.vv r2 h2
          simp only [Nb, grC]
          constructor <;> omega
  | scope body ih =>
    intro hw fu ps vv r h
    simp only [Wf] at hw
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at h
    | some r1 =>
      simp only [h1] at h
      cases h
      have i1 := ih hw fu ps vv r1 h1
      simp only [Nb, grC, szP] at i1 ⊢
      constructor
      · omega
      · simp; omega
  | branch cnd y n ihy ihn =>
    intro hw fu ps vv r h
    simp only [Wf, Bool.and_eq_true] at hw
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv ps) cnd with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      by_cases hz : v = 0
      · simp only [hz, if_true] at h
        cases h1 : pexecM mv fu n ps vv with
        | none => simp [h1] at h
        | some r1 =>
          simp only [h1] at h
          cases h
          have i1 := ihn hw.2 fu ps vv r1 h1
          simp only [Nb, grC, szP] at i1 ⊢
          constructor <;> (try simp) <;> omega
      · simp only [hz, if_false] at h
        cases h1 : pexecM mv fu y ps vv with
        | none => simp [h1] at h
        | some r1 =>
          simp only [h1] at h
          cases h
          have i1 := ihy hw.1 fu ps vv r1 h1
          simp only [Nb, grC, szP] at i1 ⊢
          constructor <;> (try simp) <;> omega
  | whileLoop cnd body ih =>
    intro hw fu
    simp only [Wf, Bool.and_eq_true, beq_iff_eq] at hw
    induction fu with
    | zero => intro ps vv r h; simp [pexecM] at h
    | succ f ihf =>
      intro ps vv r h
      rw [pexecM_while] at h
      simp only [Bind.bind, Option.bind] at h
      cases hv : vdenM mv vv (penvN mv.nv ps) cnd with
      | none => simp [hv] at h
      | some v =>
        simp only [hv] at h
        by_cases hz : v = 0
        · simp only [hz, if_true] at h
          cases h; simp only [Nb, grC, szP]; constructor <;> (try simp) <;> omega
        · simp only [hz, if_false] at h
          cases h1 : pexecM mv (f+1) body ps vv with
          | none => simp [h1] at h
          | some r1 =>
            simp only [h1] at h
            cases hr : r1.ret with
            | some w => simp [hr] at h
            | none =>
              simp only [hr] at h
              cases h2 : pexecM mv f (.whileLoop cnd body) r1.ps r1.vv with
              | none => simp [h2] at h
              | some r2 =>
                simp only [h2] at h
                cases h
                have i1 := ih hw.2 (f+1) ps vv r1 h1
                have i2 := ihf r1.ps r1.vv r2 h2
                simp only [Nb, grC, szP] at i1 i2 ⊢
                rw [hw.1] at i1
                constructor <;> (try simp) <;> omega
  | breakLoop => intro _ fu ps vv r h; simp [pexecM] at h
  | invokeScalar p args => intro _ fu ps vv r h; simp [pexecM] at h

end Proofs.BeatsRep

namespace Proofs.BeatsRep
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit

/-- The vector `k` is never written by the statement. -/
def noWrS (k : Nat) : NStmt → Bool
  | .write (.local j) _ _ _ => j != k
  | .sortVec (.local j) _ => j != k
  | .dedupVec (.local j) _ => j != k
  | _ => true

def noWr (k : Nat) : Command → Bool
  | .primitive st => noWrS k st
  | .sequence a b => noWr k a && noWr k b
  | .scope b => noWr k b
  | .branch _ y n => noWr k y && noWr k n
  | .whileLoop _ b => noWr k b
  | _ => true

theorem prim_vec (mv : MV) (k : Nat) (st : NStmt) (hn : noWrS k st = true) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (h : pstmtM mv st ps vv = some r) : r.vv k = vv k := by
  cases st with
  | declare ty w e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    cases h; rfl
  | assign s ty e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    obtain ⟨_, rfl⟩ := h; rfl
  | ret e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    cases h; rfl
  | check e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    obtain ⟨_, rfl⟩ := h; rfl
  | skip => simp [pstmtM] at h; cases h; rfl
  | write c ty iE vE =>
    cases c with
    | «local» j =>
      simp only [noWrS, bne_iff_ne, ne_eq] at hn
      simp only [pstmtM, Bind.bind, Option.bind] at h
      cases hv : vdenM mv vv (penvN mv.nv ps) vE with
      | none => simp [hv] at h
      | some x =>
        simp only [hv] at h
        cases hi : vdenM mv vv (penvN mv.nv ps) iE with
        | none => simp [hi] at h
        | some p =>
          simp only [hi] at h
          by_cases ok : j < mv.nv ∧ ty = mv.ty j ∧ 0 ≤ p ∧ p.toNat < (vv j).length ∧ (mv.ty j).valid x = true
          · rw [if_pos ok] at h; cases h; simp [upd]; intro hh; exact absurd hh.symm hn
          · rw [if_neg ok] at h; simp at h
    | row _ _ _ => simp [pstmtM] at h
  | sortVec c ty =>
    cases c with
    | «local» j =>
      simp only [noWrS, bne_iff_ne, ne_eq] at hn
      simp only [pstmtM] at h
      by_cases ok : j < mv.nv ∧ ty = mv.ty j
      · rw [if_pos ok] at h; cases h; simp [upd]; intro hh; exact absurd hh.symm hn
      · rw [if_neg ok] at h; simp at h
    | row _ _ _ => simp [pstmtM] at h
  | dedupVec c ty =>
    cases c with
    | «local» j =>
      simp only [noWrS, bne_iff_ne, ne_eq] at hn
      simp only [pstmtM] at h
      by_cases ok : j < mv.nv ∧ ty = mv.ty j
      · rw [if_pos ok] at h; cases h; simp [upd]; intro hh; exact absurd hh.symm hn
      · rw [if_neg ok] at h; simp at h
    | row _ _ _ => simp [pstmtM] at h
  | _ => simp [pstmtM] at h

theorem cmd_vec (mv : MV) (k : Nat) : ∀ (c : Command), noWr k c = true → ∀ (fu : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM),
    pexecM mv fu c ps vv = some r → r.vv k = vv k := by
  intro c
  induction c with
  | primitive st =>
    intro hn fu ps vv r h
    rw [pexecM] at h
    exact prim_vec mv k st hn ps vv r h
  | sequence a b iha ihb =>
    intro hn fu ps vv r h
    simp only [noWr, Bool.and_eq_true] at hn
    cases h1 : pexecM mv fu a ps vv with
    | none => rw [pexecM_seq, h1] at h; simp at h
    | some r1 =>
      have i1 := iha hn.1 fu ps vv r1 h1
      rw [pexecM_seq, h1] at h
      simp only [Bind.bind, Option.bind] at h
      cases hr : r1.ret with
      | some v => simp only [hr] at h; cases h; exact i1
      | none =>
        simp only [hr] at h
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at h
        | some r2 =>
          simp only [h2] at h
          cases h
          have i2 := ihb hn.2 fu r1.ps r1.vv r2 h2
          show r2.vv k = vv k
          rw [i2, i1]
  | scope body ih =>
    intro hn fu ps vv r h
    simp only [noWr] at hn
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases h1 : pexecM mv fu body ps vv with
    | none => simp [h1] at h
    | some r1 => simp only [h1] at h; cases h; exact ih hn fu ps vv r1 h1
  | branch cnd y n ihy ihn =>
    intro hn fu ps vv r h
    simp only [noWr, Bool.and_eq_true] at hn
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv ps) cnd with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      by_cases hz : v = 0
      · simp only [hz, ite_true] at h
        cases h1 : pexecM mv fu n ps vv with
        | none => simp [h1] at h
        | some r1 => simp only [h1] at h; cases h; exact ihn hn.2 fu ps vv r1 h1
      · simp only [hz, ite_false] at h
        cases h1 : pexecM mv fu y ps vv with
        | none => simp [h1] at h
        | some r1 => simp only [h1] at h; cases h; exact ihy hn.1 fu ps vv r1 h1
  | whileLoop cnd body ih =>
    intro hn fu
    simp only [noWr] at hn
    induction fu with
    | zero => intro ps vv r h; simp [pexecM] at h
    | succ f ihf =>
      intro ps vv r h
      rw [pexecM_while] at h
      simp only [Bind.bind, Option.bind] at h
      cases hv : vdenM mv vv (penvN mv.nv ps) cnd with
      | none => simp [hv] at h
      | some v =>
        simp only [hv] at h
        by_cases hz : v = 0
        · simp only [hz, ite_true] at h; cases h; rfl
        · simp only [hz, ite_false] at h
          cases h1 : pexecM mv (f+1) body ps vv with
          | none => simp [h1] at h
          | some r1 =>
            simp only [h1] at h
            cases hr : r1.ret with
            | some w => simp [hr] at h
            | none =>
              simp only [hr] at h
              cases h2 : pexecM mv f (.whileLoop cnd body) r1.ps r1.vv with
              | none => simp [h2] at h
              | some r2 =>
                simp only [h2] at h
                cases h
                have i1 := ih hn (f+1) ps vv r1 h1
                have i2 := ihf r1.ps r1.vv r2 h2
                show r2.vv k = vv k
                rw [i2, i1]
  | breakLoop => intro _ fu ps vv r h; simp [pexecM] at h
  | invokeScalar p args => intro _ fu ps vv r h; simp [pexecM] at h

end Proofs.BeatsRep
