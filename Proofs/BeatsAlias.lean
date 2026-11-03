import Proofs.BeatsNeed
namespace Proofs.BeatsRep
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch

/-- Two copies of the members `inf`, `n` (slots 15/16 and 20/21) hold the same cells. -/
def Al (d : Nat) (cs : List Cell) : Prop := d + 2 ≤ cs.length ∧ cs[0]? = cs[d]? ∧ cs[1]? = cs[d + 1]?

def noAsgS (d : Nat) : NStmt → Bool
  | .assign s _ _ => !(s == 15 || s == 16 || s == 15 + d || s == 16 + d)
  | .declare _ w _ => w
  | _ => true

def noAsg (d : Nat) : Command → Bool
  | .primitive st => noAsgS d st
  | .sequence a b => noAsg d a && noAsg d b
  | .scope b => noAsg d b
  | .branch _ y n => noAsg d y && noAsg d n
  | .whileLoop _ b => noAsg d b
  | _ => true

inductive Sim (d : Nat) : Command → Command → Prop
  | prim {s : NStmt} : Sim d (.primitive s) (.primitive s)
  | dec {t : Ty} {w : Bool} {t1 : Ty} {a b : Nat} (h : a = b ∨ (a = 15 + d ∧ b = 15) ∨ (a = 16 + d ∧ b = 16)) :
      Sim d (.primitive (.declare t w (.variable t1 a))) (.primitive (.declare t w (.variable t1 b)))
  | seq {a b a' b' : Command} : Sim d a a' → Sim d b b' → Sim d (.sequence a b) (.sequence a' b')
  | scope {a a' : Command} : Sim d a a' → Sim d (.scope a) (.scope a')
  | branch {c : NExpr} {y n y' n' : Command} : Sim d y y' → Sim d n n' → Sim d (.branch c y n) (.branch c y' n')
  | whileLoop {c : NExpr} {b b' : Command} : Sim d b b' → Sim d (.whileLoop c b) (.whileLoop c b')
  | breakLoop : Sim d .breakLoop .breakLoop

theorem gS_take2 (P cs cs' : List Cell) (h : cs.length ≤ cs'.length) :
    (⟨(gS P cs').mem.take (gS P cs).mem.length, (gS P cs').bs.take (gS P cs).bs.length⟩ : PS) = gS P (cs'.take cs.length) := by
  simp only [gS, List.length_append, List.length_map, List.length_range]
  congr 1
  · rw [List.take_append]; simp [List.take_of_length_le]
  · rw [← List.map_take]
    congr 1
    apply List.ext_getElem
    · simp [Nat.min_eq_left h]
    · intro i h1 h2; simp

/-- Reading an aliased slot gives the same value. -/
theorem env_alias (d nv : Nat) (P cs : List Cell) (hA : Al d cs) (a b : Nat)
    (hab : (a = b) ∨ (a = nv + d ∧ b = nv + 0) ∨ (a = nv + (d + 1) ∧ b = nv + 1))
    (ty : Ty) : penvN nv (gS P cs) a ty = penvN nv (gS P cs) b ty := by
  rcases hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    unfold penvN penv
    have hlt : ¬ (nv + d < nv) := by omega
    have e1 : nv + d - nv = d := by omega
    have e0 : nv + 0 - nv = 0 := by omega
    have hn0 : ¬ (nv + 0 < nv) := by omega
    simp only [hlt, hn0, if_false, e1, e0]
    have l5 : d < cs.length := by have := hA.1; omega
    have l0 : 0 < cs.length := by have := hA.1; omega
    have b5 := gS_bs_get P cs d l5
    have b0 := gS_bs_get P cs 0 l0
    have m5 := gS_mem_get P cs d l5
    have m0 := gS_mem_get P cs 0 l0
    simp only [Bind.bind, Option.bind, b5, b0, m5, m0]
    rw [← hA.2.1]
  · rw [h1, h2]
    unfold penvN penv
    have hlt : ¬ (nv + (d + 1) < nv) := by omega
    have e1 : nv + (d + 1) - nv = d + 1 := by omega
    have e0 : nv + 1 - nv = 1 := by omega
    have hn0 : ¬ (nv + 1 < nv) := by omega
    simp only [hlt, hn0, if_false, e1, e0]
    have l5 : d + 1 < cs.length := by have := hA.1; omega
    have l0 : 1 < cs.length := by have := hA.1; omega
    have b5 := gS_bs_get P cs (d + 1) l5
    have b0 := gS_bs_get P cs 1 l0
    have m5 := gS_mem_get P cs (d + 1) l5
    have m0 := gS_mem_get P cs 1 l0
    simp only [Bind.bind, Option.bind, b5, b0, m5, m0]
    rw [← hA.2.2]

theorem prim_shape (d : Nat) (mv : MV) (hnv : mv.nv = 15) (P cs : List Cell) (vv : Nat → List Int) (st : NStmt) (hn : noAsgS d st = true)
    (r : PRM) (h : pstmtM mv st (gS P cs) vv = some r) :
    ∃ cs', r.ps = gS P cs' ∧ cs.length ≤ cs'.length ∧
      (∀ j, j < cs.length → (j = 0 ∨ j = 1 ∨ j = d ∨ j = d + 1) → cs'[j]? = cs[j]?) := by
  cases st with
  | declare ty w e =>
    simp only [noAsgS] at hn
    subst hn
    simp only [pstmtM, Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) e with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      cases hc : ty.convert v with
      | none => simp [hc] at h
      | some v' =>
        simp only [hc] at h
        cases h
        refine ⟨cs ++ [⟨ty, v'⟩], ?_, by simp, ?_⟩
        · simp [gS, List.range_succ]
        · intro j hj _; rw [List.getElem?_append_left hj]
  | assign s ty e =>
    simp only [noAsgS, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
    simp only [pstmtM, Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) e with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      cases hb : (gS P cs).bs[s - mv.nv]? with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h
        cases hm : (gS P cs).mem[b.address]? with
        | none => simp [hm] at h
        | some c =>
          simp only [hm] at h
          by_cases ok : mv.nv ≤ s ∧ c.type = ty ∧ ty.valid c.value = true ∧ b.writable = true
          · simp only [ok, and_self, ite_true] at h
            cases hc : ty.convert v with
            | none => simp [hc] at h
            | some v' =>
              simp only [hc] at h
              cases h
              have hsl : s - mv.nv < cs.length := by
                by_cases hlt : s - mv.nv < cs.length
                · exact hlt
                · have : (gS P cs).bs[s - mv.nv]? = none := by simp [gS]; omega
                  rw [this] at hb; cases hb
              have hb' := gS_bs_get P cs (s - mv.nv) hsl
              rw [hb'] at hb
              cases hb
              refine ⟨cs.set (s - mv.nv) ⟨ty, v'⟩, ?_, by simp, ?_⟩
              · simp only [gS, List.length_set]
                rw [List.set_append_right _ _ (by omega)]
                simp
              · intro j hj hj'
                rw [List.getElem?_set_ne]
                omega
          · simp [ok] at h
  | ret e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) e with
    | none => simp [hv] at h
    | some v => simp only [hv] at h; cases h; exact ⟨cs, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩
  | check e =>
    simp only [pstmtM, Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) e with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      by_cases hz : v ≠ 0
      · rw [if_pos hz] at h; cases h; exact ⟨cs, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩
      · rw [if_neg hz] at h; cases h
  | skip => simp [pstmtM] at h; cases h; exact ⟨cs, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩
  | write c ty iE vE =>
    obtain ⟨h1, _⟩ := pstmtM_write_inv mv c ty iE vE _ vv r h
    exact ⟨cs, h1, Nat.le_refl _, fun _ _ _ => rfl⟩
  | sortVec c ty =>
    obtain ⟨h1, _⟩ := pstmtM_sort_inv mv c ty _ vv r h
    exact ⟨cs, h1, Nat.le_refl _, fun _ _ _ => rfl⟩
  | dedupVec c ty =>
    obtain ⟨h1, _⟩ := pstmtM_dedup_inv mv c ty _ vv r h
    exact ⟨cs, h1, Nat.le_refl _, fun _ _ _ => rfl⟩
  | _ => simp [pstmtM] at h


theorem dec_eq (d : Nat) (mv : MV) (hnv : mv.nv = 15) (P cs : List Cell) (hA : Al d cs) (vv : Nat → List Int) (t : Ty) (w : Bool) (t1 : Ty)
    (a b : Nat) (h : a = b ∨ (a = 15 + d ∧ b = 15) ∨ (a = 16 + d ∧ b = 16)) :
    pstmtM mv (.declare t w (.variable t1 b)) (gS P cs) vv = pstmtM mv (.declare t w (.variable t1 a)) (gS P cs) vv := by
  have hd : vdenM mv vv (penvN mv.nv (gS P cs)) (.variable t1 b) = vdenM mv vv (penvN mv.nv (gS P cs)) (.variable t1 a) := by
    rw [vdenM_scalar _ _ _ _ rfl, vdenM_scalar _ _ _ _ rfl, den_variable, den_variable]
    have := env_alias d mv.nv P cs hA a b (by rw [hnv]; omega) t1
    exact this.symm
  simp only [pstmtM, hd]
  rfl

theorem sim_exec (d : Nat) (mv : MV) (hnv : mv.nv = 15) : ∀ {c c' : Command}, Sim d c c' → noAsg d c = true →
    ∀ (fu : Nat) (P cs : List Cell) (vv : Nat → List Int) (r : PRM), Al d cs → pexecM mv fu c (gS P cs) vv = some r →
      pexecM mv fu c' (gS P cs) vv = some r ∧ ∃ cs', r.ps = gS P cs' ∧ Al d cs' ∧ cs.length ≤ cs'.length := by
  intro c c' hs
  induction hs with
  | @prim st =>
    intro hn fu P cs vv r hA h
    rw [pexecM] at h
    obtain ⟨cs', h1, h2, h3⟩ := prim_shape d mv hnv P cs vv st hn r h
    refine ⟨by rw [pexecM]; exact h, cs', h1, ⟨by have := hA.1; omega, ?_, ?_⟩, h2⟩
    · rw [h3 0 (by have := hA.1; omega) (by omega), h3 d (by have := hA.1; omega) (by omega)]; exact hA.2.1
    · rw [h3 1 (by have := hA.1; omega) (by omega), h3 (d + 1) (by have := hA.1; omega) (by omega)]; exact hA.2.2
  | @dec t w t1 a b hab =>
    intro hn fu P cs vv r hA h
    rw [pexecM] at h
    have e := dec_eq d mv hnv P cs hA vv t w t1 a b hab
    refine ⟨by rw [pexecM, e]; exact h, ?_⟩
    obtain ⟨cs', h1, h2, h3⟩ := prim_shape d mv hnv P cs vv _ hn r h
    refine ⟨cs', h1, ⟨by have := hA.1; omega, ?_, ?_⟩, h2⟩
    · rw [h3 0 (by have := hA.1; omega) (by omega), h3 d (by have := hA.1; omega) (by omega)]; exact hA.2.1
    · rw [h3 1 (by have := hA.1; omega) (by omega), h3 (d + 1) (by have := hA.1; omega) (by omega)]; exact hA.2.2
  | @seq a b a' b' _ _ iha ihb =>
    intro hn fu P cs vv r hA h
    simp only [noAsg, Bool.and_eq_true] at hn
    cases h1 : pexecM mv fu a (gS P cs) vv with
    | none => rw [pexecM_seq, h1] at h; simp at h
    | some r1 =>
      obtain ⟨e1, cs1, hps1, hA1, hle1⟩ := iha hn.1 fu P cs vv r1 hA h1
      rw [pexecM_seq, h1] at h
      simp only [Bind.bind, Option.bind] at h
      cases hr : r1.ret with
      | some v =>
        simp only [hr] at h; cases h
        exact ⟨by rw [pexecM_seq, e1]; simp only [Bind.bind, Option.bind, hr], cs1, hps1, hA1, hle1⟩
      | none =>
        simp only [hr] at h
        cases h2 : pexecM mv fu b r1.ps r1.vv with
        | none => simp [h2] at h
        | some r2 =>
          simp only [h2] at h; cases h
          rw [hps1] at h2
          obtain ⟨e2, cs2, hps2, hA2, hle2⟩ := ihb hn.2 fu P cs1 r1.vv r2 hA1 h2
          refine ⟨seqM_some e1 hr (by rw [hps1]; exact e2), cs2, hps2, hA2, by omega⟩
  | @scope a a' _ iha =>
    intro hn fu P cs vv r hA h
    simp only [noAsg] at hn
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases h1 : pexecM mv fu a (gS P cs) vv with
    | none => simp [h1] at h
    | some r1 =>
      simp only [h1] at h; cases h
      obtain ⟨e1, cs1, hps1, hA1, hle1⟩ := iha hn fu P cs vv r1 hA h1
      refine ⟨by rw [pexecM_scope mv fu a' _ vv r1 e1], ?_⟩
      refine ⟨cs1.take cs.length, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · show (⟨r1.ps.mem.take (gS P cs).mem.length, r1.ps.bs.take (gS P cs).bs.length⟩ : PS) = _
        rw [hps1]; exact gS_take2 P cs cs1 hle1
      · have := hA.1; simp [List.length_take]; omega
      · rw [List.getElem?_take_of_lt (by have := hA.1; omega), List.getElem?_take_of_lt (by have := hA.1; omega)]; exact hA1.2.1
      · rw [List.getElem?_take_of_lt (by have := hA.1; omega), List.getElem?_take_of_lt (by have := hA.1; omega)]; exact hA1.2.2
      · simp; omega
  | @branch cnd y n y' n' _ _ ihy ihn =>
    intro hn fu P cs vv r hA h
    simp only [noAsg, Bool.and_eq_true] at hn
    rw [pexecM] at h
    simp only [Bind.bind, Option.bind] at h
    cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) cnd with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      by_cases hz : v = 0
      · simp only [hz, ite_true] at h
        cases h1 : pexecM mv fu n (gS P cs) vv with
        | none => simp [h1] at h
        | some r1 =>
          simp only [h1] at h; cases h
          obtain ⟨e1, cs1, hps1, hA1, hle1⟩ := ihn hn.2 fu P cs vv r1 hA h1
          refine ⟨by rw [pexecM]; simp only [Bind.bind, Option.bind, hv, hz, ite_true, e1], cs1, hps1, hA1, hle1⟩
      · simp only [hz, ite_false] at h
        cases h1 : pexecM mv fu y (gS P cs) vv with
        | none => simp [h1] at h
        | some r1 =>
          simp only [h1] at h; cases h
          obtain ⟨e1, cs1, hps1, hA1, hle1⟩ := ihy hn.1 fu P cs vv r1 hA h1
          refine ⟨by rw [pexecM]; simp only [Bind.bind, Option.bind, hv, hz, ite_false, e1], cs1, hps1, hA1, hle1⟩
  | @whileLoop cnd b b' _ ih =>
    intro hn fu
    simp only [noAsg] at hn
    induction fu with
    | zero => intro P cs vv r hA h; simp [pexecM] at h
    | succ f ihf =>
      intro P cs vv r hA h
      rw [pexecM_while] at h
      simp only [Bind.bind, Option.bind] at h
      cases hv : vdenM mv vv (penvN mv.nv (gS P cs)) cnd with
      | none => simp [hv] at h
      | some v =>
        simp only [hv] at h
        by_cases hz : v = 0
        · simp only [hz, ite_true] at h; cases h
          exact ⟨by rw [pexecM_while]; simp only [Bind.bind, Option.bind, hv, hz, ite_true], cs, rfl, hA, Nat.le_refl _⟩
        · simp only [hz, ite_false] at h
          cases h1 : pexecM mv (f+1) b (gS P cs) vv with
          | none => simp [h1] at h
          | some r1 =>
            simp only [h1] at h
            obtain ⟨e1, cs1, hps1, hA1, hle1⟩ := ih hn (f+1) P cs vv r1 hA h1
            cases hr : r1.ret with
            | some w => simp [hr] at h
            | none =>
              simp only [hr] at h
              cases h2 : pexecM mv f (.whileLoop cnd b) r1.ps r1.vv with
              | none => simp [h2] at h
              | some r2 =>
                simp only [h2] at h; cases h
                rw [hps1] at h2
                obtain ⟨e2, cs2, hps2, hA2, hle2⟩ := ihf P cs1 r1.vv r2 hA1 h2
                refine ⟨?_, cs2, hps2, hA2, by omega⟩
                rw [pexecM_while]
                simp only [Bind.bind, Option.bind, hv, hz, ite_false, e1, hr]
                rw [hps1]; simp only [e2]
  | breakLoop => intro hn fu P cs vv r hA h; simp [pexecM] at h

end Proofs.BeatsRep
