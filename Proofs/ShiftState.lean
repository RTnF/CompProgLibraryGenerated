import Proofs.PowModStep

namespace Proofs.ShiftState
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.StraightLine
open Proofs.CppState (Cell)

/-- Renumber every scalar variable of an expression by one (the program gets one extra leading binding). -/
def _root_.Proofs.CppNestedProgram.NExpr.sh : NExpr → NExpr
  | .literal t v => .literal t v
  | .variable t k => .variable t (k + 1)
  | .cast t e => .cast t e.sh
  | .targetCast t e => .targetCast t e.sh
  | .unary t o e => .unary t o e.sh
  | .binary t o a b => .binary t o a.sh b.sh
  | .divrem t r a b => .divrem t r a.sh b.sh
  | .logical c a b => .logical c a.sh b.sh
  | .size e c => .size e c
  | .read t c i => .read t c i

theorem sh_denote (env env' : Nat → Ty → Option Int) (h : ∀ k ty, env' (k + 1) ty = env k ty) :
    ∀ e : NExpr, e.sh.denote env' = e.denote env
  | .literal t v => by simp [NExpr.sh, NExpr.denote]
  | .variable t k => by simp [NExpr.sh, NExpr.denote, h]
  | .cast t e => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h e]
  | .targetCast t e => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h e]
  | .unary t o e => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h e]
  | .binary t o a b => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h a, sh_denote env env' h b]
  | .divrem t r a b => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h a, sh_denote env env' h b]
  | .logical c a b => by simp [NExpr.sh, NExpr.denote, sh_denote env env' h a, sh_denote env env' h b]
  | .size e c => by simp [NExpr.sh, NExpr.denote]
  | .read t c i => by simp [NExpr.sh, NExpr.denote]

theorem sh_nodes : ∀ e : NExpr, e.sh.nodes = e.nodes
  | .literal t v => by simp [NExpr.sh, NExpr.nodes]
  | .variable t k => by simp [NExpr.sh, NExpr.nodes]
  | .cast t e => by simp [NExpr.sh, NExpr.nodes, sh_nodes e]
  | .targetCast t e => by simp [NExpr.sh, NExpr.nodes, sh_nodes e]
  | .unary t o e => by simp [NExpr.sh, NExpr.nodes, sh_nodes e]
  | .binary t o a b => by simp [NExpr.sh, NExpr.nodes, sh_nodes a, sh_nodes b]
  | .divrem t r a b => by simp [NExpr.sh, NExpr.nodes, sh_nodes a, sh_nodes b]
  | .logical c a b => by simp [NExpr.sh, NExpr.nodes, sh_nodes a, sh_nodes b]
  | .size e c => by simp [NExpr.sh, NExpr.nodes]
  | .read t c i => by simp [NExpr.sh, NExpr.nodes]

def _root_.Proofs.CppNestedProgram.NStmt.sh : NStmt → NStmt
  | .declare t w e => .declare t w e.sh
  | .assign k t e => .assign (k + 1) t e.sh
  | .ret e => .ret e.sh
  | .check e => .check e.sh
  | st => st

def shR (b0 : CppState.Binding) (r : PR) : PR := ⟨⟨r.ps.mem, b0 :: r.ps.bs⟩, r.ret, r.cost, r.need + 1⟩

theorem penv_sh (mem : List Cell) (bs : List CppState.Binding) (b0 : CppState.Binding) (k : Nat) (ty : Ty) :
    penv ⟨mem, b0 :: bs⟩ (k + 1) ty = penv ⟨mem, bs⟩ k ty := by
  simp [penv]

theorem pstmt_sh (st : NStmt) (mem : List Cell) (bs : List CppState.Binding) (b0 : CppState.Binding) :
    pstmt st.sh ⟨mem, b0 :: bs⟩ = (pstmt st ⟨mem, bs⟩).map (shR b0) := by
  have env : ∀ k ty, penv ⟨mem, b0 :: bs⟩ (k + 1) ty = penv ⟨mem, bs⟩ k ty := penv_sh mem bs b0
  cases st with
  | skip => simp [NStmt.sh, pstmt, shR]; omega
  | declare t w e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h]
    | some v =>
      cases hc : t.convert v with
      | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hc]
      | some v' => simp [NStmt.sh, pstmt, sh_denote _ _ env, sh_nodes, h, hc, shR]; omega
  | assign k t e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h]
    | some v =>
      cases hb : bs[k]? with
      | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hb]
      | some b =>
        cases hm : mem[b.address]? with
        | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hb, hm]
        | some c =>
          by_cases hh : c.type = t ∧ t.valid c.value = true ∧ b.writable = true
          · cases hc : t.convert v with
            | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hb, hm, hh, hc]
            | some v' => simp [NStmt.sh, pstmt, sh_denote _ _ env, sh_nodes, h, hb, hm, hh, hc, shR]; omega
          · simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hb, hm, hh]
  | ret e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h]
    | some v => simp [NStmt.sh, pstmt, sh_denote _ _ env, sh_nodes, h, shR]; omega
  | check e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.sh, pstmt, sh_denote _ _ env, h]
    | some v =>
      by_cases hv : v = 0
      · simp [NStmt.sh, pstmt, sh_denote _ _ env, h, hv]
      · simp [NStmt.sh, pstmt, sh_denote _ _ env, sh_nodes, h, hv, shR]; omega
  | _ => simp [NStmt.sh, pstmt]

def _root_.Proofs.CppNestedProgram.Command.sh : Command → Command
  | .primitive st => .primitive st.sh
  | .sequence a b => .sequence a.sh b.sh
  | .scope b => .scope b.sh
  | .branch c y n => .branch c.sh y.sh n.sh
  | .whileLoop c b => .whileLoop c.sh b.sh
  | c => c


theorem pexec_sh (fu : Nat) (c : Command) (ps : PS) :
    ∀ b0 : CppState.Binding, pexec fu c.sh ⟨ps.mem, b0 :: ps.bs⟩ = (pexec fu c ps).map (shR b0) := by
  induction fu, c, ps using pexec.induct with
  | case1 fu st ps =>
    intro b0
    simp only [Command.sh, pexec]
    exact pstmt_sh st ps.mem ps.bs b0
  | case2 fu a b ps iha ihb =>
    intro b0
    simp only [Command.sh, pexec, Bind.bind, Option.bind]
    rw [iha b0]
    cases ha : pexec fu a ps with
    | none => simp
    | some r =>
      cases hr : r.ret with
      | some v => simp [shR, hr]
      | none =>
        have := ihb r b0
        simp only [Option.map, shR, hr]
        rw [this]
        cases hb : pexec fu b r.ps with
        | none => simp
        | some r2 => simp [shR]
  | case3 fu body ps ih =>
    intro b0
    simp only [Command.sh, pexec, Bind.bind, Option.bind]
    rw [ih b0]
    cases ha : pexec fu body ps with
    | none => simp
    | some r => simp [shR]
  | case4 fu c y n ps ihn ihy =>
    intro b0
    have env : ∀ k ty, penv ⟨ps.mem, b0 :: ps.bs⟩ (k + 1) ty = penv ⟨ps.mem, ps.bs⟩ k ty := penv_sh ps.mem ps.bs b0
    simp only [Command.sh, pexec, Bind.bind, Option.bind, sh_denote _ _ env]
    cases hc : c.denote (penv ⟨ps.mem, ps.bs⟩) with
    | none => simp
    | some v =>
      by_cases hv : v = 0
      · simp only [hv, if_true]
        rw [ihn b0]
        cases hn : pexec fu n ps with
        | none => simp
        | some r => simp [shR, sh_nodes]; omega
      · simp only [hv, if_false]
        rw [ihy b0]
        cases hy : pexec fu y ps with
        | none => simp
        | some r => simp [shR, sh_nodes]; omega
  | case5 c body ps =>
    intro b0
    simp [Command.sh, pexec]
  | case6 fu c b ps ihb ihw =>
    intro b0
    have env : ∀ k ty, penv ⟨ps.mem, b0 :: ps.bs⟩ (k + 1) ty = penv ⟨ps.mem, ps.bs⟩ k ty := penv_sh ps.mem ps.bs b0
    simp only [Command.sh, pexec, Bind.bind, Option.bind, sh_denote _ _ env]
    cases hc : c.denote (penv ⟨ps.mem, ps.bs⟩) with
    | none => simp
    | some v =>
      by_cases hv : v = 0
      · simp [hv, shR, sh_nodes]; omega
      · simp only [hv, if_false]
        rw [ihb b0]
        cases hb : pexec (fu + 1) b ps with
        | none => simp
        | some r =>
          cases hr : r.ret with
          | some w => simp [shR, hr]
          | none =>
            have := ihw r b0
            simp only [Option.map, shR, hr]
            have e : (Command.whileLoop c.sh b.sh) = (Command.whileLoop c b).sh := rfl
            rw [e, this]
            cases hw : pexec fu (.whileLoop c b) r.ps with
            | none => simp
            | some r2 => simp [shR, sh_nodes]; omega
  | case7 fu c ps h1 h2 h3 h4 h5 h6 =>
    intro b0
    cases c with
    | primitive st => exact absurd rfl (h1 st)
    | sequence a b => exact absurd rfl (h2 a b)
    | scope b => exact absurd rfl (h3 b)
    | branch c y n => exact absurd rfl (h4 c y n)
    | whileLoop c b =>
      cases fu with
      | zero => exact absurd rfl (h5 c b rfl)
      | succ n => exact absurd rfl (h6 n c b rfl)
    | breakLoop => simp [Command.sh, pexec]
    | invokeScalar p a => simp [Command.sh, pexec]

/-- Append a continuation after the last statement of a right-nested sequence. -/
def _root_.Proofs.CppNestedProgram.Command.snoc : Command → Command → Command
  | .sequence a b, z => .sequence a (b.snoc z)
  | c, z => .sequence c z

theorem pexec_snoc (fu : Nat) (z : Command) :
    ∀ (c : Command) (ps : PS) (r : PR), pexec fu c ps = some r → r.ret = none →
      pexec fu (c.snoc z) ps = (pexec fu z r.ps).map (fun r2 => ⟨r2.ps, r2.ret, r.cost + r2.cost, max r.need r2.need⟩) := by
  intro c
  induction c with
  | sequence a b iha ihb =>
    intro ps r h hr
    simp only [Command.snoc, pexec, Bind.bind, Option.bind] at h ⊢
    cases ha : pexec fu a ps with
    | none => simp [ha] at h
    | some ra =>
      simp only [ha] at h
      cases hra : ra.ret with
      | some v => simp [hra] at h; subst h; simp [hr] at hra
      | none =>
        simp only [hra] at h ⊢
        cases hb : pexec fu b ra.ps with
        | none => simp [hb] at h
        | some rb =>
          simp only [hb] at h
          have hrr : r = ⟨rb.ps, rb.ret, ra.cost + rb.cost, max ra.need rb.need⟩ := by
            simp at h; exact h.symm
          subst hrr
          have := ihb ra.ps rb hb hr
          rw [this]
          cases hz : pexec fu z rb.ps with
          | none => simp
          | some rz => simp [Nat.add_assoc, Nat.max_assoc]
  | primitive st =>
    intro ps r h hr
    simp only [Command.snoc, pexec, Bind.bind, Option.bind] at h ⊢
    rw [h]
    cases hz : pexec fu z r.ps with
    | none => simp [hr, hz]
    | some rz => simp [hr, hz]
  | scope body ih =>
    intro ps r h hr
    simp only [Command.snoc, pexec, Bind.bind, Option.bind] at h ⊢
    cases hb : pexec fu body ps with
    | none => simp [hb] at h
    | some rb =>
      simp only [hb, Option.some.injEq] at h
      subst h
      have hr' : rb.ret = none := hr
      simp only [hb, hr']
      cases hz : pexec fu z ⟨List.take ps.mem.length rb.ps.mem, List.take ps.bs.length rb.ps.bs⟩ with
      | none => simp
      | some rz => simp
  | branch c y n =>
    intro ps r h hr
    simp only [Command.snoc, pexec, Bind.bind, Option.bind] at h ⊢
    cases hc : c.denote (penv ps) with
    | none => simp [hc] at h
    | some v =>
      simp only [hc] at h ⊢
      by_cases hv : v = 0
      · simp only [hv, if_true] at h ⊢
        cases hb : pexec fu n ps with
        | none => simp [hb] at h
        | some rb =>
          simp only [hb, Option.some.injEq] at h
          subst h
          have hr' : rb.ret = none := hr
          simp only [hb, hr']
          cases hz : pexec fu z rb.ps with
          | none => simp
          | some rz => simp
      · simp only [hv, if_false] at h ⊢
        cases hb : pexec fu y ps with
        | none => simp [hb] at h
        | some rb =>
          simp only [hb, Option.some.injEq] at h
          subst h
          have hr' : rb.ret = none := hr
          simp only [hb, hr']
          cases hz : pexec fu z rb.ps with
          | none => simp
          | some rz => simp
  | whileLoop c b =>
    intro ps r h hr
    simp only [Command.snoc, pexec, Bind.bind, Option.bind] at h ⊢
    rw [h]
    cases hz : pexec fu z r.ps with
    | none => simp [hr, hz]
    | some rz => simp [hr, hz]
  | breakLoop => intro ps r h hr; simp [Command.snoc, pexec] at h
  | invokeScalar p a => intro ps r h hr; simp [Command.snoc, pexec] at h

end Proofs.ShiftState
