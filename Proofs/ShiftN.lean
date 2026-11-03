import Proofs.PowModStep

namespace Proofs.ShiftN
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.StraightLine
open Proofs.CppState (Cell)

/-- Renumber every scalar variable of an expression by one (the program gets one extra leading binding). -/
def _root_.Proofs.CppNestedProgram.NExpr.shN (n : Nat) : NExpr → NExpr
  | .literal t v => .literal t v
  | .variable t k => .variable t (k + n)
  | .cast t e => .cast t (e.shN n)
  | .targetCast t e => .targetCast t (e.shN n)
  | .unary t o e => .unary t o (e.shN n)
  | .binary t o a b => .binary t o (a.shN n) (b.shN n)
  | .divrem t r a b => .divrem t r (a.shN n) (b.shN n)
  | .logical c a b => .logical c (a.shN n) (b.shN n)
  | .size e c => .size e c
  | .read t c i => .read t c i

theorem sh_denote (n : Nat) (env env' : Nat → Ty → Option Int) (h : ∀ k ty, env' (k + n) ty = env k ty) :
    ∀ e : NExpr, (e.shN n).denote env' = e.denote env
  | .literal t v => by simp [NExpr.shN, NExpr.denote]
  | .variable t k => by simp [NExpr.shN, NExpr.denote, h]
  | .cast t e => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h e]
  | .targetCast t e => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h e]
  | .unary t o e => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h e]
  | .binary t o a b => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h a, sh_denote n env env' h b]
  | .divrem t r a b => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h a, sh_denote n env env' h b]
  | .logical c a b => by simp [NExpr.shN, NExpr.denote, sh_denote n env env' h a, sh_denote n env env' h b]
  | .size e c => by simp [NExpr.shN, NExpr.denote]
  | .read t c i => by simp [NExpr.shN, NExpr.denote]

theorem sh_nodes (n : Nat) : ∀ e : NExpr, (e.shN n).nodes = e.nodes
  | .literal t v => by simp [NExpr.shN, NExpr.nodes]
  | .variable t k => by simp [NExpr.shN, NExpr.nodes]
  | .cast t e => by simp [NExpr.shN, NExpr.nodes, sh_nodes n e]
  | .targetCast t e => by simp [NExpr.shN, NExpr.nodes, sh_nodes n e]
  | .unary t o e => by simp [NExpr.shN, NExpr.nodes, sh_nodes n e]
  | .binary t o a b => by simp [NExpr.shN, NExpr.nodes, sh_nodes n a, sh_nodes n b]
  | .divrem t r a b => by simp [NExpr.shN, NExpr.nodes, sh_nodes n a, sh_nodes n b]
  | .logical c a b => by simp [NExpr.shN, NExpr.nodes, sh_nodes n a, sh_nodes n b]
  | .size e c => by simp [NExpr.shN, NExpr.nodes]
  | .read t c i => by simp [NExpr.shN, NExpr.nodes]

def _root_.Proofs.CppNestedProgram.NStmt.shN (n : Nat) : NStmt → NStmt
  | .declare t w e => .declare t w (e.shN n)
  | .assign k t e => .assign (k + n) t (e.shN n)
  | .ret e => .ret (e.shN n)
  | .check e => .check (e.shN n)
  | st => st

def shR (B : List CppState.Binding) (r : PR) : PR := ⟨⟨r.ps.mem, B ++ r.ps.bs⟩, r.ret, r.cost, r.need + B.length⟩

theorem penv_sh (mem : List Cell) (bs : List CppState.Binding) (B : List CppState.Binding) (k : Nat) (ty : Ty) :
    penv ⟨mem, B ++ bs⟩ (k + B.length) ty = penv ⟨mem, bs⟩ k ty := by
  simp [penv, List.getElem?_append_right]

theorem get_sh (B bs : List CppState.Binding) (k : Nat) : (B ++ bs)[k + B.length]? = bs[k]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem take_sh (B : List CppState.Binding) (bs l : List CppState.Binding) :
    (B ++ l).take (B.length + bs.length) = B ++ l.take bs.length := by
  rw [List.take_append]
  simp [List.take_of_length_le]

theorem pstmt_sh (st : NStmt) (mem : List Cell) (bs : List CppState.Binding) (B : List CppState.Binding) :
    pstmt (st.shN B.length) ⟨mem, B ++ bs⟩ = (pstmt st ⟨mem, bs⟩).map (shR B) := by
  have env : ∀ k ty, penv ⟨mem, B ++ bs⟩ (k + B.length) ty = penv ⟨mem, bs⟩ k ty := penv_sh mem bs B
  cases st with
  | skip => simp [NStmt.shN, pstmt, shR]; omega
  | declare t w e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h]
    | some v =>
      cases hc : t.convert v with
      | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hc]
      | some v' => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, sh_nodes B.length, h, hc, shR]; omega
  | assign k t e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h]
    | some v =>
      cases hb : bs[k]? with
      | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hb]
      | some b =>
        cases hm : mem[b.address]? with
        | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hb, hm]
        | some c =>
          by_cases hh : c.type = t ∧ t.valid c.value = true ∧ b.writable = true
          · cases hc : t.convert v with
            | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hb, hm, hh, hc]
            | some v' => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, sh_nodes B.length, h, hb, hm, hh, hc, shR]; omega
          · simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hb, hm, hh]
  | ret e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h]
    | some v => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, sh_nodes B.length, h, shR]; omega
  | check e =>
    cases h : e.denote (penv ⟨mem, bs⟩) with
    | none => simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h]
    | some v =>
      by_cases hv : v = 0
      · simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, h, hv]
      · simp [NStmt.shN, pstmt, sh_denote B.length _ _ env, get_sh, sh_nodes B.length, h, hv, shR]; omega
  | _ => simp [NStmt.shN, pstmt]

def _root_.Proofs.CppNestedProgram.Command.shN (n : Nat) : Command → Command
  | .primitive st => .primitive (st.shN n)
  | .sequence a b => .sequence (a.shN n) (b.shN n)
  | .scope b => .scope (b.shN n)
  | .branch c y nn => .branch (c.shN n) (y.shN n) (nn.shN n)
  | .whileLoop c b => .whileLoop (c.shN n) (b.shN n)
  | c => c


theorem pexec_sh (fu : Nat) (c : Command) (ps : PS) :
    ∀ B : List CppState.Binding, pexec fu (c.shN B.length) ⟨ps.mem, B ++ ps.bs⟩ = (pexec fu c ps).map (shR B) := by
  induction fu, c, ps using pexec.induct with
  | case1 fu st ps =>
    intro B
    simp only [Command.shN, pexec]
    exact pstmt_sh st ps.mem ps.bs B
  | case2 fu a b ps iha ihb =>
    intro B
    simp only [Command.shN, pexec, Bind.bind, Option.bind]
    rw [iha B]
    cases ha : pexec fu a ps with
    | none => simp
    | some r =>
      cases hr : r.ret with
      | some v => simp [shR, hr]
      | none =>
        have := ihb r B
        simp only [Option.map, shR, hr]
        rw [this]
        cases hb : pexec fu b r.ps with
        | none => simp
        | some r2 => simp [shR]
  | case3 fu body ps ih =>
    intro B
    simp only [Command.shN, pexec, Bind.bind, Option.bind]
    rw [ih B]
    cases ha : pexec fu body ps with
    | none => simp
    | some r => simp [shR, take_sh]
  | case4 fu c y n ps ihn ihy =>
    intro B
    have env : ∀ k ty, penv ⟨ps.mem, B ++ ps.bs⟩ (k + B.length) ty = penv ⟨ps.mem, ps.bs⟩ k ty := penv_sh ps.mem ps.bs B
    simp only [Command.shN, pexec, Bind.bind, Option.bind, sh_denote B.length _ _ env]
    cases hc : c.denote (penv ⟨ps.mem, ps.bs⟩) with
    | none => simp
    | some v =>
      by_cases hv : v = 0
      · simp only [hv, if_true]
        rw [ihn B]
        cases hn : pexec fu n ps with
        | none => simp
        | some r => simp [shR, sh_nodes B.length]; omega
      · simp only [hv, if_false]
        rw [ihy B]
        cases hy : pexec fu y ps with
        | none => simp
        | some r => simp [shR, sh_nodes B.length]; omega
  | case5 c body ps =>
    intro B
    simp [Command.shN, pexec]
  | case6 fu c b ps ihb ihw =>
    intro B
    have env : ∀ k ty, penv ⟨ps.mem, B ++ ps.bs⟩ (k + B.length) ty = penv ⟨ps.mem, ps.bs⟩ k ty := penv_sh ps.mem ps.bs B
    simp only [Command.shN, pexec, Bind.bind, Option.bind, sh_denote B.length _ _ env]
    cases hc : c.denote (penv ⟨ps.mem, ps.bs⟩) with
    | none => simp
    | some v =>
      by_cases hv : v = 0
      · simp [hv, shR, sh_nodes B.length]; omega
      · simp only [hv, if_false]
        rw [ihb B]
        cases hb : pexec (fu + 1) b ps with
        | none => simp
        | some r =>
          cases hr : r.ret with
          | some w => simp [shR, hr]
          | none =>
            have := ihw r B
            simp only [Option.map, shR, hr]
            have e : (Command.whileLoop (c.shN B.length) (b.shN B.length)) = (Command.whileLoop c b).shN B.length := rfl
            rw [e, this]
            cases hw : pexec fu (.whileLoop c b) r.ps with
            | none => simp
            | some r2 => simp [shR, sh_nodes B.length]; omega
  | case7 fu c ps h1 h2 h3 h4 h5 h6 =>
    intro B
    cases c with
    | primitive st => exact absurd rfl (h1 st)
    | sequence a b => exact absurd rfl (h2 a b)
    | scope b => exact absurd rfl (h3 b)
    | branch c y n => exact absurd rfl (h4 c y n)
    | whileLoop c b =>
      cases fu with
      | zero => exact absurd rfl (h5 c b rfl)
      | succ n => exact absurd rfl (h6 n c b rfl)
    | breakLoop => simp [Command.shN, pexec]
    | invokeScalar p a => simp [Command.shN, pexec]

end Proofs.ShiftN
