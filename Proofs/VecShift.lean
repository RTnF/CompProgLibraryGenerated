import Proofs.UfCompression
import Proofs.ShiftN

namespace Proofs.VecShift
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr
open Proofs.VecWrite Proofs.ShiftN
open Proofs.CppState (Cell)

-- Keep the vector at slot 0; insert scalar bindings immediately after it.
def slot (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => k+n+1

def expr (n : Nat) : NExpr → NExpr
  | .literal t v => .literal t v
  | .variable t k => .variable t (slot n k)
  | .cast t e => .cast t (expr n e)
  | .targetCast t e => .targetCast t (expr n e)
  | .unary t o e => .unary t o (expr n e)
  | .binary t o a b => .binary t o (expr n a) (expr n b)
  | .divrem t r a b => .divrem t r (expr n a) (expr n b)
  | .logical c a b => .logical c (expr n a) (expr n b)
  | .size e c => .size e c
  | .read t c i => .read t c (expr n i)

theorem scalarOnly (n : Nat) : ∀ e : NExpr, (expr n e).scalarOnly = e.scalarOnly
  | .literal .. | .variable .. | .size .. | .read .. => rfl
  | .cast _ e | .targetCast _ e | .unary _ _ e => by simp [expr,NExpr.scalarOnly,scalarOnly n e]
  | .binary _ _ a b | .divrem _ _ a b | .logical _ a b => by simp [expr,NExpr.scalarOnly,scalarOnly n a,scalarOnly n b]

theorem nodes (n : Nat) : ∀ e : NExpr, (expr n e).nodes = e.nodes
  | .literal .. | .variable .. | .size .. => rfl
  | .read _ _ i => by simp [expr,NExpr.nodes,nodes n i]
  | .cast _ e | .targetCast _ e | .unary _ _ e => by simp [expr,NExpr.nodes,nodes n e]
  | .binary _ _ a b | .divrem _ _ a b | .logical _ a b => by simp [expr,NExpr.nodes,nodes n a,nodes n b]

theorem denote (n : Nat) (env env' : Nat → Ty → Option Int)
    (same : ∀ k ty, env' (slot n k) ty = env k ty) :
    ∀ e : NExpr, (expr n e).denote env' = e.denote env
  | .literal .. | .size .. | .read .. => rfl
  | .variable t k => same k t
  | .cast _ e | .targetCast _ e | .unary _ _ e => by simp [expr,NExpr.denote,denote n env env' same e]
  | .binary _ _ a b | .divrem _ _ a b | .logical _ a b => by
    simp [expr,NExpr.denote,denote n env env' same a,denote n env env' same b]

def pad (B : List CppState.Binding) (ps : PS) : PS := ⟨ps.mem,B++ps.bs⟩

theorem environment (B : List CppState.Binding) (ps : PS) (k : Nat) (ty : Ty) :
    penv1 (pad B ps) (slot B.length k) ty = penv1 ps k ty := by
  cases k with
  | zero => rfl
  | succ k => exact penv_sh ps.mem ps.bs B k ty

theorem value (n : Nat) (ty : Ty) (vec : List Int) (env env' : Nat → Ty → Option Int)
    (same : ∀ k t, env' (slot n k) t = env k t) :
    ∀ e, vdenL ty vec env' (expr n e) = vdenL ty vec env e
  | .literal .. => rfl
  | .variable t k => same k t
  | .cast t e => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.cast t e)
    · exact congrArg (Option.bind · t.convert) (value n ty vec env env' same e)
  | .binary t op l r => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.binary t op l r)
    · change ((vdenL ty vec env' (expr n l)).bind fun a => (vdenL ty vec env' (expr n r)).bind fun b => t.convert (binaryValue op a b)) = _
      rw [value n ty vec env env' same l,value n ty vec env env' same r]
  | .read t (.local 0) i => by
    simp [expr,vdenL,NExpr.scalarOnly,scalarOnly,denote n env env' same]
  | .read t (.local (_+1)) i => by simp [expr,vdenL,NExpr.scalarOnly]
  | .read t (.row ..) i => by simp [expr,vdenL,NExpr.scalarOnly]
  | .size el c => by
    cases c with
    | «local» k => cases k <;> cases el <;> rfl
    | row _ _ _ => cases el <;> rfl
  | .targetCast t e => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.targetCast t e)
    · rfl
  | .unary t op e => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.unary t op e)
    · change ((vdenL ty vec env' (expr n e)).bind fun v => t.convert (unaryValue op v)) = _
      rw [value n ty vec env env' same e]
  | .divrem t rem l r => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.divrem t rem l r)
    · rfl
  | .logical c l r => by
    unfold vdenL
    simp only [scalarOnly]
    split
    · exact denote n env env' same (.logical c l r)
    · rfl

theorem wp (n : Nat) : ∀ e, vwp (expr n e) = vwp e
  | .cast t e => by
    have sc := scalarOnly n (.cast t e)
    simp only [expr] at sc
    simp [expr,vwp,sc,nodes,NExpr.nodes,wp n e]
  | .unary t op e => by
    have sc := scalarOnly n (.unary t op e)
    simp only [expr] at sc
    simp [expr,vwp,sc,nodes,NExpr.nodes,wp n e]
  | .binary t op l r => by
    have sc := scalarOnly n (.binary t op l r)
    simp only [expr] at sc
    simp [expr,vwp,sc,nodes,NExpr.nodes,wp n l,wp n r]
  | .read t c i => by cases c <;> simp [expr,vwp,nodes]
  | .size .. => rfl
  | .literal .. | .variable .. | .targetCast .. | .divrem .. | .logical .. => by
    exact Prod.ext (nodes n _) (nodes n _)

-- Shift precisely the statement profile of the flat-vector executor. Unsupported
-- statements keep their rejection; this is not a nested-container reindexer.
def stmt (n : Nat) : NStmt → NStmt
  | .declare t w e => .declare t w (expr n e)
  | .assign k t e => .assign (slot n k) t (expr n e)
  | .ret e => .ret (expr n e)
  | .check e => .check (expr n e)
  | .write c t i v => .write c t (expr n i) (expr n v)
  | other => other

def result (B : List CppState.Binding) (r : PRW) : PRW :=
  ⟨pad B r.ps,r.vec,r.ret,r.cost,r.need+B.length,r.wk⟩

theorem statement (ty : Ty) (st : NStmt) (ps : PS) (vec : List Int) (B : List CppState.Binding) :
    pstmtW ty (stmt B.length st) (pad B ps) vec = (pstmtW ty st ps vec).map (result B) := by
  have val : ∀ e, vdenL ty vec (penv1 ⟨ps.mem,B++ps.bs⟩) (expr B.length e) = vdenL ty vec (penv1 ps) e :=
    value B.length ty vec _ _ (environment B ps)
  cases st with
  | skip => simp [stmt,pstmtW,pad,result]; omega
  | declare t w e =>
    cases he : vdenL ty vec (penv1 ps) e with
    | none => simp [stmt,pstmtW,pad,val,he]
    | some v =>
      cases hc : t.convert v with
      | none => simp [stmt,pstmtW,pad,val,he,hc]
      | some x => simp [stmt,pstmtW,pad,val,he,hc,wp,pad,result,List.append_assoc]; omega
  | assign k t e =>
    cases k with
    | zero => simp [stmt,slot,pstmtW]
    | succ k =>
      cases he : vdenL ty vec (penv1 ps) e with
      | none => simp [stmt,slot,pstmtW,pad,val,he]
      | some v =>
        cases hb : ps.bs[k]? with
        | none => simp [stmt,slot,pstmtW,pad,val,he,pad,get_sh,hb]
        | some b =>
          cases hm : ps.mem[b.address]? with
          | none => simp [stmt,slot,pstmtW,pad,val,he,pad,get_sh,hb,hm]
          | some c =>
            by_cases valid : c.type = t ∧ t.valid c.value = true ∧ b.writable = true
            · cases hc : t.convert v with
              | none => simp [stmt,slot,pstmtW,pad,val,he,pad,get_sh,hb,hm,valid,hc]
              | some x => simp [stmt,slot,pstmtW,pad,val,he,pad,get_sh,hb,hm,valid,hc,wp,result]; omega
            · simp [stmt,slot,pstmtW,pad,val,he,pad,get_sh,hb,hm,valid]
  | ret e =>
    cases he : vdenL ty vec (penv1 ps) e with
    | none => simp [stmt,pstmtW,pad,val,he]
    | some v => simp [stmt,pstmtW,pad,val,he,wp,result,pad]; omega
  | check e =>
    cases he : vdenL ty vec (penv1 ps) e with
    | none => simp [stmt,pstmtW,pad,val,he]
    | some v =>
      by_cases zero : v = 0
      · simp [stmt,pstmtW,pad,val,he,zero]
      · simp [stmt,pstmtW,pad,val,he,zero,wp,result]; omega
  | write c t i v =>
    cases c with
    | «local» k =>
      cases k with
      | zero =>
        cases hv : vdenL ty vec (penv1 ps) v with
        | none => simp [stmt,pstmtW,pad,val,hv]
        | some x =>
          cases hi : vdenL ty vec (penv1 ps) i with
          | none => simp [stmt,pstmtW,pad,val,hv,hi]
          | some j =>
            by_cases valid : t = ty ∧ 0 ≤ j ∧ j.toNat < vec.length ∧ ty.valid x = true
            · simp [stmt,pstmtW,pad,val,hv,hi,valid,wp,nodes,result,pad]; omega
            · simp [stmt,pstmtW,pad,val,hv,hi,valid]
      | succ k => simp [stmt,pstmtW]
    | row _ _ _ => simp [stmt,pstmtW]
  | sortVec c t =>
    cases c with
    | «local» k =>
      cases k with
      | zero => by_cases same : t = ty <;> simp [stmt,pstmtW,same,result,pad]; omega
      | succ k => simp [stmt,pstmtW]
    | row _ _ _ => simp [stmt,pstmtW]
  | dedupVec c t =>
    cases c with
    | «local» k =>
      cases k with
      | zero => by_cases same : t = ty <;> simp [stmt,pstmtW,same,result,pad]; omega
      | succ k => simp [stmt,pstmtW]
    | row _ _ _ => simp [stmt,pstmtW]
  | _ => simp [stmt,pstmtW]

def command (n : Nat) : Command → Command
  | .primitive st => .primitive (stmt n st)
  | .sequence a b => .sequence (command n a) (command n b)
  | .scope b => .scope (command n b)
  | .branch c y no => .branch (expr n c) (command n y) (command n no)
  | .whileLoop c b => .whileLoop (expr n c) (command n b)
  | other => other

theorem execution (ty : Ty) (fuel : Nat) (c : Command) (ps : PS) (vec : List Int) :
    ∀ B : List CppState.Binding,
      pexecW ty fuel (command B.length c) (pad B ps) vec = (pexecW ty fuel c ps vec).map (result B) := by
  induction fuel,c,ps,vec using pexecW.induct with
  | case1 fu st ps vec =>
    intro B
    simpa only [command,pexecW] using statement ty st ps vec B
  | case2 fu a b ps vec iha ihb =>
    intro B
    simp only [command,pexecW,Bind.bind,Option.bind]
    rw [iha B]
    cases ha : pexecW ty fu a ps vec with
    | none => simp
    | some r =>
      cases hr : r.ret with
      | some v => simp [result,hr]
      | none =>
        have tail := ihb r B
        simp only [Option.map,result,hr]
        rw [tail]
        cases hb : pexecW ty fu b r.ps r.vec with
        | none => simp
        | some r2 => simp [result]
  | case3 fu body ps vec ih =>
    intro B
    simp only [command,pexecW,Bind.bind,Option.bind]
    rw [ih B]
    cases ha : pexecW ty fu body ps vec with
    | none => simp
    | some r => simp [result,pad,take_sh]
  | case4 fu c y no ps vec ihno ihyes =>
    intro B
    have val := value B.length ty vec (penv1 ps) (penv1 (pad B ps)) (environment B ps) c
    simp only [command,pexecW,Bind.bind,Option.bind,val]
    cases hc : vdenL ty vec (penv1 ps) c with
    | none => simp
    | some v =>
      by_cases zero : v = 0
      · simp only [zero,ite_true]
        rw [ihno B]
        cases hn : pexecW ty fu no ps vec with
        | none => simp
        | some r => simp [result,pad,wp]; omega
      · simp only [zero,ite_false]
        rw [ihyes B]
        cases hy : pexecW ty fu y ps vec with
        | none => simp
        | some r => simp [result,pad,wp]; omega
  | case5 c body ps vec =>
    intro B
    simp [command,pexecW]
  | case6 fu c b ps vec ihb ihw =>
    intro B
    have val := value B.length ty vec (penv1 ps) (penv1 (pad B ps)) (environment B ps) c
    simp only [command,pexecW,Bind.bind,Option.bind,val]
    cases hc : vdenL ty vec (penv1 ps) c with
    | none => simp
    | some v =>
      by_cases zero : v = 0
      · simp [zero,result,pad,wp]; omega
      · simp only [zero,ite_false]
        rw [ihb B]
        cases hb : pexecW ty (fu+1) b ps vec with
        | none => simp
        | some r =>
          cases hr : r.ret with
          | some w => simp [result,hr]
          | none =>
            have tail := ihw r B
            simp only [Option.map,result,hr]
            have eq : Command.whileLoop (expr B.length c) (command B.length b) = command B.length (.whileLoop c b) := rfl
            rw [eq,tail]
            cases hw : pexecW ty fu (.whileLoop c b) r.ps r.vec with
            | none => simp
            | some r2 => simp [result,pad,wp]; omega
  | case7 fu c ps vec h1 h2 h3 h4 h5 h6 =>
    intro B
    cases c with
    | primitive st => exact absurd rfl (h1 st)
    | sequence a b => exact absurd rfl (h2 a b)
    | scope b => exact absurd rfl (h3 b)
    | branch c y no => exact absurd rfl (h4 c y no)
    | whileLoop c b =>
      cases fu with
      | zero => exact absurd rfl (h5 c b rfl)
      | succ n => exact absurd rfl (h6 n c b rfl)
    | breakLoop => simp [command,pexecW]
    | invokeScalar p a => simp [command,pexecW]

end Proofs.VecShift
