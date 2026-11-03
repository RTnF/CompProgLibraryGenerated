import Proofs.VecCall
import Proofs.PexecKit

namespace Proofs.VecKit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.PowModStep Proofs.PexecKit
open Proofs.VecExpr Proofs.VecStraight
open Proofs.CppState (Cell)

theorem pexecV_prim (vc : VCtx) (fu : Nat) (st : NStmt) (ps : PS) : pexecV vc fu (.primitive st) ps = pstmtV vc st ps := by
  rw [pexecV]

theorem pexecV_seq (vc : VCtx) (fu : Nat) (a b : Command) (ps : PS) : pexecV vc fu (.sequence a b) ps = (do
      let r ← pexecV vc fu a ps
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecV vc fu b r.ps
          some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩) := by
  rw [pexecV]
  congr

theorem seqV_some {vc : VCtx} {fu : Nat} {a b : Command} {ps : PS} {r r2 : PR} (h1 : pexecV vc fu a ps = some r)
    (hr : r.ret = none) (h2 : pexecV vc fu b r.ps = some r2) :
    pexecV vc fu (.sequence a b) ps = some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩ := by
  rw [pexecV_seq, h1]
  simp only [Bind.bind, Option.bind, hr, h2]

theorem seqV_ret {vc : VCtx} {fu : Nat} {a b : Command} {ps : PS} {r : PR} {v : Int} (h1 : pexecV vc fu a ps = some r)
    (hr : r.ret = some v) : pexecV vc fu (.sequence a b) ps = some r := by
  rw [pexecV_seq, h1]
  simp only [Bind.bind, Option.bind, hr]

theorem pexecV_scope (vc : VCtx) (fu : Nat) (body : Command) (ps : PS) (r : PR) (hr : pexecV vc fu body ps = some r) :
    pexecV vc fu (.scope body) ps =
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.ret,r.cost+1,r.need⟩ := by
  rw [pexecV]
  simp [hr]

theorem pexecV_skip (vc : VCtx) (fu : Nat) (ps : PS) :
    pexecV vc fu Sk ps = some ⟨ps,none,0,ps.mem.length+ps.bs.length⟩ := by
  rw [pexecV_prim]; rfl

theorem pexecV_while (vc : VCtx) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) :
    pexecV vc (fu+1) (.whileLoop c b) ps = (do
      let v ← vden vc (penv1 ps) c
      if v = 0 then some ⟨ps,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2⟩
      else do
        let r ← pexecV vc (fu+1) b ps
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecV vc fu (.whileLoop c b) r.ps
            some ⟨r2.ps,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need)⟩) := by
  rw [pexecV]
  congr

theorem pexecV_branch_true (vc : VCtx) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (v : Int)
    (hv : vden vc (penv1 ps) c = some v) (hne : v ≠ 0) (r : PR) (hr : pexecV vc fu y ps = some r) :
    pexecV vc fu (.branch c y n) ps =
      some ⟨r.ps,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need⟩ := by
  rw [pexecV]
  simp [hv, hne, hr]

theorem pexecV_branch_false (vc : VCtx) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS)
    (hv : vden vc (penv1 ps) c = some 0) (r : PR) (hr : pexecV vc fu n ps = some r) :
    pexecV vc fu (.branch c y n) ps =
      some ⟨r.ps,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need⟩ := by
  rw [pexecV]
  simp [hv, hr]

theorem pstmtV_declare_ok (vc : VCtx) (ps : PS) (ty : Ty) (w : Bool) (e : NExpr) (v : Int)
    (hv : vden vc (penv1 ps) e = some v) (v' : Int) (hc : ty.convert v = some v') :
    pstmtV vc (.declare ty w e) ps =
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,none,(vwp e).1+1,
        ps.mem.length+ps.bs.length+(vwp e).2+4⟩ := by
  simp [pstmtV, hv, hc]

theorem pstmtV_assign_ok (vc : VCtx) (ps : PS) (slot : Nat) (ty : Ty) (e : NExpr) (v : Int)
    (hv : vden vc (penv1 ps) e = some v) (b : CppState.Binding) (c : Cell) (hb : ps.bs[slot]? = some b)
    (hc : ps.mem[b.address]? = some c) (hct : c.type = ty) (hcv : ty.valid c.value = true)
    (hw : b.writable = true) (v' : Int) (hconv : ty.convert v = some v') :
    pstmtV vc (.assign (slot+1) ty e) ps =
      some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩ := by
  simp [pstmtV, hv, hb, hc, hct, hcv, hw, hconv]

theorem pstmtV_ret_ok (vc : VCtx) (ps : PS) (e : NExpr) (v : Int) (hv : vden vc (penv1 ps) e = some v) :
    pstmtV vc (.ret e) ps = some ⟨ps,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩ := by
  simp [pstmtV, hv]

theorem pstmtV_check_ok (vc : VCtx) (ps : PS) (e : NExpr) (v : Int) (hv : vden vc (penv1 ps) e = some v) (hne : v ≠ 0) :
    pstmtV vc (.check e) ps = some ⟨ps,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2⟩ := by
  simp [pstmtV, hv, hne]

theorem pexecV_braced (vc : VCtx) (fu : Nat) (st : NStmt) (ps : PS) (r : PR) (hst : pstmtV vc st ps = some r)
    (hret : r.ret = none) (hm : r.ps.mem.length = ps.mem.length) (hb : r.ps.bs.length = ps.bs.length) :
    pexecV vc fu (.sequence (.scope (.sequence (.primitive st) Sk)) Sk) ps =
      some ⟨r.ps,none,r.cost+1,max r.need (r.ps.mem.length+r.ps.bs.length)⟩ := by
  have q1 : pexecV vc fu (.primitive st) ps = some r := by rw [pexecV_prim, hst]
  have q2 := seqV_some q1 hret (pexecV_skip vc fu r.ps)
  have q3 := pexecV_scope vc fu _ ps _ q2
  have q4 := scope_take ps r.ps hm hb
  simp only [q4] at q3
  have q5 := seqV_some q3 rfl (pexecV_skip vc fu r.ps)
  rw [q5]
  simp [Nat.max_assoc]

end Proofs.VecKit
