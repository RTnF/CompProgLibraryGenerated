import Proofs.VecWriteCall
import Proofs.PexecKit

namespace Proofs.VecKitW
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.PowModStep Proofs.PexecKit
open Proofs.VecExpr Proofs.VecStraight Proofs.VecWrite
open Proofs.CppState (Cell)

theorem pexecW_prim (ty0 : Ty) (fu : Nat) (st : NStmt) (ps : PS) (vec : List Int) :
    pexecW ty0 fu (.primitive st) ps vec = pstmtW ty0 st ps vec := by
  rw [pexecW]

theorem pexecW_seq (ty0 : Ty) (fu : Nat) (a b : Command) (ps : PS) (vec : List Int) :
    pexecW ty0 fu (.sequence a b) ps vec = (do
      let r ← pexecW ty0 fu a ps vec
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecW ty0 fu b r.ps r.vec
          some ⟨r2.ps,r2.vec,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩) := by
  rw [pexecW]
  congr

theorem seqW_some {ty0 : Ty} {fu : Nat} {a b : Command} {ps : PS} {vec : List Int} {r r2 : PRW}
    (h1 : pexecW ty0 fu a ps vec = some r) (hr : r.ret = none) (h2 : pexecW ty0 fu b r.ps r.vec = some r2) :
    pexecW ty0 fu (.sequence a b) ps vec = some ⟨r2.ps,r2.vec,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩ := by
  rw [pexecW_seq, h1]
  simp only [Bind.bind, Option.bind, hr, h2]

theorem seqW_ret {ty0 : Ty} {fu : Nat} {a b : Command} {ps : PS} {vec : List Int} {r : PRW} {v : Int}
    (h1 : pexecW ty0 fu a ps vec = some r) (hr : r.ret = some v) : pexecW ty0 fu (.sequence a b) ps vec = some r := by
  rw [pexecW_seq, h1]
  simp only [Bind.bind, Option.bind, hr]

theorem pexecW_scope (ty0 : Ty) (fu : Nat) (body : Command) (ps : PS) (vec : List Int) (r : PRW)
    (hr : pexecW ty0 fu body ps vec = some r) :
    pexecW ty0 fu (.scope body) ps vec =
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.vec,r.ret,r.cost+1,r.need,r.wk⟩ := by
  rw [pexecW]
  simp [hr]

theorem pexecW_skip (ty0 : Ty) (fu : Nat) (ps : PS) (vec : List Int) :
    pexecW ty0 fu Sk ps vec = some ⟨ps,vec,none,0,ps.mem.length+ps.bs.length,0⟩ := by
  rw [pexecW_prim]; rfl

theorem pexecW_while (ty0 : Ty) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vec : List Int) :
    pexecW ty0 (fu+1) (.whileLoop c b) ps vec = (do
      let v ← vdenL ty0 vec (penv1 ps) c
      if v = 0 then some ⟨ps,vec,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2,0⟩
      else do
        let r ← pexecW ty0 (fu+1) b ps vec
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecW ty0 fu (.whileLoop c b) r.ps r.vec
            some ⟨r2.ps,r2.vec,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need),r.wk+r2.wk⟩) := by
  rw [pexecW]
  congr

theorem pstmtW_declare_ok (ty0 : Ty) (ps : PS) (vec : List Int) (ty : Ty) (w : Bool) (e : NExpr) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) e = some v) (v' : Int) (hc : ty.convert v = some v') :
    pstmtW ty0 (.declare ty w e) ps vec =
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,vec,none,(vwp e).1+1,
        ps.mem.length+ps.bs.length+(vwp e).2+4,0⟩ := by
  simp [pstmtW, hv, hc]

theorem pstmtW_assign_ok (ty0 : Ty) (ps : PS) (vec : List Int) (slot : Nat) (ty : Ty) (e : NExpr) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) e = some v) (b : CppState.Binding) (c : Cell) (hb : ps.bs[slot]? = some b)
    (hc : ps.mem[b.address]? = some c) (hct : c.type = ty) (hcv : ty.valid c.value = true)
    (hw : b.writable = true) (v' : Int) (hconv : ty.convert v = some v') :
    pstmtW ty0 (.assign (slot+1) ty e) ps vec =
      some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtW, hv, hb, hc, hct, hcv, hw, hconv]

theorem pstmtW_ret_ok (ty0 : Ty) (ps : PS) (vec : List Int) (e : NExpr) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) e = some v) :
    pstmtW ty0 (.ret e) ps vec = some ⟨ps,vec,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtW, hv]

theorem pstmtW_check_ok (ty0 : Ty) (ps : PS) (vec : List Int) (e : NExpr) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) e = some v) (hne : v ≠ 0) :
    pstmtW ty0 (.check e) ps vec = some ⟨ps,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtW, hv, hne]

theorem pstmtW_write_ok (ty0 : Ty) (ps : PS) (vec : List Int) (iE vE : NExpr) (x : Int) (p : Nat)
    (hx : vdenL ty0 vec (penv1 ps) vE = some x) (hp : vdenL ty0 vec (penv1 ps) iE = some (p : Int))
    (hlt : p < vec.length) (hv : ty0.valid x = true) :
    pstmtW ty0 (.write (.local 0) ty0 iE vE) ps vec =
      some ⟨ps,vec.set p x,none,(vwp vE).1+(vwp iE).1+3,
        ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5,1⟩ := by
  simp [pstmtW, hx, hp, hlt, hv]

end Proofs.VecKitW
