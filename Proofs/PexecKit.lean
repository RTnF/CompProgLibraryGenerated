import Proofs.PowModStep
import Proofs.IntSim

namespace Proofs.PexecKit
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.PowModStep Proofs.IntSim
open Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.CppState (Cell)

-- Reading a variable: the binding and the cell it names.
theorem penv_ok (ps : PS) (i : Nat) (ty : Ty) (b : CppState.Binding) (c : Cell) (hb : ps.bs[i]? = some b)
    (hc : ps.mem[b.address]? = some c) (ht : c.type = ty) (hv : ty.valid c.value = true) :
    penv ps i ty = some c.value := by
  simp [penv, hb, hc, ht, hv]

theorem pstmt_declare_ok (ps : PS) (ty : Ty) (w : Bool) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v)
    (v' : Int) (hc : ty.convert v = some v') :
    pstmt (.declare ty w e) ps =
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+4⟩ := by
  simp [pstmt, hv, hc]

theorem pstmt_assign_ok (ps : PS) (slot : Nat) (ty : Ty) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v)
    (b : CppState.Binding) (c : Cell) (hb : ps.bs[slot]? = some b) (hc : ps.mem[b.address]? = some c)
    (hct : c.type = ty) (hcv : ty.valid c.value = true) (hw : b.writable = true) (v' : Int) (hconv : ty.convert v = some v') :
    pstmt (.assign slot ty e) ps =
      some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,none,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ := by
  simp [pstmt, hv, hb, hc, hct, hcv, hw, hconv]

theorem pstmt_ret_ok (ps : PS) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v) :
    pstmt (.ret e) ps = some ⟨ps,some v,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ := by
  simp [pstmt, hv]

theorem pexec_branch_true (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (v : Int) (hv : c.denote (penv ps) = some v)
    (hne : v ≠ 0) (r : PR) (hr : pexec fu y ps = some r) :
    pexec fu (.branch c y n) ps = some ⟨r.ps,r.ret,r.cost+c.nodes+1,max (ps.mem.length+ps.bs.length+c.nodes+2) r.need⟩ := by
  rw [pexec]
  simp [hv, hne, hr]

theorem pexec_branch_false (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (hv : c.denote (penv ps) = some 0)
    (r : PR) (hr : pexec fu n ps = some r) :
    pexec fu (.branch c y n) ps = some ⟨r.ps,r.ret,r.cost+c.nodes+1,max (ps.mem.length+ps.bs.length+c.nodes+2) r.need⟩ := by
  rw [pexec]
  simp [hv, hr]

theorem pexec_scope (fu : Nat) (body : Command) (ps : PS) (r : PR) (hr : pexec fu body ps = some r) :
    pexec fu (.scope body) ps =
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.ret,r.cost+1,r.need⟩ := by
  rw [pexec]
  simp [hr]

theorem scope_take (ps ps' : PS) (hm : ps'.mem.length = ps.mem.length) (hb : ps'.bs.length = ps.bs.length) :
    (⟨ps'.mem.take ps.mem.length, ps'.bs.take ps.bs.length⟩ : PS) = ps' := by
  rw [← hm, ← hb]
  simp

theorem pexec_skip (fu : Nat) (ps : PS) :
    pexec fu Sk ps = some ⟨ps,none,0,ps.mem.length+ps.bs.length⟩ := by
  rw [pexec_prim]; rfl

-- `{ st; }` followed by nothing: a braced single statement that neither returns nor changes the layout.
theorem pexec_braced (fu : Nat) (st : NStmt) (ps : PS) (r : PR) (hst : pstmt st ps = some r) (hret : r.ret = none)
    (hm : r.ps.mem.length = ps.mem.length) (hb : r.ps.bs.length = ps.bs.length) :
    pexec fu (.sequence (.scope (.sequence (.primitive st) Sk)) Sk) ps =
      some ⟨r.ps,none,r.cost+1,max r.need (r.ps.mem.length+r.ps.bs.length)⟩ := by
  have q1 : pexec fu (.primitive st) ps = some r := by rw [pexec_prim, hst]
  have q2 := seq_some q1 hret (pexec_skip fu r.ps)
  have q3 := pexec_scope fu _ ps _ q2
  have q4 := scope_take ps r.ps hm hb
  simp only [q4] at q3
  have q5 := seq_some q3 rfl (pexec_skip fu r.ps)
  rw [q5]
  simp [Nat.max_assoc]

end Proofs.PexecKit
