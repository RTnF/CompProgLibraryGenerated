import Proofs.MultiVecN
import Proofs.GenState

namespace Proofs.MultiKitN
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.PowModStep Proofs.PexecKit
open Proofs.VecExpr Proofs.VecStraight Proofs.VecWrite Proofs.MultiVecN Proofs.GenState
open Proofs.CppState (Cell)

theorem pexecM_prim (mv : MV) (fu : Nat) (st : NStmt) (ps : PS) (vv : Nat → List Int) :
    pexecM mv fu (.primitive st) ps vv = pstmtM mv st ps vv := by
  rw [pexecM]

theorem pexecM_seq (mv : MV) (fu : Nat) (a b : Command) (ps : PS) (vv : Nat → List Int) :
    pexecM mv fu (.sequence a b) ps vv = (do
      let r ← pexecM mv fu a ps vv
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexecM mv fu b r.ps r.vv
          some ⟨r2.ps,r2.vv,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩) := by
  rw [pexecM]
  congr

theorem seqM_some {mv : MV} {fu : Nat} {a b : Command} {ps : PS} {vv : Nat → List Int} {r r2 : PRM}
    (h1 : pexecM mv fu a ps vv = some r) (hr : r.ret = none) (h2 : pexecM mv fu b r.ps r.vv = some r2) :
    pexecM mv fu (.sequence a b) ps vv = some ⟨r2.ps,r2.vv,r2.ret,r.cost+r2.cost,max r.need r2.need,r.wk+r2.wk⟩ := by
  rw [pexecM_seq, h1]
  simp only [Bind.bind, Option.bind, hr, h2]

theorem seqM_ret {mv : MV} {fu : Nat} {a b : Command} {ps : PS} {vv : Nat → List Int} {r : PRM} {v : Int}
    (h1 : pexecM mv fu a ps vv = some r) (hr : r.ret = some v) : pexecM mv fu (.sequence a b) ps vv = some r := by
  rw [pexecM_seq, h1]
  simp only [Bind.bind, Option.bind, hr]

theorem pexecM_scope (mv : MV) (fu : Nat) (body : Command) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (hr : pexecM mv fu body ps vv = some r) :
    pexecM mv fu (.scope body) ps vv =
      some ⟨⟨r.ps.mem.take ps.mem.length,r.ps.bs.take ps.bs.length⟩,r.vv,r.ret,r.cost+1,r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hr]

theorem pexecM_skip (mv : MV) (fu : Nat) (ps : PS) (vv : Nat → List Int) :
    pexecM mv fu Sk ps vv = some ⟨ps,vv,none,0,ps.mem.length+ps.bs.length,0⟩ := by
  rw [pexecM_prim]; rfl

theorem pexecM_while (mv : MV) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vv : Nat → List Int) :
    pexecM mv (fu+1) (.whileLoop c b) ps vv = (do
      let v ← vdenM mv vv (penvN mv.nv ps) c
      if v = 0 then some ⟨ps,vv,none,(vwp c).1+1,ps.mem.length+ps.bs.length+(vwp c).2+2,0⟩
      else do
        let r ← pexecM mv (fu+1) b ps vv
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexecM mv fu (.whileLoop c b) r.ps r.vv
            some ⟨r2.ps,r2.vv,r2.ret,(vwp c).1+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+(vwp c).2+2) (max r.need r2.need),r.wk+r2.wk⟩) := by
  rw [pexecM]
  congr

theorem pstmtM_declare_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (ty : Ty) (w : Bool) (e : NExpr) (v : Int)
    (hv : vdenN mv vv (penvN mv.nv ps) e = some v) (v' : Int) (hc : ty.convert v = some v') :
    pstmtM mv (.declare ty w e) ps vv =
      some ⟨⟨ps.mem ++ [⟨ty,v'⟩],ps.bs ++ [⟨ps.mem.length,w⟩]⟩,vv,none,(vwp e).1+1,
        ps.mem.length+ps.bs.length+(vwp e).2+4,0⟩ := by
  simp [pstmtM, hv, hc]

theorem pstmtM_assign_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (slot : Nat) (ty : Ty) (e : NExpr) (v : Int)
    (hv : vdenN mv vv (penvN mv.nv ps) e = some v) (b : CppState.Binding) (c : Cell) (hb : ps.bs[slot]? = some b)
    (hc : ps.mem[b.address]? = some c) (hct : c.type = ty) (hcv : ty.valid c.value = true)
    (hw : b.writable = true) (v' : Int) (hconv : ty.convert v = some v') :
    pstmtM mv (.assign (mv.nv+slot) ty e) ps vv =
      some ⟨⟨ps.mem.set b.address ⟨ty,v'⟩,ps.bs⟩,vv,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtM, hv, hb, hc, hct, hcv, hw, hconv]

theorem pstmtM_ret_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (e : NExpr) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) e = some v) :
    pstmtM mv (.ret e) ps vv = some ⟨ps,vv,some v,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtM, hv]

theorem pstmtM_check_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (e : NExpr) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) e = some v) (hne : v ≠ 0) :
    pstmtM mv (.check e) ps vv = some ⟨ps,vv,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
  simp [pstmtM, hv, hne]

theorem pstmtM_write_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (k : Nat) (hk : k < mv.nv) (hf : mv.flat k = true) (iE vE : NExpr) (x : Int) (p : Nat)
    (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : p < (vv k).length) (hv : (mv.ty k).valid x = true) :
    pstmtM mv (.write (.local k) (mv.ty k) iE vE) ps vv =
      some ⟨ps,upd vv k ((vv k).set p x),none,(vwp vE).1+(vwp iE).1+3,
        ps.mem.length+ps.bs.length+iE.nodes+vE.nodes+(vwp vE).2+(vwp iE).2+5,1⟩ := by
  simp [pstmtM, hx, hp, hlt, hv, hk, hf]

theorem pstmtM_writeRow_ok (mv : MV) (ps : PS) (vv : Nat → List Int) (k : Nat) (hk : k < mv.nv) (hfk : mv.flat k = false)
    (hwn : mv.wN k = true) (idx iE vE : NExpr) (x : Int) (a p : Nat)
    (hidxS : idx.scalarOnly = true) (hiS : iE.scalarOnly = true) (hvS : vE.scalarOnly = true)
    (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (ha : vdenM mv vv (penvN mv.nv ps) idx = some (a : Int))
    (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int)) (hal : a < mv.wrows k)
    (hpl : p < (vv (rowKey k a)).length) (hv : (mv.ty k).valid x = true) :
    pstmtM mv (.write (.row (.local k) (.integer (mv.ty k)) idx) (mv.ty k) iE vE) ps vv =
      some ⟨ps, upd vv (rowKey k a) ((vv (rowKey k a)).set p x), none, vE.nodes+idx.nodes+iE.nodes+6,
        ps.mem.length+ps.bs.length+idx.nodes+iE.nodes+vE.nodes+10, 1⟩ := by
  simp [pstmtM, hx, ha, hp, hk, hfk, hwn, hidxS, hiS, hvS, hal, hpl, hv]

theorem vdenM_scalar (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (e : NExpr) (h : e.scalarOnly = true) :
    vdenM mv vv env e = e.denote env := by
  unfold vdenM; simp [h]

/-- Reading variable `nv + k` (variables below `nv` are the vectors) of a well-typed cell. -/
theorem vdenN_of_M {mv : MV} {vv : Nat → List Int} {env : Nat → Ty → Option Int} {e : NExpr} {v : Int}
    (h : vdenM mv vv env e = some v) (hs : e.scalarOnly = true) : vdenN mv vv env e = some v := by
  rw [vdenN_scalar mv vv env e hs]; rw [vdenM_scalar mv vv env e hs] at h; exact h

theorem gSM_env (nv : Nat) (P cs : List Cell) (k : Nat) (c : Cell) (hk : cs[k]? = some c) (hv : c.type.valid c.value = true) :
    penvN nv (gS P cs) (nv + k) c.type = some c.value := by
  have hlt : k < cs.length := (List.getElem?_eq_some_iff.mp hk).1
  unfold penvN
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact Proofs.PexecKit.penv_ok (gS P cs) k c.type ⟨P.length + k, true⟩ c (gS_bs_get P cs k hlt)
    (by rw [gS_mem_get P cs k hlt]; exact hk) rfl hv

theorem gSM_decl (mv : MV) (P cs : List Cell) (vv : Nat → List Int) (ty : Ty) (e : NExpr) (v v' : Int)
    (hv : vdenN mv vv (penvN mv.nv (gS P cs)) e = some v) (hc : ty.convert v = some v') :
    pstmtM mv (.declare ty true e) (gS P cs) vv =
      some ⟨gS P (cs ++ [⟨ty, v'⟩]), vv, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 4, 0⟩ := by
  have h := pstmtM_declare_ok mv (gS P cs) vv ty true e v hv v' hc
  have hmem : (gS P cs).mem ++ [⟨ty, v'⟩] = (gS P (cs ++ [⟨ty, v'⟩])).mem := by
    simp [gS]
  have hbs : (gS P cs).bs ++ [⟨(gS P cs).mem.length, true⟩] = (gS P (cs ++ [⟨ty, v'⟩])).bs := by
    simp [gS, List.range_succ]
  rw [h, hmem, hbs]
  simp only [Option.some.injEq, PRM.mk.injEq, true_and, gS_mem_len, gS_bs_len]
  exact ⟨by omega, trivial⟩

theorem gSM_assign (mv : MV) (P cs : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cs.length) (ty : Ty)
    (e : NExpr) (v v' : Int) (hv : vdenN mv vv (penvN mv.nv (gS P cs)) e = some v) (c : Cell) (hc : cs[slot]? = some c)
    (hct : c.type = ty) (hcv : ty.valid c.value = true) (hconv : ty.convert v = some v') :
    pstmtM mv (.assign (mv.nv + slot) ty e) (gS P cs) vv =
      some ⟨gS P (cs.set slot ⟨ty, v'⟩), vv, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 2, 0⟩ := by
  have hb := gS_bs_get P cs slot hslot
  have hm : (gS P cs).mem[(⟨P.length + slot, true⟩ : CppState.Binding).address]? = some c := by
    show (gS P cs).mem[P.length + slot]? = some c
    rw [gS_mem_get P cs slot hslot]; exact hc
  have h := pstmtM_assign_ok mv (gS P cs) vv slot ty e v hv ⟨P.length + slot, true⟩ c hb hm hct hcv rfl v' hconv
  have key : (⟨(gS P cs).mem.set (P.length + slot) ⟨ty, v'⟩, (gS P cs).bs⟩ : PS) = gS P (cs.set slot ⟨ty, v'⟩) := by
    simp only [gS, List.length_set]
    rw [List.set_append_right _ _ (by omega)]
    simp
  rw [h]
  dsimp only
  rw [key]
  simp only [Option.some.injEq, PRM.mk.injEq, true_and, gS_mem_len, gS_bs_len]
  exact ⟨by omega, trivial⟩

end Proofs.MultiKitN
