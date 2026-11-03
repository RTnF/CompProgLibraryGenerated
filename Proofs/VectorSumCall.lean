import Proofs.VecPrepare
import Proofs.Generated.VectorSum
import Proofs.DoublingCall
import Proofs.IntSim
import Proofs.ModIntExec

namespace Proofs.VectorSumCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall
open Proofs.CppState (Cell)

-- The caller owns a root vector of `long long` bound at its vector slot `vslot`.
structure VOK (caller : NState) (vslot vb V vsc : Nat) (m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer s64,false,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer s64,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_vs (caller : NState) (params : List CppVectorBindings.Parameter) (hp : params = [.vector s64 false])
    {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOK caller vslot vb V vsc m vbuf) :
    ∃ Sinit, prepare caller params [.vectorReference vslot] = some Sinit ∧
      Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,false,.root vsc⟩]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector s64 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer s64) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer s64) =
        some (vbuf,⟨.integer s64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec]
  simp [bound,bindAll,bindOne,callerP,NState.release,NState.observe,CppState.State.observe]
  simp [NState.charge,NState.observe,CppState.State.observe]
  exact Nat.le_max_left _ _

theorem conv_signed (t : Ty) (hs : t.boolean = false) (hg : t.signed = true) (v : Int) (h : t.valid v = true) :
    t.convert v = some v := by
  unfold Ty.convert
  simp [hs, hg, h]

abbrev bT : Ty := ⟨1, false, true⟩

abbrev condE : NExpr := .binary bT .lt (.variable i32 2) (.cast i32 (.size (.integer s64) (.local 0)))
abbrev bodyE : NExpr := .binary s64 .add (.variable s64 1) (.read s64 (.local 0) (.cast u64 (.variable i32 2)))
abbrev incE : NExpr := .binary i32 .add (.variable i32 2) (.literal i32 1)
abbrev assignS : NStmt := .assign 1 s64 bodyE
abbrev assignI : NStmt := .assign 2 i32 incE
abbrev loopBody : Command := .sequence (.scope (.sequence (.primitive assignS) (.primitive .skip)))
    (.sequence (.primitive assignI) (.primitive .skip))
abbrev loopC : Command := .whileLoop condE loopBody
abbrev declS : NStmt := .declare s64 true (.cast s64 (.literal i32 0))
abbrev declI : NStmt := .declare i32 true (.literal i32 0)
abbrev bodyCmd : Command := .sequence (.primitive declS)
  (.sequence (.scope (.sequence (.primitive declI) (.sequence loopC (.primitive .skip))))
    (.sequence (.primitive (.ret (.variable s64 1))) (.primitive .skip)))

theorem body_eq : Proofs.VectorSumInstance.vector_sum_std_vector_long_long.body = bodyCmd := rfl

-- The callee state in the loop: the sum cell and the counter cell, both writable.
def stS (P : List Cell) (s i : Int) : PS :=
  ⟨P ++ [⟨s64,s⟩,⟨i32,i⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩]⟩

theorem stS_size (P : List Cell) (s i : Int) : (stS P s i).mem.length + (stS P s i).bs.length = P.length + 4 := by
  simp [stS]

theorem env_s (P : List Cell) (s i : Int) (hs : s64.valid s = true) : penv1 (stS P s i) 1 s64 = some s := by
  show penv (stS P s i) 0 s64 = some s
  refine Proofs.PexecKit.penv_ok _ 0 s64 ⟨P.length,true⟩ ⟨s64,s⟩ rfl ?_ rfl hs
  show (P ++ [⟨s64,s⟩,⟨i32,i⟩])[P.length]? = _
  have := Proofs.ModIntExec.get_tail P [⟨s64,s⟩,⟨i32,i⟩] 0
  simpa using this

theorem env_i (P : List Cell) (s i : Int) (hi : i32.valid i = true) : penv1 (stS P s i) 2 i32 = some i := by
  show penv (stS P s i) 1 i32 = some i
  refine Proofs.PexecKit.penv_ok _ 1 i32 ⟨P.length+1,true⟩ ⟨i32,i⟩ rfl ?_ rfl hi
  show (P ++ [⟨s64,s⟩,⟨i32,i⟩])[P.length+1]? = _
  have := Proofs.ModIntExec.get_tail P [⟨s64,s⟩,⟨i32,i⟩] 1
  simpa using this

theorem i32_valid (i : Int) (h0 : -2147483648 ≤ i) (h1 : i < 2147483648) : i32.valid i = true := by
  simp [Ty.valid, i32]; omega

theorem vden_binary (c : VCtx) (env : Nat → Ty → Option Int) (ty : Ty) (op : Binary) (l r : NExpr)
    (h : (NExpr.binary ty op l r).scalarOnly = false) :
    vden c env (.binary ty op l r) =
      (vden c env l).bind fun a => (vden c env r).bind fun b => ty.convert (binaryValue op a b) := by
  rw [vden, if_neg (by rw [h]; decide)]

theorem vden_cast (c : VCtx) (env : Nat → Ty → Option Int) (ty : Ty) (op : NExpr)
    (h : (NExpr.cast ty op).scalarOnly = false) :
    vden c env (.cast ty op) = (vden c env op).bind ty.convert := by
  rw [vden, if_neg (by rw [h]; decide)]

theorem cond_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (s i : Int) (hn : vc.vec.length < 2147483648)
    (h0 : 0 ≤ i) (h1 : i ≤ vc.vec.length) :
    vden vc (penv1 (stS P s i)) condE = some (if i < (vc.vec.length : Int) then 1 else 0) := by
  have e2 := env_i P s i (i32_valid i (by omega) (by omega))
  have hl : (NExpr.variable i32 2).scalarOnly = true := rfl
  have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
  have hc : condE.scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vc.vec.length : Int) = some (vc.vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have hsz : vden vc (penv1 (stS P s i)) (.size (.integer s64) (.local 0)) = some (vc.vec.length : Int) := by
    simp [vden, hr, hty]
  have hb : bT.convert (if i < (vc.vec.length : Int) then 1 else 0) = some (if i < (vc.vec.length : Int) then 1 else 0) := by
    simp only [bT]; unfold Ty.convert; by_cases hh : i < (vc.vec.length : Int) <;> simp [hh]
  have step1 := vden_binary vc (penv1 (stS P s i)) bT .lt (.variable i32 2) (.cast i32 (.size (.integer s64) (.local 0))) hc
  have step2 : vden vc (penv1 (stS P s i)) (.cast i32 (.size (.integer s64) (.local 0))) = some (vc.vec.length : Int) := by
    rw [vden_cast vc _ _ _ hr2, hsz, Option.bind_some, hn']
  have step3 : vden vc (penv1 (stS P s i)) (.variable i32 2) = some i := by
    rw [vden_scalar vc _ _ hl]; exact e2
  rw [step1, step2, step3, Option.bind_some, Option.bind_some]
  have : binaryValue .lt i (vc.vec.length : Int) = if i < (vc.vec.length : Int) then 1 else 0 := rfl
  rw [this]; exact hb

theorem vden_read (c : VCtx) (env : Nat → Ty → Option Int) (ty : Ty) (index : NExpr)
    (h : (NExpr.read ty (.local 0) index).scalarOnly = false) :
    vden c env (.read ty (.local 0) index) =
      if ty = c.ty ∧ index.scalarOnly = true then (index.denote env).bind (elemAt c) else none := by
  rw [vden, if_neg (by rw [h]; decide)]

theorem body_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (s : Int) (i : Nat) (hn : vc.vec.length < 2147483648)
    (hi : i < vc.vec.length) (hs : s64.valid s = true) (x : Int) (hx : vc.vec[i]? = some x)
    (hxv : s64.valid x = true) (hsum : s64.valid (s + x) = true) :
    vden vc (penv1 (stS P s i)) bodyE = some (s + x) := by
  have e1 := env_s P s i hs
  have e2 := env_i P s i (i32_valid i (by omega) (by omega))
  have hb : bodyE.scalarOnly = false := rfl
  have hrd : (NExpr.read s64 (.local 0) (.cast u64 (.variable i32 2))).scalarOnly = false := rfl
  have hl : (NExpr.variable s64 1).scalarOnly = true := rfl
  have hidx : (NExpr.cast u64 (.variable i32 2)).scalarOnly = true := rfl
  have hden : (NExpr.cast u64 (.variable i32 2)).denote (penv1 (stS P s i)) = some (i : Int) := by
    rw [den_cast]
    show ((penv1 (stS P s i)) 2 i32).bind u64.convert = _
    rw [e2, Option.bind_some, convert_u64]
    simp
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hread : vden vc (penv1 (stS P s i)) (NExpr.read s64 (.local 0) (.cast u64 (.variable i32 2))) = some x := by
    rw [vden_read vc _ _ _ hrd, if_pos ⟨hty.symm, hidx⟩, hden, Option.bind_some]
    simp [elemAt, hx, hty, hxv]
  have step1 := vden_binary vc (penv1 (stS P s i)) s64 .add (.variable s64 1)
    (.read s64 (.local 0) (.cast u64 (.variable i32 2))) hb
  have step3 : vden vc (penv1 (stS P s i)) (.variable s64 1) = some s := by
    rw [vden_scalar vc _ _ hl]; exact e1
  rw [step1, step3, hread, Option.bind_some, Option.bind_some]
  exact conv_signed s64 rfl rfl _ hsum

theorem inc_val (vc : VCtx) (P : List Cell) (s : Int) (i : Nat) (hi : i < 2147483647) :
    vden vc (penv1 (stS P s i)) incE = some ((i : Int) + 1) := by
  have e2 := env_i P s i (i32_valid i (by omega) (by omega))
  rw [vden_scalar vc _ _ rfl]
  show ((penv1 (stS P s i)) 2 i32).bind (fun a => ((NExpr.literal i32 1).denote (penv1 (stS P s i))).bind fun b =>
    i32.convert (binaryValue .add a b)) = _
  rw [e2, Option.bind_some]
  have : (NExpr.literal i32 1).denote (penv1 (stS P s i)) = some 1 := by
    rw [den_literal]; rw [if_pos (i32_valid 1 (by omega) (by omega))]
  rw [this, Option.bind_some]
  have hv : binaryValue .add (i : Int) 1 = (i : Int) + 1 := rfl
  rw [hv]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem vwp_cond : vwp condE = (6,6) := by decide
theorem vwp_body : vwp bodyE = (7,7) := by decide
theorem vwp_inc : vwp incE = (3,3) := by decide

theorem set_s (P : List Cell) (s i s' : Int) :
    (⟨(stS P s i).mem.set P.length ⟨s64,s'⟩,(stS P s i).bs⟩ : PS) = stS P s' i := by
  simp [stS, List.set_append_right]

theorem set_i (P : List Cell) (s i i' : Int) :
    (⟨(stS P s i).mem.set (P.length+1) ⟨i32,i'⟩,(stS P s i).bs⟩ : PS) = stS P s i' := by
  have : P.length + 1 = P.length + 1 := rfl
  simp [stS, List.set_append_right]

theorem iter (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (s : Int) (i : Nat) (hn : vc.vec.length < 2147483648)
    (hi : i < vc.vec.length) (hs : s64.valid s = true) (x : Int) (hx : vc.vec[i]? = some x)
    (hxv : s64.valid x = true) (hsum : s64.valid (s + x) = true) (fu : Nat) :
    ∃ r1, pexecV vc fu loopBody (stS P s i) = some r1 ∧ r1.ps = stS P (s+x) (i+1) ∧ r1.ret = none ∧
      r1.cost = 13 ∧ r1.need ≤ P.length + 13 := by
  have hv := body_val vc hty P s i hn hi hs x hx hxv hsum
  have bA : (stS P s i).bs[0]? = some ⟨P.length,true⟩ := by simp [stS]
  have cA : (stS P s i).mem[P.length]? = some ⟨s64,s⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,s⟩,⟨i32,i⟩] 0
    simpa [stS] using this
  have stA := Proofs.VecKit.pstmtV_assign_ok vc (stS P s i) 0 s64 bodyE (s+x) hv ⟨P.length,true⟩ ⟨s64,s⟩ bA cA rfl hs rfl
    (s+x) (conv_signed s64 rfl rfl _ hsum)
  rw [set_s] at stA
  have a1 := (Proofs.VecKit.pexecV_prim vc fu assignS (stS P s i)).trans stA
  have a2 := Proofs.VecKit.seqV_some a1 rfl (Proofs.VecKit.pexecV_skip vc fu (stS P (s+x) i))
  have a3 := Proofs.VecKit.pexecV_scope vc fu _ _ _ a2
  have hsz : (stS P (s+x) i).mem.length = (stS P s i).mem.length ∧ (stS P (s+x) i).bs.length = (stS P s i).bs.length := by
    simp [stS]
  have a4 := Proofs.PexecKit.scope_take (stS P s i) (stS P (s+x) i) hsz.1 hsz.2
  simp only [a4] at a3
  have hi' := inc_val vc P (s+x) i (by omega)
  have bI : (stS P (s+x) i).bs[1]? = some ⟨P.length+1,true⟩ := by simp [stS]
  have cI : (stS P (s+x) i).mem[P.length+1]? = some ⟨i32,i⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,s+x⟩,⟨i32,i⟩] 1
    simpa [stS] using this
  have stI := Proofs.VecKit.pstmtV_assign_ok vc (stS P (s+x) i) 1 i32 incE ((i : Int) + 1) hi' ⟨P.length+1,true⟩ ⟨i32,i⟩ bI cI rfl
    (show i32.valid (i : Int) = true from i32_valid _ (by omega) (by omega)) rfl ((i : Int) + 1) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_i] at stI
  have b1 := (Proofs.VecKit.pexecV_prim vc fu assignI (stS P (s+x) i)).trans stI
  have b2 := Proofs.VecKit.seqV_some b1 rfl (Proofs.VecKit.pexecV_skip vc fu (stS P (s+x) (i+1)))
  have c1 := Proofs.VecKit.seqV_some a3 rfl b2
  refine ⟨_, c1, rfl, rfl, ?_, ?_⟩
  · simp [vwp_body, vwp_inc]
  · simp [vwp_body, vwp_inc, stS]

def psum (l : List Int) (k : Nat) : Int := (l.take k).sum

theorem psum_succ (l : List Int) (i : Nat) (x : Int) (hx : l[i]? = some x) : psum l (i+1) = psum l i + x := by
  simp [psum, List.take_succ, hx, List.sum_append]

theorem loop_run (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (hn : vc.vec.length < 2147483648)
    (hel : ∀ y ∈ vc.vec, s64.valid y = true) (hpre : ∀ k ≤ vc.vec.length, s64.valid (psum vc.vec k) = true) :
    ∀ (m i : Nat), i + m = vc.vec.length → ∀ fu, m + 1 ≤ fu →
      ∃ r, pexecV vc fu loopC (stS P (psum vc.vec i) i) = some r ∧
        r.ps = stS P (psum vc.vec vc.vec.length) vc.vec.length ∧ r.ret = none ∧ r.cost = 20*m+7 ∧
        r.need ≤ P.length + 13 := by
  intro m
  induction m with
  | zero =>
    intro i hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := cond_val vc hty P (psum vc.vec i) i hn (by omega) (by omega)
    have hz : ¬ ((i : Int) < (vc.vec.length : Int)) := by omega
    rw [if_neg hz] at hc
    rw [Proofs.VecKit.pexecV_while, hc]
    have : i = vc.vec.length := by omega
    subst this
    simp only [Bind.bind, Option.bind, ite_true, vwp_cond]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · simp
    · simp [stS]
  | succ m ih =>
    intro i hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hlt : i < vc.vec.length := by omega
    have hc := cond_val vc hty P (psum vc.vec i) i hn (by omega) (by omega)
    have ht : (i : Int) < (vc.vec.length : Int) := by omega
    rw [if_pos ht] at hc
    obtain ⟨x, hx⟩ : ∃ x, vc.vec[i]? = some x := ⟨vc.vec[i], by simp [hlt]⟩
    have hxv := hel x (List.mem_of_getElem? hx)
    have hs := hpre i (by omega)
    have hs' := hpre (i+1) (by omega)
    have hps := psum_succ vc.vec i x hx
    rw [hps] at hs'
    obtain ⟨r1, h1, p1, ret1, c1, n1⟩ := iter vc hty P (psum vc.vec i) i hn hlt hs x hx hxv hs' (fu'+1)
    rw [← hps] at p1
    have p1' : r1.ps = stS P (psum vc.vec (i+1)) ((i+1 : Nat) : Int) := by rw [p1]; simp
    obtain ⟨r2, h2, p2, ret2, c2, n2⟩ := ih (i+1) (by omega) fu' (by omega)
    rw [Proofs.VecKit.pexecV_while, hc]
    simp only [Bind.bind, Option.bind, h1, ret1, p1', h2, vwp_cond]
    refine ⟨⟨r2.ps, r2.ret, 6+1+r1.cost+r2.cost, max ((stS P (psum vc.vec i) i).mem.length +
      (stS P (psum vc.vec i) i).bs.length + 6 + 2) (max r1.need r2.need)⟩, by simp, ?_, ?_, ?_, ?_⟩
    · exact p2
    · exact ret2
    · simp [c1, c2]; omega
    · simp [stS_size, n1, n2]; omega

theorem vwp_lit : vwp (.cast s64 (.literal i32 0)) = (2,2) := by decide
theorem vwp_lit2 : vwp (.literal i32 0) = (1,1) := by decide
theorem vwp_var : vwp (.variable s64 1) = (1,1) := by decide

theorem body_exec (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (hn : vc.vec.length < 2147483648)
    (hel : ∀ y ∈ vc.vec, s64.valid y = true) (hpre : ∀ k ≤ vc.vec.length, s64.valid (psum vc.vec k) = true)
    (fu : Nat) (hfu : vc.vec.length + 1 ≤ fu) :
    ∃ r, pexecV vc fu bodyCmd ⟨P,[]⟩ = some r ∧ r.ret = some (psum vc.vec vc.vec.length) ∧
      r.ps = ⟨P ++ [⟨s64,psum vc.vec vc.vec.length⟩],[⟨P.length,true⟩]⟩ ∧
      r.cost = 20*vc.vec.length + 15 ∧ r.need ≤ P.length + 13 := by
  have z64 : s64.convert 0 = some 0 := conv_signed s64 rfl rfl _ rfl
  have hv1 : vden vc (penv1 ⟨P,[]⟩) (.cast s64 (.literal i32 0)) = some 0 := by
    rw [vden_scalar vc _ _ rfl, den_cast]
    show ((NExpr.literal i32 0).denote (penv1 ⟨P,[]⟩)).bind s64.convert = _
    have h0 : i32.valid 0 = true := rfl
    rw [den_literal, if_pos h0, Option.bind_some, z64]
  have d1 := Proofs.VecKit.pstmtV_declare_ok vc ⟨P,[]⟩ s64 true (.cast s64 (.literal i32 0)) 0 hv1 0 z64
  have hv2 : vden vc (penv1 (⟨P ++ [(⟨s64,0⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS)) (.literal i32 0) = some 0 := by
    have h0 : i32.valid 0 = true := rfl
    rw [vden_scalar vc _ _ rfl, den_literal, if_pos h0]
  have d2 := Proofs.VecKit.pstmtV_declare_ok vc (⟨P ++ [(⟨s64,0⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) i32 true (.literal i32 0) 0 hv2 0
    (conv_signed i32 rfl rfl _ rfl)
  have st0 : (⟨(P ++ [(⟨s64,0⟩ : Cell)]) ++ [(⟨i32,0⟩ : Cell)],[⟨P.length,true⟩] ++ [⟨(P ++ [(⟨s64,0⟩ : Cell)]).length,true⟩]⟩ : PS) =
      stS P (psum vc.vec 0) ((0 : Nat) : Int) := by
    simp [stS, psum]
  rw [st0] at d2
  obtain ⟨rL, hL, pL, retL, cL, nL⟩ := loop_run vc hty P hn hel hpre vc.vec.length 0 (by omega) fu hfu
  have hS := hpre vc.vec.length (Nat.le_refl _)
  have f2 := Proofs.VecKit.seqV_some hL retL (Proofs.VecKit.pexecV_skip vc fu rL.ps)
  have d2' := (Proofs.VecKit.pexecV_prim vc fu declI _).trans d2
  have f3 := Proofs.VecKit.seqV_some d2' rfl f2
  have f4 := Proofs.VecKit.pexecV_scope vc fu _ _ _ f3
  have ps1eq : (⟨(P ++ [(⟨s64,0⟩ : Cell)]),[⟨P.length,true⟩]⟩ : PS) = ⟨P ++ [(⟨s64,0⟩ : Cell)],[] ++ [⟨P.length,true⟩]⟩ := by
    simp
  have take_eq : (⟨(stS P (psum vc.vec vc.vec.length) vc.vec.length).mem.take (P ++ [(⟨s64,0⟩ : Cell)]).length,
      (stS P (psum vc.vec vc.vec.length) vc.vec.length).bs.take [(⟨P.length,true⟩ : CppState.Binding)].length⟩ : PS) =
      (⟨P ++ [(⟨s64,psum vc.vec vc.vec.length⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) := by
    simp [stS, List.take_append, List.take_of_length_le]
  rw [pL] at f4
  simp only [take_eq] at f4
  have e1 := (Proofs.VecKit.pexecV_prim vc fu declS _).trans d1
  have hret : vden vc (penv1 (⟨P ++ [(⟨s64,psum vc.vec vc.vec.length⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS)) (.variable s64 1) =
      some (psum vc.vec vc.vec.length) := by
    rw [vden_scalar vc _ _ rfl]
    show penv _ 0 s64 = _
    refine Proofs.PexecKit.penv_ok _ 0 s64 (⟨P.length,true⟩ : CppState.Binding) (⟨s64,psum vc.vec vc.vec.length⟩ : Cell) rfl ?_ rfl hS
    show (P ++ [(⟨s64,psum vc.vec vc.vec.length⟩ : Cell)])[P.length]? = _
    simp
  have g1 := Proofs.VecKit.pstmtV_ret_ok vc _ _ _ hret
  have g2 := (Proofs.VecKit.pexecV_prim vc fu (.ret (.variable s64 1)) _).trans g1
  have g3 := Proofs.VecKit.seqV_ret (b := .primitive .skip) g2 rfl
  have h4 := Proofs.VecKit.seqV_some f4 rfl g3
  have h5 := Proofs.VecKit.seqV_some e1 rfl h4
  refine ⟨_, h5, rfl, rfl, ?_, ?_⟩
  · simp [vwp_var, vwp_lit, vwp_lit2, cL]
    omega
  · simp [vwp_var, vwp_lit, vwp_lit2, nL, stS]
    omega

set_option maxHeartbeats 4000000 in
theorem vector_sum_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOK caller vslot vb V vsc m vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hn : vec.length < 2147483648) (hel : ∀ y ∈ vec, s64.valid y = true)
    (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true) :
    ∃ Sinit fuel res, prepare caller Proofs.VectorSumInstance.vector_sum_std_vector_long_long.parameters [.vectorReference vslot] = some Sinit ∧
      Proofs.VectorSumInstance.vector_sum_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] = .finished (res,.scalar vec.sum) ∧
      ScalarPost2 caller Sinit res 0 (20*vec.length+20) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_vs caller _ rfl ok
  let vc : VCtx := ⟨s64,false,m,V,vsc,vbuf,vec,hitems,by simp,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have hty : vc.ty = s64 := rfl
  have hvec : vc.vec = vec := rfl
  have fvS : FV vc Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨r,hexec,hret,hrps,hcost,hneed⟩ := body_exec vc hty (callerP caller) (by simpa [hvec] using hn)
    (by simpa [hvec] using hel) (by simpa [hvec] using hpre) (vec.length+1) (Nat.le_refl _)
  have hS : psum vec vec.length = vec.sum := by simp [psum]
  simp only [hvec] at hexec hret hrps
  rw [hS] at hret hrps
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left
  have hSv : s64.valid vec.sum = true := by
    have := hpre vec.length (Nat.le_refl _); rwa [hS] at this
  have hvl : vc.vec.length = vec.length := rfl
  have hpost := call_vec vc caller Proofs.VectorSumInstance.vector_sum_std_vector_long_long [.vectorReference vslot] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) (by rw [sMem]) sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fvS rfl rfl rfl rfl
    (by omega) (by simp [hlen]) (by rw [takeM]) ok.base (by decide) (vec.length+1) r
    (by rw [body_eq]; exact hexec) vec.sum hret s64 rfl hSv (by omega) (by simp) 0 (20*vec.length+20)
    (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [callerP, List.append_assoc, List.take_left]
  rw [hs] at post; exact post

end Proofs.VectorSumCall
