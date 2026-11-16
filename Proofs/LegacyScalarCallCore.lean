import Proofs.MonoidCallCore

/-! Shared scalar helpers retained until the remaining legacy components migrate.
The compatibility namespaces keep their reviewed statements unchanged; this module
contains no Group component programs or Group API correctness proofs. -/

namespace Proofs.GroupCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCallCore
open Proofs.CppState (Cell)

-- The callee state: the caller's reserved memory `P`, the reference bindings `R`, then writable locals `L`.
def ws (P : List Cell) (R : List CppState.Binding) (L : List Cell) : PS :=
  ⟨P ++ L, R ++ (List.range L.length).map fun j => ⟨P.length + j, true⟩⟩

theorem ws_nil (P : List Cell) (R : List CppState.Binding) : ws P R [] = ⟨P,R⟩ := by simp [ws]

theorem ws_size (P : List Cell) (R : List CppState.Binding) (L : List Cell) :
    (ws P R L).mem.length + (ws P R L).bs.length = P.length + R.length + 2 * L.length := by
  simp [ws]; omega

theorem ws_env_ref (P : List Cell) (R : List CppState.Binding) (L : List Cell) (i a : Nat) (w : Bool) (ty : Ty) (v : Int)
    (hR : R[i]? = some ⟨a,w⟩) (ha : P[a]? = some ⟨ty,v⟩) (hv : ty.valid v = true) :
    penv (ws P R L) i ty = some v := by
  have hlt : a < P.length := (List.getElem?_eq_some_iff.mp ha).1
  refine penv_ok _ i ty ⟨a,w⟩ ⟨ty,v⟩ ?_ ?_ rfl hv
  · show (R ++ _)[i]? = _
    have hi : i < R.length := (List.getElem?_eq_some_iff.mp hR).1
    rw [List.getElem?_append_left hi]; exact hR
  · show (P ++ L)[a]? = _
    rw [List.getElem?_append_left hlt]; exact ha

theorem ws_env_loc (P : List Cell) (R : List CppState.Binding) (L : List Cell) (j : Nat) (cell : Cell) (ty : Ty)
    (hj : L[j]? = some cell) (ht : cell.type = ty) (hv : ty.valid cell.value = true) :
    penv (ws P R L) (R.length + j) ty = some cell.value := by
  have hlt : j < L.length := (List.getElem?_eq_some_iff.mp hj).1
  refine penv_ok _ (R.length + j) ty ⟨P.length + j,true⟩ cell ?_ ?_ ht hv
  · show (R ++ _)[R.length + j]? = _
    rw [List.getElem?_append_right (by omega)]
    simp [hlt]
  · show (P ++ L)[P.length + j]? = _
    rw [get_tail]; exact hj

theorem ws_declare (P : List Cell) (R : List CppState.Binding) (L : List Cell) (ty : Ty) (e : NExpr) (v : Int)
    (hv : e.denote (penv (ws P R L)) = some v) (hc : ty.convert v = some v) :
    pstmt (.declare ty true e) (ws P R L) =
      some ⟨ws P R (L ++ [⟨ty,v⟩]),none,e.nodes+1,P.length+R.length+2*L.length+e.nodes+4⟩ := by
  rw [pstmt_declare_ok _ ty true e v hv v hc]
  have hl : (ws P R L).mem.length = P.length + L.length := by simp [ws]
  have h1 : (ws P R L).mem ++ [⟨ty,v⟩] = (ws P R (L ++ [⟨ty,v⟩])).mem := by simp [ws]
  have h2 : (ws P R L).bs ++ [⟨(ws P R L).mem.length,true⟩] = (ws P R (L ++ [⟨ty,v⟩])).bs := by
    simp [ws, List.range_succ, hl]
  have h3 := ws_size P R L
  rw [h1, h2]
  have : (ws P R L).mem.length + (ws P R L).bs.length + e.nodes + 4 = P.length + R.length + 2 * L.length + e.nodes + 4 := by omega
  rw [this]

theorem ws_check (P : List Cell) (R : List CppState.Binding) (L : List Cell) (e : NExpr) (v : Int)
    (hv : e.denote (penv (ws P R L)) = some v) (hne : v ≠ 0) :
    pstmt (.check e) (ws P R L) = some ⟨ws P R L,none,e.nodes+1,P.length+R.length+2*L.length+e.nodes+2⟩ := by
  have h3 := ws_size P R L
  simp [pstmt, hv, hne]
  omega

-- `T r = e; T t = r; return t;` after the references `R`.
abbrev shapeA (k : Nat) (e : NExpr) : Command :=
  .sequence (.primitive (.declare s64 true e))
    (.sequence (.primitive (.declare s64 true (.variable s64 k)))
      (.sequence (.primitive (.ret (.variable s64 (k+1)))) Sk))

theorem shapeA_exec (P : List Cell) (R : List CppState.Binding) (e : NExpr) (v : Int) (hv : s64.valid v = true)
    (hd : e.denote (penv (ws P R [])) = some v) (hn : e.nodes ≤ 10) :
    ∃ r, pexec 1 (shapeA R.length e) (ws P R []) = some r ∧ r.ret = some v ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length + R.length + 30 ∧ r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩] := by
  have s1 := ws_declare P R [] s64 e v hd (convS _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv (ws P R [⟨s64,v⟩]) (R.length + 0) s64 = some v :=
    ws_env_loc P R [⟨s64,v⟩] 0 ⟨s64,v⟩ s64 rfl rfl hv
  have s2 := ws_declare P R [⟨s64,v⟩] s64 (.variable s64 (R.length + 0)) v (by rw [den_variable]; exact e2) (convS _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e3 : penv (ws P R [⟨s64,v⟩, ⟨s64,v⟩]) (R.length + 1) s64 = some v :=
    ws_env_loc P R [⟨s64,v⟩, ⟨s64,v⟩] 1 ⟨s64,v⟩ s64 rfl rfl hv
  have q3 := exec_ret 1 (ws P R ([⟨s64,v⟩] ++ [⟨s64,v⟩])) (.variable s64 (R.length + 1)) v (by rw [den_variable]; exact e3)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  refine ⟨_, q123, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · have := ws_size P R ([⟨s64,v⟩] ++ [⟨s64,v⟩])
    simp [NExpr.nodes, ws] at *; omega
  · simp [ws]

-- `T r = e; assert(r != 0); T t = r; return t;` (a constructor with an assert, inlined).
abbrev nz (k : Nat) : NExpr := .binary bT .ne (.variable s64 k) (.cast s64 (.literal i32 0))

theorem nz_value (env : Nat → Ty → Option Int) (k : Nat) (v : Int) (h : env k s64 = some v) (hne : v ≠ 0) :
    (nz k).denote env = some 1 := by
  have z : (NExpr.cast s64 (.literal i32 0)).denote env = some 0 := by
    rw [den_cast]
    have h0 : i32.valid 0 = true := rfl
    rw [den_literal, if_pos h0, Option.bind_some]
    exact convS 0 rfl
  rw [den_binary, den_variable, z, h]
  simp only [Option.bind_some]
  have : binaryValue .ne v 0 = 1 := by
    show (if (v != 0) then 1 else 0) = 1
    have : (v != 0) = true := by simp; exact hne
    rw [this]; rfl
  rw [this]
  rfl

theorem refs1_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 true false])
    (hr : prog.result = ResultKind.scalar s64) (hbody : Scalar prog.body = true)
    (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : s64.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+100 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ s64 false hp sa ba x ca (by simp) valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret s64 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem refs2b_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 true false,.scalar s64 true false])
    (hr : prog.result = ResultKind.scalar s64) (hbody : Scalar prog.body = true)
    (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : s64.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+100 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ s64 false false hp sa sb ba bb _ _ ca cb (by simp) (by simp) valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret s64 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

-- `return x;` for a read-only reference parameter (the accessor `x()`).
theorem env2 (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 0 s64 = some x ∧ penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 1 s64 = some y :=
  ⟨ws_env_ref P _ [] 0 a false s64 x rfl ha hxv, ws_env_ref P _ [] 1 b false s64 y rfl hb hyv⟩

abbrev addE : NExpr := .binary s64 .add (.variable s64 0) (.variable s64 1)
theorem addE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 s64 = some x) (h1 : env 1 s64 = some y)
    (hxy : s64.valid (x+y) = true) : addE.denote env = some (x+y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convS _ hxy

def copy_tail : Command :=
  .sequence (.primitive (.declare s64 true (.variable s64 0)))
    (.sequence (.primitive (.declare s64 true (.variable s64 1)))
      (.sequence (.primitive (.ret (.variable s64 2))) Sk))

def default_shape (checked : Bool) (e : NExpr) : Command :=
  .sequence (.primitive (.declare s64 true e))
    (if checked then .sequence (.primitive (.check (nz 0))) copy_tail else copy_tail)

theorem copy_tail_exec (P : List Cell) (v : Int) (hv : s64.valid v = true) :
    ∃ r, pexec 1 copy_tail (ws P [] [⟨s64,v⟩]) = some r ∧ r.ret = some v ∧
      r.cost ≤ 10 ∧ r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩] := by
  have e0 : penv (ws P [] [⟨s64,v⟩]) 0 s64 = some v :=
    ws_env_loc _ _ _ 0 ⟨s64,v⟩ s64 rfl rfl hv
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [⟨s64,v⟩] s64 (.variable s64 0) v
    (by rw [den_variable]; exact e0) (convS _ hv))
  have e1 : penv (ws P [] [⟨s64,v⟩,⟨s64,v⟩]) 1 s64 = some v :=
    ws_env_loc _ _ _ 1 ⟨s64,v⟩ s64 rfl rfl hv
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P [] [⟨s64,v⟩,⟨s64,v⟩] s64 (.variable s64 1) v
    (by rw [den_variable]; exact e1) (convS _ hv))
  have e2 : penv (ws P [] [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩]) 2 s64 = some v :=
    ws_env_loc _ _ _ 2 ⟨s64,v⟩ s64 rfl rfl hv
  have q3 := exec_ret 1 (ws P [] [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩]) (.variable s64 2) v
    (by rw [den_variable]; exact e2)
  have q := seq_some q1 rfl (seq_some q2 rfl q3)
  refine ⟨_,q,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws]
  · simp [ws]

theorem default_exec (P : List Cell) (checked : Bool) (e : NExpr) (v : Int)
    (hv : s64.valid v = true) (he : e.denote (penv (ws P [] [])) = some v)
    (hn : e.nodes ≤ 10) (hne : checked = true → v ≠ 0) :
    ∃ r, pexec 1 (default_shape checked e) ⟨P,[]⟩ = some r ∧ r.ret = some v ∧
      r.cost ≤ 30 ∧ r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩] := by
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [] s64 e v he (convS _ hv))
  obtain ⟨r,tail,ret,cost,need,mem⟩ := copy_tail_exec P v hv
  cases checked with
  | false =>
    have q := seq_some q1 rfl tail
    rw [ws_nil] at q
    refine ⟨_,q,ret,?_,?_,mem⟩
    · simpa using (by omega : e.nodes+1+r.cost ≤ 30)
    · simp; omega
  | true =>
    have e0 : penv (ws P [] [⟨s64,v⟩]) 0 s64 = some v :=
      ws_env_loc _ _ _ 0 ⟨s64,v⟩ s64 rfl rfl hv
    have qc := (pexec_prim 1 _ _).trans (ws_check P [] [⟨s64,v⟩] (nz 0) 1
      (nz_value _ 0 v e0 (hne rfl)) (by decide))
    have q := seq_some q1 rfl (seq_some qc rfl tail)
    rw [ws_nil] at q
    refine ⟨_,q,ret,?_,?_,mem⟩
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega

theorem default_correct (prog : NProgram) (checked : Bool) (e : NExpr) (v : Int)
    (hp : prog.parameters = []) (hb : prog.body = default_shape checked e)
    (hr : prog.result = ResultKind.scalar s64) (he : ∀ env, e.denote env = some v)
    (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (hne : checked = true → v ≠ 0)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨s64,v⟩ : Cell),⟨s64,v⟩,⟨s64,v⟩]).take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  obtain ⟨r,ran,ret,cost,need,mem⟩ := default_exec (callerP caller) checked e v hv (he _) hn hne
  rw [← hb] at ran
  have scalar : Scalar prog.body = true := by
    rw [hb]; cases checked <;> simp [default_shape,copy_tail,Scalar,hs,nz,NExpr.scalarOnly]
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by simp [callerP]) valid lengths strict base scalar 1 r ran v ret s64 hr hv
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simpa only [mem,takeM] using post

theorem prep_rrv (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar s64 true false,.scalar s64 true false,.scalar s64 false true])
    (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v1 v2 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (e : NExpr) (n : Int) (hs : e.scalarOnly = true) (hty : e.resultType = s64)
    (value : e.denote (envOf caller) = some n) (valid : caller.frame.state.wellFormed = true)
    (nv : s64.valid n = true) :
    ∃ t, Good ((caller.charge 1 1).charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨s64,n⟩] ∧
        Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have core2 : Core caller ((caller.charge 1 1).charge 1 1) := (core_charge caller 1 1).trans (core_charge _ 1 1)
  obtain ⟨t,ran,good⟩ := scalar_eval e ((caller.charge 1 1).charge 1 1) n hs (by rw [envOf_core core2]; exact value)
  refine ⟨t,good,?_⟩
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
  have c2' : (caller.charge 1 1).scalarCell s2 s64 = some (b2,⟨s64,v2⟩) := c2
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨s64,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨s64,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have res3 : resolve ((caller.charge 1 1).charge 1 1) (.scalar s64 false true) (.value e) = some (t,.scalar s64 true n) := by
    simp [resolve,hty,ran]
  have res1 : resolve caller (.scalar s64 true false) (.scalarReference s1) =
      some (caller.charge 1 1,.scalarAddress s64 b1.address false) := by simp [resolve,c1]
  have res2 : resolve (caller.charge 1 1) (.scalar s64 true false) (.scalarReference s2) =
      some ((caller.charge 1 1).charge 1 1,.scalarAddress s64 b2.address false) := by simp [resolve,c2']
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,res3]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g := good.2.2.2.2.1
  simp only [charge_scalar_peak] at g ⊢
  exact Nat.le_trans (by omega) (Nat.le_max_left _ _)

abbrev applyE : NExpr := .binary s64 .add (.binary s64 .mul (.variable s64 0) (.variable s64 2)) (.variable s64 1)

theorem applyE_den (env : Nat → Ty → Option Int) (a b x : Int) (h0 : env 0 s64 = some a) (h1 : env 1 s64 = some b)
    (h2 : env 2 s64 = some x) (hm : s64.valid (a*x) = true) (hs : s64.valid (a*x + b) = true) :
    applyE.denote env = some (a*x + b) := by
  rw [den_binary, den_binary, den_variable, den_variable, den_variable, h0, h2, h1]
  simp only [Option.bind_some]
  have e1 : binaryValue .mul a x = a * x := rfl
  rw [e1, convS _ hm]
  simp only [Option.bind_some]
  have e2 : binaryValue .add (a * x) b = a * x + b := rfl
  rw [e2]
  exact convS _ hs

set_option maxHeartbeats 4000000 in
theorem prepare_values2 (ty : Ty) (caller : NState) (params : List Proofs.CppVectorBindings.Parameter)
    (hp : params = [.scalar ty false true, .scalar ty false true]) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = ty) (t2ty : e2.resultType = ty)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : ty.valid v1 = true) (n2 : ty.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller params [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨ty,v1⟩,⟨ty,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a,b]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a,b]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a,b]
  have res1 : resolve caller (.scalar ty false true) (.value e1) = some (t1,.scalar ty true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar ty false true) (.value e2) = some (t2,.scalar ty true v2) := by
    simp [resolve,t2ty,ran2]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  omega

end Proofs.GroupCall


namespace Proofs.GroupCallInt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCallCore
open Proofs.CppState (Cell)

theorem convI (v : Int) (h : i32.valid v = true) : i32.convert v = some v :=
  by unfold Ty.convert; simp [i32, h]

def ws (P : List Cell) (R : List CppState.Binding) (L : List Cell) : PS :=
  ⟨P ++ L, R ++ (List.range L.length).map fun j => ⟨P.length + j, true⟩⟩

theorem ws_nil (P : List Cell) (R : List CppState.Binding) : ws P R [] = ⟨P,R⟩ := by simp [ws]

theorem ws_size (P : List Cell) (R : List CppState.Binding) (L : List Cell) :
    (ws P R L).mem.length + (ws P R L).bs.length = P.length + R.length + 2 * L.length := by
  simp [ws]; omega

theorem ws_env_loc (P : List Cell) (R : List CppState.Binding) (L : List Cell) (j : Nat) (cell : Cell) (ty : Ty)
    (hj : L[j]? = some cell) (ht : cell.type = ty) (hv : ty.valid cell.value = true) :
    penv (ws P R L) (R.length + j) ty = some cell.value := by
  have hlt : j < L.length := (List.getElem?_eq_some_iff.mp hj).1
  refine penv_ok _ (R.length + j) ty ⟨P.length + j,true⟩ cell ?_ ?_ ht hv
  · show (R ++ _)[R.length + j]? = _
    rw [List.getElem?_append_right (by omega)]
    simp [hlt]
  · show (P ++ L)[P.length + j]? = _
    rw [get_tail]; exact hj

theorem ws_declare (P : List Cell) (R : List CppState.Binding) (L : List Cell) (ty : Ty) (e : NExpr) (v : Int)
    (hv : e.denote (penv (ws P R L)) = some v) (hc : ty.convert v = some v) :
    pstmt (.declare ty true e) (ws P R L) =
      some ⟨ws P R (L ++ [⟨ty,v⟩]),none,e.nodes+1,P.length+R.length+2*L.length+e.nodes+4⟩ := by
  rw [pstmt_declare_ok _ ty true e v hv v hc]
  have hl : (ws P R L).mem.length = P.length + L.length := by simp [ws]
  have h1 : (ws P R L).mem ++ [⟨ty,v⟩] = (ws P R (L ++ [⟨ty,v⟩])).mem := by simp [ws]
  have h2 : (ws P R L).bs ++ [⟨(ws P R L).mem.length,true⟩] = (ws P R (L ++ [⟨ty,v⟩])).bs := by
    simp [ws, List.range_succ, hl]
  have h3 := ws_size P R L
  rw [h1, h2]
  have : (ws P R L).mem.length + (ws P R L).bs.length + e.nodes + 4 = P.length + R.length + 2 * L.length + e.nodes + 4 := by omega
  rw [this]

theorem ws_check (P : List Cell) (R : List CppState.Binding) (L : List Cell) (e : NExpr) (v : Int)
    (hv : e.denote (penv (ws P R L)) = some v) (hne : v ≠ 0) :
    pstmt (.check e) (ws P R L) = some ⟨ws P R L,none,e.nodes+1,P.length+R.length+2*L.length+e.nodes+2⟩ := by
  have h3 := ws_size P R L
  simp [pstmt, hv, hne]
  omega

-- `T r = e; T t = r; return t;` after the references `R`.
abbrev nz (k : Nat) : NExpr := .binary bT .ne (.variable i32 k) (.literal i32 0)

theorem nz_value (env : Nat → Ty → Option Int) (k : Nat) (v : Int) (h : env k i32 = some v) (hne : v ≠ 0) :
    (nz k).denote env = some 1 := by
  have z : (NExpr.literal i32 0).denote env = some 0 := by
    have h0 : i32.valid 0 = true := rfl
    rw [den_literal, if_pos h0]
  rw [den_binary, den_variable, z, h]
  simp only [Option.bind_some]
  have : binaryValue .ne v 0 = 1 := by
    show (if (v != 0) then 1 else 0) = 1
    have : (v != 0) = true := by simp; exact hne
    rw [this]; rfl
  rw [this]
  rfl

def copy_tail : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 0)))
    (.sequence (.primitive (.declare i32 true (.variable i32 1)))
      (.sequence (.primitive (.ret (.variable i32 2))) Sk))

def default_shape (checked : Bool) (e : NExpr) : Command :=
  .sequence (.primitive (.declare i32 true e))
    (if checked then .sequence (.primitive (.check (nz 0))) copy_tail else copy_tail)

theorem copy_tail_exec (P : List Cell) (v : Int) (hv : i32.valid v = true) :
    ∃ r, pexec 1 copy_tail (ws P [] [⟨i32,v⟩]) = some r ∧ r.ret = some v ∧
      r.cost ≤ 10 ∧ r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨i32,v⟩,⟨i32,v⟩,⟨i32,v⟩] := by
  have e0 : penv (ws P [] [⟨i32,v⟩]) 0 i32 = some v :=
    ws_env_loc _ _ _ 0 ⟨i32,v⟩ i32 rfl rfl hv
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [⟨i32,v⟩] i32 (.variable i32 0) v
    (by rw [den_variable]; exact e0) (convI _ hv))
  have e1 : penv (ws P [] [⟨i32,v⟩,⟨i32,v⟩]) 1 i32 = some v :=
    ws_env_loc _ _ _ 1 ⟨i32,v⟩ i32 rfl rfl hv
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P [] [⟨i32,v⟩,⟨i32,v⟩] i32 (.variable i32 1) v
    (by rw [den_variable]; exact e1) (convI _ hv))
  have e2 : penv (ws P [] [⟨i32,v⟩,⟨i32,v⟩,⟨i32,v⟩]) 2 i32 = some v :=
    ws_env_loc _ _ _ 2 ⟨i32,v⟩ i32 rfl rfl hv
  have q3 := exec_ret 1 (ws P [] [⟨i32,v⟩,⟨i32,v⟩,⟨i32,v⟩]) (.variable i32 2) v
    (by rw [den_variable]; exact e2)
  have q := seq_some q1 rfl (seq_some q2 rfl q3)
  refine ⟨_,q,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws]
  · simp [ws]

theorem default_exec (P : List Cell) (checked : Bool) (e : NExpr) (v : Int)
    (hv : i32.valid v = true) (he : e.denote (penv (ws P [] [])) = some v)
    (hn : e.nodes ≤ 10) (hne : checked = true → v ≠ 0) :
    ∃ r, pexec 1 (default_shape checked e) ⟨P,[]⟩ = some r ∧ r.ret = some v ∧
      r.cost ≤ 30 ∧ r.need ≤ P.length+40 ∧ r.ps.mem = P ++ [⟨i32,v⟩,⟨i32,v⟩,⟨i32,v⟩] := by
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [] i32 e v he (convI _ hv))
  obtain ⟨r,tail,ret,cost,need,mem⟩ := copy_tail_exec P v hv
  cases checked with
  | false =>
    have q := seq_some q1 rfl tail
    rw [ws_nil] at q
    refine ⟨_,q,ret,?_,?_,mem⟩
    · simpa using (by omega : e.nodes+1+r.cost ≤ 30)
    · simp; omega
  | true =>
    have e0 : penv (ws P [] [⟨i32,v⟩]) 0 i32 = some v :=
      ws_env_loc _ _ _ 0 ⟨i32,v⟩ i32 rfl rfl hv
    have qc := (pexec_prim 1 _ _).trans (ws_check P [] [⟨i32,v⟩] (nz 0) 1
      (nz_value _ 0 v e0 (hne rfl)) (by decide))
    have q := seq_some q1 rfl (seq_some qc rfl tail)
    rw [ws_nil] at q
    refine ⟨_,q,ret,?_,?_,mem⟩
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega

theorem default_correct (prog : NProgram) (checked : Bool) (e : NExpr) (v : Int)
    (hp : prog.parameters = []) (hb : prog.body = default_shape checked e)
    (hr : prog.result = ResultKind.scalar i32) (he : ∀ env, e.denote env = some v)
    (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
    (hne : checked = true → v ≠ 0)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,v⟩ : Cell),⟨i32,v⟩,⟨i32,v⟩]).take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  obtain ⟨r,ran,ret,cost,need,mem⟩ := default_exec (callerP caller) checked e v hv (he _) hn hne
  rw [← hb] at ran
  have scalar : Scalar prog.body = true := by
    rw [hb]; cases checked <;> simp [default_shape,copy_tail,Scalar,hs,nz,NExpr.scalarOnly]
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by simp [callerP]) valid lengths strict base scalar 1 r ran v ret i32 hr hv
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simpa only [mem,takeM] using post

end Proofs.GroupCallInt
