import Proofs.MonoidCallCore
import Proofs.Generated.Group

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

abbrev shapeB (k : Nat) (e : NExpr) : Command :=
  .sequence (.primitive (.declare s64 true e))
    (.sequence (.primitive (.check (nz k)))
      (.sequence (.primitive (.declare s64 true (.variable s64 k)))
        (.sequence (.primitive (.ret (.variable s64 (k+1)))) Sk)))

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

theorem shapeB_exec (P : List Cell) (R : List CppState.Binding) (e : NExpr) (v : Int) (hv : s64.valid v = true)
    (hd : e.denote (penv (ws P R [])) = some v) (hn : e.nodes ≤ 10) (hne : v ≠ 0) :
    ∃ r, pexec 1 (shapeB R.length e) (ws P R []) = some r ∧ r.ret = some v ∧ r.cost ≤ 30 ∧
      r.need ≤ P.length + R.length + 40 ∧ r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩] := by
  have s1 := ws_declare P R [] s64 e v hd (convS _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv (ws P R [⟨s64,v⟩]) (R.length + 0) s64 = some v :=
    ws_env_loc P R [⟨s64,v⟩] 0 ⟨s64,v⟩ s64 rfl rfl hv
  have c2 := ws_check P R [⟨s64,v⟩] (nz R.length) 1 (nz_value _ R.length v e2 hne) (by decide)
  have qc := (pexec_prim 1 _ _).trans c2
  have s3 := ws_declare P R [⟨s64,v⟩] s64 (.variable s64 (R.length + 0)) v (by rw [den_variable]; exact e2) (convS _ hv)
  have q3 := (pexec_prim 1 _ _).trans s3
  have e3 : penv (ws P R [⟨s64,v⟩, ⟨s64,v⟩]) (R.length + 1) s64 = some v :=
    ws_env_loc P R [⟨s64,v⟩, ⟨s64,v⟩] 1 ⟨s64,v⟩ s64 rfl rfl hv
  have q4 := exec_ret 1 (ws P R ([⟨s64,v⟩] ++ [⟨s64,v⟩])) (.variable s64 (R.length + 1)) v (by rw [den_variable]; exact e3)
  have q34 := seq_some q3 rfl q4
  have q234 := seq_some qc rfl q34
  have q1234 := seq_some q1 rfl q234
  refine ⟨_, q1234, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · have := ws_size P R ([⟨s64,v⟩] ++ [⟨s64,v⟩])
    simp [NExpr.nodes, ws] at *; omega
  · simp [ws]

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
theorem retvar_exec (P : List Cell) (a : Nat) (x : Int) (hxv : s64.valid x = true) (ha : P[a]? = some ⟨s64,x⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable s64 0))) Sk) ⟨P,[⟨a,false⟩]⟩ = some r ∧
      r.ret = some x ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a,false⟩]⟩ 0 s64 = some x := penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl ha rfl hxv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩]⟩ (.variable s64 0) x (by rw [den_variable]; exact e0)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem groupsum_x_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : s64.valid x = true) (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_long_long_x.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_long_long_x.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar_exec (callerP caller) ba.address x hxv (P_cell caller sa ba x ca)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem groupmul_x_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : s64.valid x = true) (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_long_long_x.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_long_long_x.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar_exec (callerP caller) ba.address x hxv (P_cell caller sa ba x ca)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem env2 (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 0 s64 = some x ∧ penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 1 s64 = some y :=
  ⟨ws_env_ref P _ [] 0 a false s64 x rfl ha hxv, ws_env_ref P _ [] 1 b false s64 y rfl hb hyv⟩

abbrev addE : NExpr := .binary s64 .add (.variable s64 0) (.variable s64 1)
abbrev mulE : NExpr := .binary s64 .mul (.variable s64 0) (.variable s64 1)
abbrev negE : NExpr := .unary s64 .neg (.variable s64 0)
abbrev invE : NExpr := .divrem s64 false (.cast s64 (.literal i32 1)) (.variable s64 0)

theorem addE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 s64 = some x) (h1 : env 1 s64 = some y)
    (hxy : s64.valid (x+y) = true) : addE.denote env = some (x+y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convS _ hxy

theorem mulE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 s64 = some x) (h1 : env 1 s64 = some y)
    (hxy : s64.valid (x*y) = true) : mulE.denote env = some (x*y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convS _ hxy

theorem negE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 s64 = some x)
    (hx : s64.valid (-x) = true) : negE.denote env = some (-x) := by
  simp only [negE, NExpr.denote, h0, Option.bind_some]
  exact convS _ hx

theorem invE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 s64 = some x) (hx : x = 1 ∨ x = -1) :
    invE.denote env = some x := by
  have one : (NExpr.cast s64 (.literal i32 1)).denote env = some 1 := by
    rw [den_cast]
    have h1 : i32.valid 1 = true := rfl
    rw [den_literal, if_pos h1, Option.bind_some]
    exact convS 1 rfl
  simp only [invE, NExpr.denote, one, h0, Option.bind_some]
  rcases hx with rfl | rfl
  · decide
  · decide

theorem groupsum_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hxy : s64.valid (x+y) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.op_GroupSum_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.op_GroupSum_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x+y)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x+y) hxy 20 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2 (callerP caller) ba.address bb.address x y hxv hyv (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeA_exec (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] addE (x+y) hxy
    (addE_den _ x y e0 e1 hxy) (by decide)
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupsum_inv_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : s64.valid x = true) (hnx : s64.valid (-x) = true) (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_long_long_inv.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_long_long_inv.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar (-x)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 (-x) hnx 20 ?_
  intro P hP
  subst hP
  have e0 : penv (ws (callerP caller) [⟨ba.address,false⟩] []) 0 s64 = some x :=
    ws_env_ref _ _ [] 0 ba.address false s64 x rfl (P_cell caller sa ba x ca) hxv
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeA_exec (callerP caller) [⟨ba.address,false⟩] negE (-x) hnx
    (negE_den _ x e0 hnx) (by decide)
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupmul_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hxy : s64.valid (x*y) = true) (hne : x*y ≠ 0)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.op_GroupMul_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.op_GroupMul_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x*y)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x*y) hxy 30 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2 (callerP caller) ba.address bb.address x y hxv hyv (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] mulE (x*y) hxy
    (mulE_den _ x y e0 e1 hxy) (by decide) hne
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupmul_inv_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hx : x = 1 ∨ x = -1) (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_long_long_inv.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_long_long_inv.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  have hxv : s64.valid x = true := by rcases hx with rfl | rfl <;> rfl
  have hne : x ≠ 0 := by rcases hx with rfl | rfl <;> decide
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 30 ?_
  intro P hP
  subst hP
  have e0 : penv (ws (callerP caller) [⟨ba.address,false⟩] []) 0 s64 = some x :=
    ws_env_ref _ _ [] 0 ba.address false s64 x rfl (P_cell caller sa ba x ca) hxv
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [⟨ba.address,false⟩] invE x hxv
    (invE_den _ x e0 hx) (by decide) hne
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

-- The constructor with an assert: `assert(x != 0); return x;`.
theorem groupmul_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (hne : v ≠ 0) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 80 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ s64 rfl e v hs hty value valid hv
  have takeM2 : (callerP caller ++ [(⟨s64,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have e0 : penv ⟨callerP caller ++ [⟨s64,v⟩],[⟨(callerP caller).length,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨(callerP caller).length,true⟩ ⟨s64,v⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,v⟩] 0) rfl hv
  have hd := nz_value (penv ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩) 0 v e0 hne
  have c1 : pstmt (.check (nz 0)) ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩ =
      some ⟨⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩,none,(nz 0).nodes+1,
        (callerP caller ++ [(⟨s64,v⟩ : Cell)]).length+1+(nz 0).nodes+2⟩ := by
    simp only [pstmt, hd]
    simp
  have qc := (pexec_prim 1 _ _).trans c1
  have q := exec_ret 1 ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩ (.variable s64 0) v
    (by rw [den_variable]; exact e0)
  have qq := seq_some qc rfl q
  have gw := good.2.2.1
  have hpost := call_scalar caller Proofs.GroupInstance.GroupMul_long_long_new0 [.value e] Sinit
    (callerP caller ++ [(⟨s64,v⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)] hprep (by rw [sSlots]; rfl)
    sMem sBind sBase sScope sFrame (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base
    (by decide) 1 _ qq _ rfl s64 rfl hv (by simp [NExpr.nodes]) (by simp)
    e.nodes 80 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM2] at post
  exact post

theorem groupsum_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correct _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

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

theorem groupsum_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_long_long_new1.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  default_correct _ false (.cast s64 (.literal i32 0)) 0 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base


theorem groupmul_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_long_long_new1.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  default_correct _ true (.cast s64 (.literal i32 1)) 1 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base


theorem prep_rrrr (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar s64 true false,.scalar s64 true false,.scalar s64 true false,.scalar s64 true false])
    (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,v4⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+9 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  obtain ⟨i4,_,_,m4,_,w4⟩ := scalarCell_facts c4
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have l4 : b4.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m4).1
  have c2' : (caller.charge 1 1).scalarCell s2 s64 = some (b2,⟨s64,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 s64 = some (b3,⟨s64,v3⟩) := c3
  have c4' : (((caller.charge 1 1).charge 1 1).charge 1 1).scalarCell s4 s64 = some (b4,⟨s64,v4⟩) := c4
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨s64,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨s64,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have h3 := pad b3 v3 l3 m3
  have h4 := pad b4 v4 l4 m4
  rw [hp]
  have wt : (true = true → True) := fun _ => trivial
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3',c4']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,h4,w1,w2,w3,w4]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

theorem prep_rrr (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar s64 true false,.scalar s64 true false,.scalar s64 true false])
    (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3] =
        some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have c2' : (caller.charge 1 1).scalarCell s2 s64 = some (b2,⟨s64,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 s64 = some (b3,⟨s64,v3⟩) := c3
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨s64,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨s64,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have h3 := pad b3 v3 l3 m3
  rw [hp]
  have wt : (true = true → True) := fun _ => trivial
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,w1,w2,w3]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _


-- Generic preparation for two read-only references followed by a value argument.
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

theorem apply_body : Proofs.GroupInstance.GroupAffine_long_long_apply.body = .sequence (.primitive (.ret applyE)) Sk := rfl

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
theorem affine_apply_correct (caller : NState) (sa sb sx : Nat) (ba bb bx : CppState.Binding) (a b x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,a⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,b⟩))
    (cx : caller.scalarCell sx s64 = some (bx,⟨s64,x⟩))
    (hav : s64.valid a = true) (hbv : s64.valid b = true) (hxv : s64.valid x = true)
    (hm : s64.valid (a*x) = true) (hsum : s64.valid (a*x + b) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_apply.parameters
        [.scalarReference sa,.scalarReference sb,.scalarReference sx] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_apply.callFuel fuel caller [.scalarReference sa,.scalarReference sb,.scalarReference sx] =
        .finished (res,.scalar (a*x + b)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrr caller _ rfl sa sb sx ba bb bx a b x ca cb cx valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hPa := P_cell caller sa ba a ca
  have hPb := P_cell caller sb bb b cb
  have hPx := P_cell caller sx bx x cx
  let refs : List CppState.Binding := [⟨ba.address,false⟩,⟨bb.address,false⟩,⟨bx.address,false⟩]
  have e0 : penv ⟨callerP caller,refs⟩ 0 s64 = some a :=
    penv_ok _ 0 s64 ⟨ba.address,false⟩ ⟨s64,a⟩ rfl hPa rfl hav
  have e1 : penv ⟨callerP caller,refs⟩ 1 s64 = some b :=
    penv_ok _ 1 s64 ⟨bb.address,false⟩ ⟨s64,b⟩ rfl hPb rfl hbv
  have e2 : penv ⟨callerP caller,refs⟩ 2 s64 = some x :=
    penv_ok _ 2 s64 ⟨bx.address,false⟩ ⟨s64,x⟩ rfl hPx rfl hxv
  have q := exec_ret 1 ⟨callerP caller,refs⟩ applyE (a*x + b) (applyE_den _ a b x e0 e1 e2 hm hsum)
  have hexec : pexec 1 Proofs.GroupInstance.GroupAffine_long_long_apply.body ⟨callerP caller,refs⟩ =
      some ⟨⟨callerP caller,refs⟩,some (a*x + b),applyE.nodes+1,(callerP caller).length+3+applyE.nodes+2⟩ := by
    rw [apply_body]; simpa [refs] using q
  have hpost := call_scalar caller Proofs.GroupInstance.GroupAffine_long_long_apply
    [.scalarReference sa,.scalarReference sb,.scalarReference sx] Sinit (callerP caller) refs
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak (by omega) (by rw [takeM]) valid lengths
    strict base (by rw [apply_body]; simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl s64 rfl hsum
    (by simp [NExpr.nodes]) (by simp [refs]) 0 80 (by simp only [NExpr.nodes] at *; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post

theorem refs4_correct (prog : NProgram)
    (hp : prog.parameters = [.scalar s64 true false,.scalar s64 true false,.scalar s64 true false,.scalar s64 true false])
    (hr : prog.result = ResultKind.scalar s64) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,v4⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : s64.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrrr caller _ hp s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret s64 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

abbrev compAE : NExpr := .binary s64 .mul (.variable s64 0) (.variable s64 2)
abbrev compBE : NExpr := .binary s64 .add (.binary s64 .mul (.variable s64 1) (.variable s64 2)) (.variable s64 3)

theorem compA_body : Proofs.GroupInstance.GroupAffine_long_long_op__a.body = .sequence (.primitive (.ret compAE)) Sk := rfl
theorem compB_body : Proofs.GroupInstance.GroupAffine_long_long_op__b.body = .sequence (.primitive (.ret compBE)) Sk := rfl

theorem compA_exec (P : List Cell) (a1 a2 a3 a4 : Nat) (v1 v2 v3 v4 : Int)
    (h1 : P[a1]? = some ⟨s64,v1⟩) (h3 : P[a3]? = some ⟨s64,v3⟩)
    (g1 : s64.valid v1 = true) (g3 : s64.valid v3 = true) (gm : s64.valid (v1*v3) = true) :
    ∃ r, pexec 1 Proofs.GroupInstance.GroupAffine_long_long_op__a.body ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some (v1*v3) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 0 s64 = some v1 :=
    penv_ok _ 0 s64 ⟨a1,false⟩ ⟨s64,v1⟩ rfl h1 rfl g1
  have e2 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 2 s64 = some v3 :=
    penv_ok _ 2 s64 ⟨a3,false⟩ ⟨s64,v3⟩ rfl h3 rfl g3
  have den : compAE.denote (penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩) = some (v1*v3) := by
    rw [den_binary, den_variable, den_variable, e0, e2]
    simp only [Option.bind_some]
    have e1 : binaryValue .mul v1 v3 = v1 * v3 := rfl
    rw [e1]; exact convS _ gm
  have q := exec_ret 1 ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ compAE (v1*v3) den
  refine ⟨_, by rw [compA_body]; exact q, rfl, ?_, ?_, rfl⟩ <;> simp [NExpr.nodes] <;> omega

theorem compB_exec (P : List Cell) (a1 a2 a3 a4 : Nat) (v1 v2 v3 v4 : Int)
    (h2 : P[a2]? = some ⟨s64,v2⟩) (h3 : P[a3]? = some ⟨s64,v3⟩) (h4 : P[a4]? = some ⟨s64,v4⟩)
    (g2 : s64.valid v2 = true) (g3 : s64.valid v3 = true) (g4 : s64.valid v4 = true)
    (gm : s64.valid (v2*v3) = true) (gs : s64.valid (v2*v3 + v4) = true) :
    ∃ r, pexec 1 Proofs.GroupInstance.GroupAffine_long_long_op__b.body ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some (v2*v3 + v4) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e1 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 1 s64 = some v2 :=
    penv_ok _ 1 s64 ⟨a2,false⟩ ⟨s64,v2⟩ rfl h2 rfl g2
  have e2 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 2 s64 = some v3 :=
    penv_ok _ 2 s64 ⟨a3,false⟩ ⟨s64,v3⟩ rfl h3 rfl g3
  have e3 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 3 s64 = some v4 :=
    penv_ok _ 3 s64 ⟨a4,false⟩ ⟨s64,v4⟩ rfl h4 rfl g4
  have den : compBE.denote (penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩) = some (v2*v3 + v4) := by
    rw [den_binary, den_binary, den_variable, den_variable, den_variable, e1, e2, e3]
    simp only [Option.bind_some]
    have m1 : binaryValue .mul v2 v3 = v2 * v3 := rfl
    rw [m1, convS _ gm]
    simp only [Option.bind_some]
    have m2 : binaryValue .add (v2 * v3) v4 = v2 * v3 + v4 := rfl
    rw [m2]; exact convS _ gs
  have q := exec_ret 1 ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ compBE (v2*v3 + v4) den
  refine ⟨_, by rw [compB_body]; exact q, rfl, ?_, ?_, rfl⟩ <;> simp [NExpr.nodes] <;> omega

theorem affine_compose_a_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,v4⟩))
    (g1 : s64.valid v1 = true) (g3 : s64.valid v3 = true) (gm : s64.valid (v1*v3) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_op__a.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_op__a.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v1*v3)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  refine refs4_correct _ rfl rfl (by rw [compA_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v1*v3) gm 10 ?_
  intro P hP
  subst hP
  obtain ⟨r,h,hr,hc,hn,hm⟩ := compA_exec (callerP caller) b1.address b2.address b3.address b4.address v1 v2 v3 v4
    (P_cell caller s1 b1 v1 c1) (P_cell caller s3 b3 v3 c3) g1 g3 gm
  exact ⟨r,h,hr,hc,hn,by rw [hm]; simpa using take_P caller []⟩

theorem affine_compose_b_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 s64 = some (b2,⟨s64,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 s64 = some (b4,⟨s64,v4⟩))
    (g2 : s64.valid v2 = true) (g3 : s64.valid v3 = true) (g4 : s64.valid v4 = true)
    (gm : s64.valid (v2*v3) = true) (gs : s64.valid (v2*v3 + v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_op__b.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_op__b.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v2*v3 + v4)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  refine refs4_correct _ rfl rfl (by rw [compB_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v2*v3 + v4) gs 10 ?_
  intro P hP
  subst hP
  obtain ⟨r,h,hr,hc,hn,hm⟩ := compB_exec (callerP caller) b1.address b2.address b3.address b4.address v1 v2 v3 v4
    (P_cell caller s2 b2 v2 c2) (P_cell caller s3 b3 v3 c3) (P_cell caller s4 b4 v4 c4) g2 g3 g4 gm gs
  exact ⟨r,h,hr,hc,hn,by rw [hm]; simpa using take_P caller []⟩


/-! ### `GroupAffine`: the accessors, the identity and the inverse -/

theorem retvar2a_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable s64 0))) Sk) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some x ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 s64 = some x := penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl ha rfl hxv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ (.variable s64 0) x (by rw [den_variable]; exact e0)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem retvar2b_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable s64 1))) Sk) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some y ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 s64 = some y := penv_ok _ 1 s64 ⟨b,false⟩ ⟨s64,y⟩ rfl hb rfl hyv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ (.variable s64 1) y (by rw [den_variable]; exact e1)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem affine_a_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_a.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_a.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar2a_exec (callerP caller) ba.address bb.address x y hxv hyv
    (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem affine_b_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_b.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_b.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar y) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 y hyv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar2b_exec (callerP caller) ba.address bb.address x y hxv hyv
    (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem affine_e_a_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_e__a.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_e__a.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem affine_e_b_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_e__b.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_e__b.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem groupsum_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_long_long_e.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_long_long_e.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

-- The static `e()` of a class whose constructor asserts: `declare r = e; assert(r != 0); declare s = r; return s`.
theorem e_check_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = shapeB 0 e) (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (hne : v ≠ 0) (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [] e v hv (by rw [ws_nil]; exact he _) hn hne
  rw [ws_nil] at h1
  simp only [List.length_nil] at h1
  rw [← hb] at h1
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base
    (by rw [hb]; simp [Scalar, hs, NExpr.scalarOnly, nz]) 1 _ h1 _ h2 s64 hr hv
    (by simp at h4 ⊢; omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have e3 : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [h5]
    have : callerP caller ++ [(⟨s64,v⟩ : Cell),⟨s64,v⟩] = callerP caller ++ [(⟨s64,v⟩ : Cell),⟨s64,v⟩] := rfl
    exact take_P caller _
  rw [e3] at post
  exact post

theorem groupmul_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_long_long_e.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_long_long_e.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_check_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) (by decide) caller valid lengths strict base

/-! `GroupAffine::inv`: the integer divisions `1 / a` and `-b / a` (truncating, as in C++) -/

abbrev invAE : NExpr := .divrem s64 false (.cast s64 (.literal i32 1)) (.variable s64 0)
abbrev invBE : NExpr := .divrem s64 false (.unary s64 .neg (.variable s64 1)) (.variable s64 0)

theorem invAE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 s64 = some x) (hne : x ≠ 0)
    (hq : s64.valid ((1 : Int).tdiv x) = true) : invAE.denote env = some ((1 : Int).tdiv x) := by
  have one : (NExpr.cast s64 (.literal i32 1)).denote env = some 1 := by
    rw [den_cast]
    have h1 : i32.valid 1 = true := rfl
    rw [den_literal, if_pos h1, Option.bind_some]
    exact convS 1 rfl
  rw [den_divrem, one, den_variable, h0]
  simp only [Option.bind_some, checkedDivRem]
  have hb : (x == 0) = false := by simp [hne]
  rw [hb]
  simp only [Bool.false_eq_true, if_false]
  rw [if_neg (by simp [hq])]
  exact convS _ hq

theorem invBE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 s64 = some x) (h1 : env 1 s64 = some y)
    (hne : x ≠ 0) (hn : s64.valid (-y) = true) (hq : s64.valid ((-y).tdiv x) = true) :
    invBE.denote env = some ((-y).tdiv x) := by
  have neg : (NExpr.unary s64 .neg (.variable s64 1)).denote env = some (-y) := by
    simp only [NExpr.denote, h1, Option.bind_some, unaryValue]
    exact convS _ hn
  rw [den_divrem, neg, den_variable, h0]
  simp only [Option.bind_some, checkedDivRem]
  have hb : (x == 0) = false := by simp [hne]
  rw [hb]
  simp only [Bool.false_eq_true, if_false]
  rw [if_neg (by rw [hq]; decide)]
  exact convS _ hq

theorem affine_inv_a_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hne : x ≠ 0) (hq : s64.valid ((1 : Int).tdiv x) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_inv__a.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_inv__a.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((1 : Int).tdiv x)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 _ hq 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨ba.address,false⟩ ⟨s64,x⟩ rfl (P_cell caller sa ba x ca) rfl hxv
  have q := exec_ret 1 ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ invAE ((1 : Int).tdiv x)
    (invAE_den _ x e0 hne hq)
  have hb : Proofs.GroupInstance.GroupAffine_long_long_inv__a.body = .sequence (.primitive (.ret invAE)) Sk := rfl
  rw [hb]
  refine ⟨_, q, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simpa using take_P caller []

theorem affine_inv_b_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hne : x ≠ 0) (hn : s64.valid (-y) = true)
    (hq : s64.valid ((-y).tdiv x) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_inv__b.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_inv__b.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((-y).tdiv x)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 _ hq 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨ba.address,false⟩ ⟨s64,x⟩ rfl (P_cell caller sa ba x ca) rfl hxv
  have e1 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 1 s64 = some y :=
    penv_ok _ 1 s64 ⟨bb.address,false⟩ ⟨s64,y⟩ rfl (P_cell caller sb bb y cb) rfl hyv
  have q := exec_ret 1 ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ invBE ((-y).tdiv x)
    (invBE_den _ x y e0 e1 hne hn hq)
  have hb : Proofs.GroupInstance.GroupAffine_long_long_inv__b.body = .sequence (.primitive (.ret invBE)) Sk := rfl
  rw [hb]
  refine ⟨_, q, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simpa using take_P caller []

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

theorem value2_correct (prog : NProgram) (second : Bool)
    (hp : prog.parameters = [.scalar s64 false true,.scalar s64 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable s64 (if second then 1 else 0)))) Sk)
    (hr : prog.result = ResultKind.scalar s64) (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (if second then y else x)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_values2 s64 caller _ hp e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 valid hx hy
  let P := callerP caller
  let M := P ++ [(⟨s64,x⟩ : Cell),⟨s64,y⟩]
  let bs : List CppState.Binding := [⟨P.length,true⟩,⟨P.length+1,true⟩]
  have ev : penv ⟨M,bs⟩ (if second then 1 else 0) s64 = some (if second then y else x) := by
    cases second
    · exact penv_ok _ 0 s64 ⟨P.length,true⟩ ⟨s64,x⟩ rfl
        (by simp [M,P]) rfl hx
    · exact penv_ok _ 1 s64 ⟨P.length+1,true⟩ ⟨s64,y⟩ rfl
        (by simp [M,P]) rfl hy
  have takeM : M.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  have q := exec_ret 1 (⟨M,bs⟩ : PS) (.variable s64 (if second then 1 else 0)) (if second then y else x)
    (by rw [den_variable]; exact ev)
  rw [← hb] at q
  have hexec := q
  have peak1 := g1.2.2.2.2.1
  have peak2 := g2.2.2.2.2.1
  have work1 := g1.2.2.1
  have work2 := g2.2.2.1
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [P,callerP]
  have hpost := call_scalar caller prog [.value e1,.value e2] Sinit M bs
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [M]; omega) (by rw [takeM]) valid lengths strict base
    (by rw [hb]; simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl s64 hr
    (by cases second <;> assumption) (by simp [M,bs,P,NExpr.nodes]) (by simp [M,bs,P])
    (e1.nodes+e2.nodes) 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [takeM] using post⟩

theorem affine_new_a_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_new0__a.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_new0__a.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2_correct _ false rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem affine_new_b_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : s64.valid x = true) (hy : s64.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_new0__b.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_new0__b.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar y) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2_correct _ true rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem affine_default_a_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_new1__a.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_new1__a.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem affine_default_b_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_long_long_new1__b.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_long_long_new1__b.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

-- The original hidden friends have the same complete scalar programs as their namespace counterparts.
theorem groupsum_friend_program : Proofs.GroupInstance.GroupSum_long_long_op = Proofs.GroupInstance.op_GroupSum_long_long := rfl
theorem groupmul_friend_program : Proofs.GroupInstance.GroupMul_long_long_op = Proofs.GroupInstance.op_GroupMul_long_long := rfl
theorem affine_friend_a_program : Proofs.GroupInstance.GroupAffine_long_long_op_friend__a = Proofs.GroupInstance.GroupAffine_long_long_op__a := rfl
theorem affine_friend_b_program : Proofs.GroupInstance.GroupAffine_long_long_op_friend__b = Proofs.GroupInstance.GroupAffine_long_long_op__b := rfl

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

theorem P_cellI (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) : (callerP caller)[ba.address]? = some ⟨i32,x⟩ := by
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma

theorem convI (v : Int) (h : i32.valid v = true) : i32.convert v = some v :=
  by unfold Ty.convert; simp [i32, h]

theorem const_correctI (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar i32)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
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
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have q := exec_ret 1 ⟨callerP caller,[]⟩ e v (he _)
  have hexec : pexec 1 prog.body ⟨callerP caller,[]⟩ = some ⟨⟨callerP caller,[]⟩,some v,e.nodes+1,
      (callerP caller).length+0+e.nodes+2⟩ := by rw [hb]; simpa using q
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by rw [hb]; simp [Scalar, hs]) 1 _ hexec _ rfl i32 hr hv
    (by simp; omega) (by simp) 0 70 (by simp; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post

theorem ctor_correctI (prog : NProgram) (hp : prog.parameters = [.scalar i32 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable i32 0))) Sk) (hr : prog.result = ResultKind.scalar i32)
    (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v)
    (hv : i32.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ i32 hp e v hs hty value valid hv
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have takeM2 : (callerP caller ++ [(⟨i32,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  have e0 : penv ⟨callerP caller ++ [⟨i32,v⟩],[⟨(callerP caller).length,true⟩]⟩ 0 i32 = some v :=
    penv_ok _ 0 i32 ⟨(callerP caller).length,true⟩ ⟨i32,v⟩ rfl (by simpa using get_tail (callerP caller) [⟨i32,v⟩] 0) rfl hv
  have q := exec_ret 1 ⟨callerP caller ++ [⟨i32,v⟩],[⟨(callerP caller).length,true⟩]⟩ (.variable i32 0) v
    (by rw [den_variable]; exact e0)
  have hexec : pexec 1 prog.body ⟨callerP caller ++ [⟨i32,v⟩],[⟨(callerP caller).length,true⟩]⟩ =
      some ⟨(⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[(⟨(callerP caller).length,true⟩ : CppState.Binding)]⟩ : PS),some v,
        (NExpr.variable i32 0).nodes+1,
        (callerP caller ++ [(⟨i32,v⟩ : Cell)]).length+1+(NExpr.variable i32 0).nodes+2⟩ := by rw [hb]; simpa using q
  have gw := good.2.2.1
  have hpost := call_scalar caller prog [.value e] Sinit
    (callerP caller ++ [(⟨i32,v⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame
    (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base (by rw [hb]; simp [Scalar, NExpr.scalarOnly])
    1 _ hexec _ rfl i32 hr hv (by simp [NExpr.nodes]) (by simp) e.nodes 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM2] at post
  exact post

theorem e_correctI (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.declare i32 true e))
      (.sequence (.primitive (.declare i32 true (.variable i32 0))) (.sequence (.primitive (.ret (.variable i32 1))) Sk)))
    (hr : prog.result = ResultKind.scalar i32)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
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
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have s1 := pstmt_declare_ok ⟨callerP caller,[]⟩ i32 true e v (he _) v (convI _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e1 : penv ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[] ++ [⟨(callerP caller).length,true⟩]⟩ 0 i32 = some v :=
    penv_ok _ 0 i32 ⟨(callerP caller).length,true⟩ ⟨i32,v⟩ (by simp) (by simp) rfl hv
  have s2 := pstmt_declare_ok ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[] ++ [⟨(callerP caller).length,true⟩]⟩ i32 true
    (.variable i32 0) v (by rw [den_variable]; exact e1) v (convI _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e2 : penv ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)] ++ [(⟨i32,v⟩ : Cell)],
      [] ++ [⟨(callerP caller).length,true⟩] ++ [⟨(callerP caller ++ [(⟨i32,v⟩ : Cell)]).length,true⟩]⟩ 1 i32 = some v :=
    penv_ok _ 1 i32 ⟨(callerP caller).length+1,true⟩ ⟨i32,v⟩ (by simp) (by simp) rfl hv
  have q3 := exec_ret 1 ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)] ++ [(⟨i32,v⟩ : Cell)],
      [] ++ [⟨(callerP caller).length,true⟩] ++ [⟨(callerP caller ++ [(⟨i32,v⟩ : Cell)]).length,true⟩]⟩
    (.variable i32 1) v (by rw [den_variable]; exact e2)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  have hexec := q123
  rw [← hb] at hexec
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by rw [hb]; simp [Scalar, hs, NExpr.scalarOnly]) 1 _ hexec _ rfl i32 hr hv
    (by simp [NExpr.nodes] at hn ⊢; omega) (by simp) 0 70 (by simp [NExpr.nodes] at hn ⊢; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have e3 : callerP caller ++ [(⟨i32,v⟩ : Cell)] ++ [(⟨i32,v⟩ : Cell)] = callerP caller ++ [(⟨i32,v⟩ : Cell),⟨i32,v⟩] := by
    simp
  rw [e3, take_P caller] at post
  exact post

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
  .sequence (.primitive (.declare i32 true e))
    (.sequence (.primitive (.declare i32 true (.variable i32 k)))
      (.sequence (.primitive (.ret (.variable i32 (k+1)))) Sk))

theorem shapeA_exec (P : List Cell) (R : List CppState.Binding) (e : NExpr) (v : Int) (hv : i32.valid v = true)
    (hd : e.denote (penv (ws P R [])) = some v) (hn : e.nodes ≤ 10) :
    ∃ r, pexec 1 (shapeA R.length e) (ws P R []) = some r ∧ r.ret = some v ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length + R.length + 30 ∧ r.ps.mem = P ++ [⟨i32,v⟩,⟨i32,v⟩] := by
  have s1 := ws_declare P R [] i32 e v hd (convI _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv (ws P R [⟨i32,v⟩]) (R.length + 0) i32 = some v :=
    ws_env_loc P R [⟨i32,v⟩] 0 ⟨i32,v⟩ i32 rfl rfl hv
  have s2 := ws_declare P R [⟨i32,v⟩] i32 (.variable i32 (R.length + 0)) v (by rw [den_variable]; exact e2) (convI _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e3 : penv (ws P R [⟨i32,v⟩, ⟨i32,v⟩]) (R.length + 1) i32 = some v :=
    ws_env_loc P R [⟨i32,v⟩, ⟨i32,v⟩] 1 ⟨i32,v⟩ i32 rfl rfl hv
  have q3 := exec_ret 1 (ws P R ([⟨i32,v⟩] ++ [⟨i32,v⟩])) (.variable i32 (R.length + 1)) v (by rw [den_variable]; exact e3)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  refine ⟨_, q123, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · have := ws_size P R ([⟨i32,v⟩] ++ [⟨i32,v⟩])
    simp [NExpr.nodes, ws] at *; omega
  · simp [ws]

-- `T r = e; assert(r != 0); T t = r; return t;` (a constructor with an assert, inlined).
abbrev nz (k : Nat) : NExpr := .binary bT .ne (.variable i32 k) (.literal i32 0)

abbrev shapeB (k : Nat) (e : NExpr) : Command :=
  .sequence (.primitive (.declare i32 true e))
    (.sequence (.primitive (.check (nz k)))
      (.sequence (.primitive (.declare i32 true (.variable i32 k)))
        (.sequence (.primitive (.ret (.variable i32 (k+1)))) Sk)))

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

theorem shapeB_exec (P : List Cell) (R : List CppState.Binding) (e : NExpr) (v : Int) (hv : i32.valid v = true)
    (hd : e.denote (penv (ws P R [])) = some v) (hn : e.nodes ≤ 10) (hne : v ≠ 0) :
    ∃ r, pexec 1 (shapeB R.length e) (ws P R []) = some r ∧ r.ret = some v ∧ r.cost ≤ 30 ∧
      r.need ≤ P.length + R.length + 40 ∧ r.ps.mem = P ++ [⟨i32,v⟩,⟨i32,v⟩] := by
  have s1 := ws_declare P R [] i32 e v hd (convI _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv (ws P R [⟨i32,v⟩]) (R.length + 0) i32 = some v :=
    ws_env_loc P R [⟨i32,v⟩] 0 ⟨i32,v⟩ i32 rfl rfl hv
  have c2 := ws_check P R [⟨i32,v⟩] (nz R.length) 1 (nz_value _ R.length v e2 hne) (by decide)
  have qc := (pexec_prim 1 _ _).trans c2
  have s3 := ws_declare P R [⟨i32,v⟩] i32 (.variable i32 (R.length + 0)) v (by rw [den_variable]; exact e2) (convI _ hv)
  have q3 := (pexec_prim 1 _ _).trans s3
  have e3 : penv (ws P R [⟨i32,v⟩, ⟨i32,v⟩]) (R.length + 1) i32 = some v :=
    ws_env_loc P R [⟨i32,v⟩, ⟨i32,v⟩] 1 ⟨i32,v⟩ i32 rfl rfl hv
  have q4 := exec_ret 1 (ws P R ([⟨i32,v⟩] ++ [⟨i32,v⟩])) (.variable i32 (R.length + 1)) v (by rw [den_variable]; exact e3)
  have q34 := seq_some q3 rfl q4
  have q234 := seq_some qc rfl q34
  have q1234 := seq_some q1 rfl q234
  refine ⟨_, q1234, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · have := ws_size P R ([⟨i32,v⟩] ++ [⟨i32,v⟩])
    simp [NExpr.nodes, ws] at *; omega
  · simp [ws]

theorem refs1_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 true false])
    (hr : prog.result = ResultKind.scalar i32) (hbody : Scalar prog.body = true)
    (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : i32.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+100 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ i32 false hp sa ba x ca (by simp) valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret i32 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem refs2b_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 true false,.scalar i32 true false])
    (hr : prog.result = ResultKind.scalar i32) (hbody : Scalar prog.body = true)
    (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : i32.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+100 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ i32 false false hp sa sb ba bb _ _ ca cb (by simp) (by simp) valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret i32 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

-- `return x;` for a read-only reference parameter (the accessor `x()`).
theorem retvar_exec (P : List Cell) (a : Nat) (x : Int) (hxv : i32.valid x = true) (ha : P[a]? = some ⟨i32,x⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable i32 0))) Sk) ⟨P,[⟨a,false⟩]⟩ = some r ∧
      r.ret = some x ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a,false⟩]⟩ 0 i32 = some x := penv_ok _ 0 i32 ⟨a,false⟩ ⟨i32,x⟩ rfl ha rfl hxv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩]⟩ (.variable i32 0) x (by rw [den_variable]; exact e0)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem groupsum_x_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : i32.valid x = true) (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_int_x.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_int_x.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar_exec (callerP caller) ba.address x hxv (P_cellI caller sa ba x ca)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem groupmul_x_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : i32.valid x = true) (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_int_x.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_int_x.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar_exec (callerP caller) ba.address x hxv (P_cellI caller sa ba x ca)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem env2 (P : List Cell) (a b : Nat) (x y : Int) (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 0 i32 = some x ∧ penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 1 i32 = some y :=
  ⟨ws_env_ref P _ [] 0 a false i32 x rfl ha hxv, ws_env_ref P _ [] 1 b false i32 y rfl hb hyv⟩

abbrev addE : NExpr := .binary i32 .add (.variable i32 0) (.variable i32 1)
abbrev mulE : NExpr := .binary i32 .mul (.variable i32 0) (.variable i32 1)
abbrev negE : NExpr := .unary i32 .neg (.variable i32 0)
abbrev invE : NExpr := .divrem i32 false (.literal i32 1) (.variable i32 0)

theorem addE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 i32 = some x) (h1 : env 1 i32 = some y)
    (hxy : i32.valid (x+y) = true) : addE.denote env = some (x+y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convI _ hxy

theorem mulE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 i32 = some x) (h1 : env 1 i32 = some y)
    (hxy : i32.valid (x*y) = true) : mulE.denote env = some (x*y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convI _ hxy

theorem negE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 i32 = some x)
    (hx : i32.valid (-x) = true) : negE.denote env = some (-x) := by
  simp only [negE, NExpr.denote, h0, Option.bind_some]
  exact convI _ hx

theorem invE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 i32 = some x) (hx : x = 1 ∨ x = -1) :
    invE.denote env = some x := by
  have one : (NExpr.literal i32 1).denote env = some 1 := by
    have h1 : i32.valid 1 = true := rfl
    rw [den_literal, if_pos h1]
  simp only [invE, NExpr.denote, one, h0, Option.bind_some]
  rcases hx with rfl | rfl
  · decide
  · decide

theorem groupsum_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (hxy : i32.valid (x+y) = true)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.op_GroupSum_int.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.op_GroupSum_int.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x+y)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x+y) hxy 20 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2 (callerP caller) ba.address bb.address x y hxv hyv (P_cellI caller sa ba x ca) (P_cellI caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeA_exec (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] addE (x+y) hxy
    (addE_den _ x y e0 e1 hxy) (by decide)
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupsum_inv_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : i32.valid x = true) (hnx : i32.valid (-x) = true) (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_int_inv.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_int_inv.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar (-x)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 (-x) hnx 20 ?_
  intro P hP
  subst hP
  have e0 : penv (ws (callerP caller) [⟨ba.address,false⟩] []) 0 i32 = some x :=
    ws_env_ref _ _ [] 0 ba.address false i32 x rfl (P_cellI caller sa ba x ca) hxv
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeA_exec (callerP caller) [⟨ba.address,false⟩] negE (-x) hnx
    (negE_den _ x e0 hnx) (by decide)
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupmul_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (hxy : i32.valid (x*y) = true) (hne : x*y ≠ 0)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.op_GroupMul_int.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.op_GroupMul_int.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x*y)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x*y) hxy 30 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2 (callerP caller) ba.address bb.address x y hxv hyv (P_cellI caller sa ba x ca) (P_cellI caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] mulE (x*y) hxy
    (mulE_den _ x y e0 e1 hxy) (by decide) hne
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

theorem groupmul_inv_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hx : x = 1 ∨ x = -1) (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_int_inv.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_int_inv.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  have hxv : i32.valid x = true := by rcases hx with rfl | rfl <;> rfl
  have hne : x ≠ 0 := by rcases hx with rfl | rfl <;> decide
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 x hxv 30 ?_
  intro P hP
  subst hP
  have e0 : penv (ws (callerP caller) [⟨ba.address,false⟩] []) 0 i32 = some x :=
    ws_env_ref _ _ [] 0 ba.address false i32 x rfl (P_cellI caller sa ba x ca) hxv
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [⟨ba.address,false⟩] invE x hxv
    (invE_den _ x e0 hx) (by decide) hne
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

-- The constructor with an assert: `assert(x != 0); return x;`.
theorem groupmul_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v)
    (hv : i32.valid v = true) (hne : v ≠ 0) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_int_new0.parameters [.value e] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_int_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 80 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ i32 rfl e v hs hty value valid hv
  have takeM2 : (callerP caller ++ [(⟨i32,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have e0 : penv ⟨callerP caller ++ [⟨i32,v⟩],[⟨(callerP caller).length,true⟩]⟩ 0 i32 = some v :=
    penv_ok _ 0 i32 ⟨(callerP caller).length,true⟩ ⟨i32,v⟩ rfl (by simpa using get_tail (callerP caller) [⟨i32,v⟩] 0) rfl hv
  have hd := nz_value (penv ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩) 0 v e0 hne
  have c1 : pstmt (.check (nz 0)) ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩ =
      some ⟨⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩,none,(nz 0).nodes+1,
        (callerP caller ++ [(⟨i32,v⟩ : Cell)]).length+1+(nz 0).nodes+2⟩ := by
    simp only [pstmt, hd]
    simp
  have qc := (pexec_prim 1 _ _).trans c1
  have q := exec_ret 1 ⟨callerP caller ++ [(⟨i32,v⟩ : Cell)],[⟨(callerP caller).length,true⟩]⟩ (.variable i32 0) v
    (by rw [den_variable]; exact e0)
  have qq := seq_some qc rfl q
  have gw := good.2.2.1
  have hpost := call_scalar caller Proofs.GroupInstance.GroupMul_int_new0 [.value e] Sinit
    (callerP caller ++ [(⟨i32,v⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)] hprep (by rw [sSlots]; rfl)
    sMem sBind sBase sScope sFrame (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base
    (by decide) 1 _ qq _ rfl i32 rfl hv (by simp [NExpr.nodes]) (by simp)
    e.nodes 80 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM2] at post
  exact post

theorem groupsum_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v)
    (hv : i32.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_int_new0.parameters [.value e] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_int_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correctI _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

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

theorem groupsum_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_int_new1.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_int_new1.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  default_correct _ false (.literal i32 0) 0 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base


theorem groupmul_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_int_new1.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_int_new1.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  default_correct _ true (.literal i32 1) 1 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base


theorem prep_rrrr (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar i32 true false,.scalar i32 true false,.scalar i32 true false,.scalar i32 true false])
    (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 i32 = some (b3,⟨i32,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+9 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  obtain ⟨i4,_,_,m4,_,w4⟩ := scalarCell_facts c4
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have l4 : b4.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m4).1
  have c2' : (caller.charge 1 1).scalarCell s2 i32 = some (b2,⟨i32,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 i32 = some (b3,⟨i32,v3⟩) := c3
  have c4' : (((caller.charge 1 1).charge 1 1).charge 1 1).scalarCell s4 i32 = some (b4,⟨i32,v4⟩) := c4
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨i32,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨i32,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have h3 := pad b3 v3 l3 m3
  have h4 := pad b4 v4 l4 m4
  rw [hp]
  have wt : (true = true → True) := fun _ => trivial
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3',c4']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,h4,w1,w2,w3,w4]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

theorem prep_rrr (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar i32 true false,.scalar i32 true false,.scalar i32 true false])
    (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 i32 = some (b3,⟨i32,v3⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3] =
        some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have c2' : (caller.charge 1 1).scalarCell s2 i32 = some (b2,⟨i32,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 i32 = some (b3,⟨i32,v3⟩) := c3
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨i32,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨i32,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have h3 := pad b3 v3 l3 m3
  rw [hp]
  have wt : (true = true → True) := fun _ => trivial
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,w1,w2,w3]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _


-- Generic preparation for two read-only references followed by a value argument.
theorem prep_rrv (caller : NState) (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar i32 true false,.scalar i32 true false,.scalar i32 false true])
    (s1 s2 : Nat) (b1 b2 : CppState.Binding) (v1 v2 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (e : NExpr) (n : Int) (hs : e.scalarOnly = true) (hty : e.resultType = i32)
    (value : e.denote (envOf caller) = some n) (valid : caller.frame.state.wellFormed = true)
    (nv : i32.valid n = true) :
    ∃ t, Good ((caller.charge 1 1).charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.value e] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,n⟩] ∧
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
  have c2' : (caller.charge 1 1).scalarCell s2 i32 = some (b2,⟨i32,v2⟩) := c2
  have pad : ∀ (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨i32,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨i32,v⟩ := by
    intro b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad b1 v1 l1 m1
  have h2 := pad b2 v2 l2 m2
  have res3 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e) = some (t,.scalar i32 true n) := by
    simp [resolve,hty,ran]
  have res1 : resolve caller (.scalar i32 true false) (.scalarReference s1) =
      some (caller.charge 1 1,.scalarAddress i32 b1.address false) := by simp [resolve,c1]
  have res2 : resolve (caller.charge 1 1) (.scalar i32 true false) (.scalarReference s2) =
      some ((caller.charge 1 1).charge 1 1,.scalarAddress i32 b2.address false) := by simp [resolve,c2']
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2,res3]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,NState.observe,
    CppState.State.observe,h1,h2,w1,w2]
  have g := good.2.2.2.2.1
  simp only [charge_scalar_peak] at g ⊢
  exact Nat.le_trans (by omega) (Nat.le_max_left _ _)

abbrev applyE : NExpr := .binary i32 .add (.binary i32 .mul (.variable i32 0) (.variable i32 2)) (.variable i32 1)

theorem apply_body : Proofs.GroupInstance.GroupAffine_int_apply.body = .sequence (.primitive (.ret applyE)) Sk := rfl

theorem applyE_den (env : Nat → Ty → Option Int) (a b x : Int) (h0 : env 0 i32 = some a) (h1 : env 1 i32 = some b)
    (h2 : env 2 i32 = some x) (hm : i32.valid (a*x) = true) (hs : i32.valid (a*x + b) = true) :
    applyE.denote env = some (a*x + b) := by
  rw [den_binary, den_binary, den_variable, den_variable, den_variable, h0, h2, h1]
  simp only [Option.bind_some]
  have e1 : binaryValue .mul a x = a * x := rfl
  rw [e1, convI _ hm]
  simp only [Option.bind_some]
  have e2 : binaryValue .add (a * x) b = a * x + b := rfl
  rw [e2]
  exact convI _ hs

set_option maxHeartbeats 4000000 in
theorem affine_apply_correct (caller : NState) (sa sb sx : Nat) (ba bb bx : CppState.Binding) (a b x : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,a⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,b⟩))
    (cx : caller.scalarCell sx i32 = some (bx,⟨i32,x⟩))
    (hav : i32.valid a = true) (hbv : i32.valid b = true) (hxv : i32.valid x = true)
    (hm : i32.valid (a*x) = true) (hsum : i32.valid (a*x + b) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_apply.parameters
        [.scalarReference sa,.scalarReference sb,.scalarReference sx] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_apply.callFuel fuel caller [.scalarReference sa,.scalarReference sb,.scalarReference sx] =
        .finished (res,.scalar (a*x + b)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrr caller _ rfl sa sb sx ba bb bx a b x ca cb cx valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hPa := P_cellI caller sa ba a ca
  have hPb := P_cellI caller sb bb b cb
  have hPx := P_cellI caller sx bx x cx
  let refs : List CppState.Binding := [⟨ba.address,false⟩,⟨bb.address,false⟩,⟨bx.address,false⟩]
  have e0 : penv ⟨callerP caller,refs⟩ 0 i32 = some a :=
    penv_ok _ 0 i32 ⟨ba.address,false⟩ ⟨i32,a⟩ rfl hPa rfl hav
  have e1 : penv ⟨callerP caller,refs⟩ 1 i32 = some b :=
    penv_ok _ 1 i32 ⟨bb.address,false⟩ ⟨i32,b⟩ rfl hPb rfl hbv
  have e2 : penv ⟨callerP caller,refs⟩ 2 i32 = some x :=
    penv_ok _ 2 i32 ⟨bx.address,false⟩ ⟨i32,x⟩ rfl hPx rfl hxv
  have q := exec_ret 1 ⟨callerP caller,refs⟩ applyE (a*x + b) (applyE_den _ a b x e0 e1 e2 hm hsum)
  have hexec : pexec 1 Proofs.GroupInstance.GroupAffine_int_apply.body ⟨callerP caller,refs⟩ =
      some ⟨⟨callerP caller,refs⟩,some (a*x + b),applyE.nodes+1,(callerP caller).length+3+applyE.nodes+2⟩ := by
    rw [apply_body]; simpa [refs] using q
  have hpost := call_scalar caller Proofs.GroupInstance.GroupAffine_int_apply
    [.scalarReference sa,.scalarReference sb,.scalarReference sx] Sinit (callerP caller) refs
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak (by omega) (by rw [takeM]) valid lengths
    strict base (by rw [apply_body]; simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl i32 rfl hsum
    (by simp [NExpr.nodes]) (by simp [refs]) 0 80 (by simp only [NExpr.nodes] at *; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post

theorem refs4_correct (prog : NProgram)
    (hp : prog.parameters = [.scalar i32 true false,.scalar i32 true false,.scalar i32 true false,.scalar i32 true false])
    (hr : prog.result = ResultKind.scalar i32) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 i32 = some (b3,⟨i32,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : i32.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrrr caller _ hp s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩,⟨b4.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret i32 hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

abbrev compAE : NExpr := .binary i32 .mul (.variable i32 0) (.variable i32 2)
abbrev compBE : NExpr := .binary i32 .add (.binary i32 .mul (.variable i32 1) (.variable i32 2)) (.variable i32 3)

theorem compA_body : Proofs.GroupInstance.GroupAffine_int_op__a.body = .sequence (.primitive (.ret compAE)) Sk := rfl
theorem compB_body : Proofs.GroupInstance.GroupAffine_int_op__b.body = .sequence (.primitive (.ret compBE)) Sk := rfl

theorem compA_exec (P : List Cell) (a1 a2 a3 a4 : Nat) (v1 v2 v3 v4 : Int)
    (h1 : P[a1]? = some ⟨i32,v1⟩) (h3 : P[a3]? = some ⟨i32,v3⟩)
    (g1 : i32.valid v1 = true) (g3 : i32.valid v3 = true) (gm : i32.valid (v1*v3) = true) :
    ∃ r, pexec 1 Proofs.GroupInstance.GroupAffine_int_op__a.body ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some (v1*v3) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 0 i32 = some v1 :=
    penv_ok _ 0 i32 ⟨a1,false⟩ ⟨i32,v1⟩ rfl h1 rfl g1
  have e2 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 2 i32 = some v3 :=
    penv_ok _ 2 i32 ⟨a3,false⟩ ⟨i32,v3⟩ rfl h3 rfl g3
  have den : compAE.denote (penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩) = some (v1*v3) := by
    rw [den_binary, den_variable, den_variable, e0, e2]
    simp only [Option.bind_some]
    have e1 : binaryValue .mul v1 v3 = v1 * v3 := rfl
    rw [e1]; exact convI _ gm
  have q := exec_ret 1 ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ compAE (v1*v3) den
  refine ⟨_, by rw [compA_body]; exact q, rfl, ?_, ?_, rfl⟩ <;> simp [NExpr.nodes] <;> omega

theorem compB_exec (P : List Cell) (a1 a2 a3 a4 : Nat) (v1 v2 v3 v4 : Int)
    (h2 : P[a2]? = some ⟨i32,v2⟩) (h3 : P[a3]? = some ⟨i32,v3⟩) (h4 : P[a4]? = some ⟨i32,v4⟩)
    (g2 : i32.valid v2 = true) (g3 : i32.valid v3 = true) (g4 : i32.valid v4 = true)
    (gm : i32.valid (v2*v3) = true) (gs : i32.valid (v2*v3 + v4) = true) :
    ∃ r, pexec 1 Proofs.GroupInstance.GroupAffine_int_op__b.body ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ = some r ∧
      r.ret = some (v2*v3 + v4) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e1 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 1 i32 = some v2 :=
    penv_ok _ 1 i32 ⟨a2,false⟩ ⟨i32,v2⟩ rfl h2 rfl g2
  have e2 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 2 i32 = some v3 :=
    penv_ok _ 2 i32 ⟨a3,false⟩ ⟨i32,v3⟩ rfl h3 rfl g3
  have e3 : penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ 3 i32 = some v4 :=
    penv_ok _ 3 i32 ⟨a4,false⟩ ⟨i32,v4⟩ rfl h4 rfl g4
  have den : compBE.denote (penv ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩) = some (v2*v3 + v4) := by
    rw [den_binary, den_binary, den_variable, den_variable, den_variable, e1, e2, e3]
    simp only [Option.bind_some]
    have m1 : binaryValue .mul v2 v3 = v2 * v3 := rfl
    rw [m1, convI _ gm]
    simp only [Option.bind_some]
    have m2 : binaryValue .add (v2 * v3) v4 = v2 * v3 + v4 := rfl
    rw [m2]; exact convI _ gs
  have q := exec_ret 1 ⟨P,[⟨a1,false⟩,⟨a2,false⟩,⟨a3,false⟩,⟨a4,false⟩]⟩ compBE (v2*v3 + v4) den
  refine ⟨_, by rw [compB_body]; exact q, rfl, ?_, ?_, rfl⟩ <;> simp [NExpr.nodes] <;> omega

theorem affine_compose_a_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 i32 = some (b3,⟨i32,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : i32.valid v1 = true) (g3 : i32.valid v3 = true) (gm : i32.valid (v1*v3) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_op__a.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_op__a.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v1*v3)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  refine refs4_correct _ rfl rfl (by rw [compA_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v1*v3) gm 10 ?_
  intro P hP
  subst hP
  obtain ⟨r,h,hr,hc,hn,hm⟩ := compA_exec (callerP caller) b1.address b2.address b3.address b4.address v1 v2 v3 v4
    (P_cellI caller s1 b1 v1 c1) (P_cellI caller s3 b3 v3 c3) g1 g3 gm
  exact ⟨r,h,hr,hc,hn,by rw [hm]; simpa using take_P caller []⟩

theorem affine_compose_b_correct (caller : NState) (s1 s2 s3 s4 : Nat) (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 i32 = some (b1,⟨i32,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 i32 = some (b3,⟨i32,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g2 : i32.valid v2 = true) (g3 : i32.valid v3 = true) (g4 : i32.valid v4 = true)
    (gm : i32.valid (v2*v3) = true) (gs : i32.valid (v2*v3 + v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_op__b.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_op__b.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = .finished (res,.scalar (v2*v3 + v4)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  refine refs4_correct _ rfl rfl (by rw [compB_body]; simp [Scalar, NExpr.scalarOnly]) caller s1 s2 s3 s4 b1 b2 b3 b4
    v1 v2 v3 v4 c1 c2 c3 c4 valid lengths strict base 1 (v2*v3 + v4) gs 10 ?_
  intro P hP
  subst hP
  obtain ⟨r,h,hr,hc,hn,hm⟩ := compB_exec (callerP caller) b1.address b2.address b3.address b4.address v1 v2 v3 v4
    (P_cellI caller s2 b2 v2 c2) (P_cellI caller s3 b3 v3 c3) (P_cellI caller s4 b4 v4 c4) g2 g3 g4 gm gs
  exact ⟨r,h,hr,hc,hn,by rw [hm]; simpa using take_P caller []⟩


/-! ### `GroupAffine`: the accessors, the identity and the inverse -/

theorem retvar2a_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable i32 0))) Sk) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some x ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 i32 = some x := penv_ok _ 0 i32 ⟨a,false⟩ ⟨i32,x⟩ rfl ha rfl hxv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ (.variable i32 0) x (by rw [den_variable]; exact e0)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem retvar2b_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    ∃ r, pexec 1 (.sequence (.primitive (.ret (.variable i32 1))) Sk) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some y ∧ r.cost ≤ 5 ∧ r.need ≤ P.length+100 ∧ r.ps.mem = P := by
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 i32 = some y := penv_ok _ 1 i32 ⟨b,false⟩ ⟨i32,y⟩ rfl hb rfl hyv
  have q := exec_ret 1 ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ (.variable i32 1) y (by rw [den_variable]; exact e1)
  refine ⟨_, q, rfl, ?_, ?_, rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem affine_a_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_a.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_a.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 x hxv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar2a_exec (callerP caller) ba.address bb.address x y hxv hyv
    (P_cellI caller sa ba x ca) (P_cellI caller sb bb y cb)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem affine_b_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_b.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_b.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar y) ∧
      ScalarPost2 caller Sinit res 0 65 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 y hyv 5 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := retvar2b_exec (callerP caller) ba.address bb.address x y hxv hyv
    (P_cellI caller sa ba x ca) (P_cellI caller sb bb y cb)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; simpa using take_P caller []⟩

theorem affine_e_a_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_e__a.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_e__a.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correctI _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem affine_e_b_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_e__b.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_e__b.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correctI _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem groupsum_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupSum_int_e.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupSum_int_e.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_correctI _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

-- The static `e()` of a class whose constructor asserts: `declare r = e; assert(r != 0); declare s = r; return s`.
theorem e_check_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = shapeB 0 e) (hr : prog.result = ResultKind.scalar i32)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
    (hne : v ≠ 0) (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeB_exec (callerP caller) [] e v hv (by rw [ws_nil]; exact he _) hn hne
  rw [ws_nil] at h1
  simp only [List.length_nil] at h1
  rw [← hb] at h1
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base
    (by rw [hb]; simp [Scalar, hs, NExpr.scalarOnly, nz]) 1 _ h1 _ h2 i32 hr hv
    (by simp at h4 ⊢; omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have e3 : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [h5]
    have : callerP caller ++ [(⟨i32,v⟩ : Cell),⟨i32,v⟩] = callerP caller ++ [(⟨i32,v⟩ : Cell),⟨i32,v⟩] := rfl
    exact take_P caller _
  rw [e3] at post
  exact post

theorem groupmul_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupMul_int_e.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupMul_int_e.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_check_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, i32]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) (by decide) caller valid lengths strict base

/-! `GroupAffine::inv`: the integer divisions `1 / a` and `-b / a` (truncating, as in C++) -/

abbrev invAE : NExpr := .divrem i32 false (.literal i32 1) (.variable i32 0)
abbrev invBE : NExpr := .divrem i32 false (.unary i32 .neg (.variable i32 1)) (.variable i32 0)

theorem invAE_den (env : Nat → Ty → Option Int) (x : Int) (h0 : env 0 i32 = some x) (hne : x ≠ 0)
    (hq : i32.valid ((1 : Int).tdiv x) = true) : invAE.denote env = some ((1 : Int).tdiv x) := by
  have one : (NExpr.literal i32 1).denote env = some 1 := by
    have h1 : i32.valid 1 = true := rfl
    rw [den_literal, if_pos h1]
  rw [den_divrem, one, den_variable, h0]
  simp only [Option.bind_some, checkedDivRem]
  have hb : (x == 0) = false := by simp [hne]
  rw [hb]
  simp only [Bool.false_eq_true, if_false]
  rw [if_neg (by simp [hq])]
  exact convI _ hq

theorem invBE_den (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 i32 = some x) (h1 : env 1 i32 = some y)
    (hne : x ≠ 0) (hn : i32.valid (-y) = true) (hq : i32.valid ((-y).tdiv x) = true) :
    invBE.denote env = some ((-y).tdiv x) := by
  have neg : (NExpr.unary i32 .neg (.variable i32 1)).denote env = some (-y) := by
    simp only [NExpr.denote, h1, Option.bind_some, unaryValue]
    exact convI _ hn
  rw [den_divrem, neg, den_variable, h0]
  simp only [Option.bind_some, checkedDivRem]
  have hb : (x == 0) = false := by simp [hne]
  rw [hb]
  simp only [Bool.false_eq_true, if_false]
  rw [if_neg (by rw [hq]; decide)]
  exact convI _ hq

theorem affine_inv_a_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (hne : x ≠ 0) (hq : i32.valid ((1 : Int).tdiv x) = true)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_inv__a.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_inv__a.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((1 : Int).tdiv x)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 _ hq 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 0 i32 = some x :=
    penv_ok _ 0 i32 ⟨ba.address,false⟩ ⟨i32,x⟩ rfl (P_cellI caller sa ba x ca) rfl hxv
  have q := exec_ret 1 ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ invAE ((1 : Int).tdiv x)
    (invAE_den _ x e0 hne hq)
  have hb : Proofs.GroupInstance.GroupAffine_int_inv__a.body = .sequence (.primitive (.ret invAE)) Sk := rfl
  rw [hb]
  refine ⟨_, q, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simpa using take_P caller []

theorem affine_inv_b_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (hne : x ≠ 0) (hn : i32.valid (-y) = true)
    (hq : i32.valid ((-y).tdiv x) = true)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_inv__b.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_inv__b.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((-y).tdiv x)) ∧
      ScalarPost2 caller Sinit res 0 90 caller.scalars.memory := by
  refine refs2b_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 _ hq 30 ?_
  intro P hP
  subst hP
  have e0 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 0 i32 = some x :=
    penv_ok _ 0 i32 ⟨ba.address,false⟩ ⟨i32,x⟩ rfl (P_cellI caller sa ba x ca) rfl hxv
  have e1 : penv ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ 1 i32 = some y :=
    penv_ok _ 1 i32 ⟨bb.address,false⟩ ⟨i32,y⟩ rfl (P_cellI caller sb bb y cb) rfl hyv
  have q := exec_ret 1 ⟨callerP caller,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ invBE ((-y).tdiv x)
    (invBE_den _ x y e0 e1 hne hn hq)
  have hb : Proofs.GroupInstance.GroupAffine_int_inv__b.body = .sequence (.primitive (.ret invBE)) Sk := rfl
  rw [hb]
  refine ⟨_, q, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simpa using take_P caller []

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

theorem value2_correct (prog : NProgram) (second : Bool)
    (hp : prog.parameters = [.scalar i32 false true,.scalar i32 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable i32 (if second then 1 else 0)))) Sk)
    (hr : prog.result = ResultKind.scalar i32) (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : i32.valid x = true) (hy : i32.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (if second then y else x)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_values2 i32 caller _ hp e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 valid hx hy
  let P := callerP caller
  let M := P ++ [(⟨i32,x⟩ : Cell),⟨i32,y⟩]
  let bs : List CppState.Binding := [⟨P.length,true⟩,⟨P.length+1,true⟩]
  have ev : penv ⟨M,bs⟩ (if second then 1 else 0) i32 = some (if second then y else x) := by
    cases second
    · exact penv_ok _ 0 i32 ⟨P.length,true⟩ ⟨i32,x⟩ rfl
        (by simp [M,P]) rfl hx
    · exact penv_ok _ 1 i32 ⟨P.length+1,true⟩ ⟨i32,y⟩ rfl
        (by simp [M,P]) rfl hy
  have takeM : M.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  have q := exec_ret 1 (⟨M,bs⟩ : PS) (.variable i32 (if second then 1 else 0)) (if second then y else x)
    (by rw [den_variable]; exact ev)
  rw [← hb] at q
  have hexec := q
  have peak1 := g1.2.2.2.2.1
  have peak2 := g2.2.2.2.2.1
  have work1 := g1.2.2.1
  have work2 := g2.2.2.1
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [P,callerP]
  have hpost := call_scalar caller prog [.value e1,.value e2] Sinit M bs
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame (by omega)
    (by simp [M]; omega) (by rw [takeM]) valid lengths strict base
    (by rw [hb]; simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl i32 hr
    (by cases second <;> assumption) (by simp [M,bs,P,NExpr.nodes]) (by simp [M,bs,P])
    (e1.nodes+e2.nodes) 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  exact ⟨Sinit,fuel,res,hprep,hrun,by simpa only [takeM] using post⟩

theorem affine_new_a_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : i32.valid x = true) (hy : i32.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_new0__a.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_new0__a.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar x) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2_correct _ false rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem affine_new_b_correct (caller : NState) (e1 e2 : NExpr) (x y : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some y)
    (hx : i32.valid x = true) (hy : i32.valid y = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_new0__b.parameters [.value e1,.value e2] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_new0__b.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar y) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory :=
  value2_correct _ true rfl rfl rfl caller e1 e2 x y hs1 hs2 ht1 ht2 d1 d2 hx hy valid lengths strict base

theorem affine_default_a_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_new1__a.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_new1__a.callFuel fuel caller [] = .finished (res,.scalar 1) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correctI _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem affine_default_b_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.GroupInstance.GroupAffine_int_new1__b.parameters [] = some Sinit ∧
      Proofs.GroupInstance.GroupAffine_int_new1__b.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correctI _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

-- The original hidden friends have the same complete scalar programs as their namespace counterparts.
theorem groupsum_friend_program : Proofs.GroupInstance.GroupSum_int_op = Proofs.GroupInstance.op_GroupSum_int := rfl
theorem groupmul_friend_program : Proofs.GroupInstance.GroupMul_int_op = Proofs.GroupInstance.op_GroupMul_int := rfl
theorem affine_friend_a_program : Proofs.GroupInstance.GroupAffine_int_op_friend__a = Proofs.GroupInstance.GroupAffine_int_op__a := rfl
theorem affine_friend_b_program : Proofs.GroupInstance.GroupAffine_int_op_friend__b = Proofs.GroupInstance.GroupAffine_int_op__b := rfl

end Proofs.GroupCallInt
