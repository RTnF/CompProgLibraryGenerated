import Proofs.ModIntCall
import Proofs.Generated.Monoid

namespace Proofs.MonoidCallCoreInt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

theorem i32_valid_int (v : Int) (h0 : -2147483648 ≤ v) (h1 : v < 2147483648) : i32.valid v = true := by
  simp [i32, Ty.valid]; omega

-- A constructor-like function without parameters whose body is `return e` for a closed expression.
theorem const_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
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

-- The constructor from a value: `return x_`.
theorem ctor_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 false true])
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

-- Two read-only reference parameters, the body given by an execution hypothesis on the reserved memory.
theorem refs2_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 true false,.scalar i32 true false])
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
        r.cost ≤ C ∧ r.need ≤ P.length+16 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
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

theorem convI (v : Int) (h : i32.valid v = true) : i32.convert v = some v := by
  unfold Ty.convert; simp [i32, h]

theorem mul_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : i32.valid x = true) (hyv : i32.valid y = true)
    (hxy : i32.valid (x*y) = true) (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    ∃ r, pexec 1 Proofs.MonoidInstance.op_MonoidMul_int.body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (x*y) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨i32,x*y⟩,⟨i32,x*y⟩] := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 i32 = some x :=
    penv_ok _ 0 i32 ⟨a,false⟩ ⟨i32,x⟩ rfl ha rfl hxv
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 i32 = some y :=
    penv_ok _ 1 i32 ⟨b,false⟩ ⟨i32,y⟩ rfl hb rfl hyv
  have hbv : binaryValue .mul x y = x*y := rfl
  have d1 : (NExpr.binary i32 .mul (.variable i32 0) (.variable i32 1)).denote (penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩) = some (x*y) := by
    rw [den_binary, den_variable, den_variable, e0, e1]
    simp only [Option.bind_some, hbv]
    exact convI _ hxy
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ i32 true _ (x*y) d1 (x*y) (convI _ hxy)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv ⟨P ++ [(⟨i32,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 i32 = some (x*y) :=
    penv_ok _ 2 i32 ⟨P.length,true⟩ ⟨i32,x*y⟩ (by simp) (by simp) rfl hxy
  have d2 : (NExpr.variable i32 2).denote (penv ⟨P ++ [(⟨i32,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (x*y) := by
    rw [den_variable]; exact e2
  have s2 := pstmt_declare_ok ⟨P ++ [(⟨i32,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ i32 true _ (x*y) d2 (x*y) (convI _ hxy)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e3 : penv ⟨P ++ [(⟨i32,x*y⟩ : Cell)] ++ [⟨i32,x*y⟩],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩] ++ [⟨(P ++ [(⟨i32,x*y⟩ : Cell)]).length,true⟩]⟩ 3 i32 = some (x*y) :=
    penv_ok _ 3 i32 ⟨P.length+1,true⟩ ⟨i32,x*y⟩ (by simp) (by simp) rfl hxy
  have q3 := exec_ret 1 ⟨P ++ [(⟨i32,x*y⟩ : Cell)] ++ [⟨i32,x*y⟩],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩] ++ [⟨(P ++ [(⟨i32,x*y⟩ : Cell)]).length,true⟩]⟩
    (.variable i32 3) (x*y) (by rw [den_variable]; exact e3)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  refine ⟨_, q123, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simp

abbrev bT : Ty := ⟨1, false, true⟩

abbrev selBody (i j : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 0)))
    (.sequence (.branch (.binary bT .lt (.variable i32 i) (.variable i32 j))
        (.sequence (.scope (.sequence (.primitive (.assign 2 i32 (.variable i32 1))) Sk)) Sk) Sk)
      (.sequence (.primitive (.ret (.variable i32 2))) Sk))


theorem sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    ∃ r, pexec 1 (selBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨i32,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] := by
  have hla : a < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have hlb : b < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 i32 = some x :=
    penv_ok _ 0 i32 ⟨a,false⟩ ⟨i32,x⟩ rfl ha rfl hxv
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ i32 true (.variable i32 0) x (by rw [den_variable]; exact e0) x (convI _ hxv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have hmemS1 : ∀ k, k < P.length → (P ++ [(⟨i32,x⟩ : Cell)])[k]? = P[k]? := fun k hk => List.getElem?_append_left hk
  have e0' : penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 0 i32 = some x :=
    penv_ok _ 0 i32 ⟨a,false⟩ ⟨i32,x⟩ rfl (by simpa using (hmemS1 a hla).trans ha) rfl hxv
  have e1' : penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 1 i32 = some y :=
    penv_ok _ 1 i32 ⟨b,false⟩ ⟨i32,y⟩ rfl (by simpa using (hmemS1 b hlb).trans hb) rfl hyv
  have e2' : penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 i32 = some x :=
    penv_ok _ 2 i32 ⟨P.length,true⟩ ⟨i32,x⟩ (by simp) (by simp) rfl hxv
  obtain ⟨u, hu⟩ : ∃ u, penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ i i32 = some u ∧
      u = if i = 0 then x else y := by
    rcases hij with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨x, e0', by simp⟩
    · exact ⟨y, e1', by simp⟩
  obtain ⟨w, hw⟩ : ∃ w, penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ j i32 = some w ∧
      w = if j = 0 then x else y := by
    rcases hij with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨y, e1', by simp⟩
    · exact ⟨x, e0', by simp⟩
  have hcond : (NExpr.binary bT .lt (.variable i32 i) (.variable i32 j)).denote
      (penv ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (if u < w then 1 else 0) := by
    rw [den_binary, den_variable, den_variable, hu.1, hw.1]
    simp only [Option.bind_some]
    have : binaryValue .lt u w = if u < w then 1 else 0 := rfl
    rw [this]
    unfold Ty.convert
    by_cases h : u < w <;> simp [bT, h]
  have huw : (u < w) ↔ ((if i = 0 then x else y) < (if j = 0 then x else y)) := by rw [hu.2, hw.2]
  have hskip := pexec_skip 1 ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩
  by_cases hlt : u < w
  · rw [if_pos hlt] at hcond
    have st := pstmt_assign_ok ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 i32 (.variable i32 1) y
      (by rw [den_variable]; exact e1') ⟨P.length,true⟩ ⟨i32,x⟩ (by simp) (by simp) rfl hxv rfl y (convI _ hyv)
    have hset : (P ++ [(⟨i32,x⟩ : Cell)]).set P.length ⟨i32,y⟩ = P ++ [(⟨i32,y⟩ : Cell)] := by
      simp [List.set_append_right]
    rw [hset] at st
    have yes := pexec_braced 1 (.assign 2 i32 (.variable i32 1)) _ _ st rfl (by simp) (by simp)
    have br := pexec_branch_true 1 (.binary bT .lt (.variable i32 i) (.variable i32 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 i32 (.variable i32 1))) Sk)) Sk) Sk _ 1 hcond (by decide) _ yes
    have e3 : penv ⟨P ++ [(⟨i32,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 i32 = some y :=
      penv_ok _ 2 i32 ⟨P.length,true⟩ ⟨i32,y⟩ (by simp) (by simp) rfl hyv
    have q3 := exec_ret 1 ⟨P ++ [(⟨i32,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ (.variable i32 2) y
      (by rw [den_variable]; exact e3)
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (huw.mp hlt)]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rw [if_pos (huw.mp hlt)]
  · rw [if_neg hlt] at hcond
    have br := pexec_branch_false 1 (.binary bT .lt (.variable i32 i) (.variable i32 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 i32 (.variable i32 1))) Sk)) Sk) Sk _ hcond _ hskip
    have q3 := exec_ret 1 ⟨P ++ [(⟨i32,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ (.variable i32 2) x
      (by rw [den_variable]; exact e2')
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (fun h => hlt (huw.mpr h))]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rw [if_neg (fun h => hlt (huw.mpr h))]

theorem P_cell (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) : (callerP caller)[ba.address]? = some ⟨i32,x⟩ := by
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory := by
  have : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hl : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
  rw [List.take_append_of_le_length hl]; exact this

-- The static `e()`: `declare r = e; declare s = r; return s` for a closed expression `e`.
theorem e_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
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


end Proofs.MonoidCallCoreInt
