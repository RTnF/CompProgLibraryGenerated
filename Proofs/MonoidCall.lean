import Proofs.MonoidCallCore
import Proofs.GroupCall

namespace Proofs.MonoidCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall

theorem s64_valid_int (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) : s64.valid v = true :=
  Proofs.MonoidCallCore.s64_valid_int v h0 h1

theorem const_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.const_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base

theorem ctor_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable s64 0))) Sk) (hr : prog.result = ResultKind.scalar s64)
    (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.ctor_correct prog hp hb hr caller e v hs hty value hv valid lengths strict base

theorem refs2_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 true false,.scalar s64 true false])
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
        r.cost ≤ C ∧ r.need ≤ P.length+16 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory :=
  Proofs.MonoidCallCore.refs2_correct prog hp hr hbody caller sa sb ba bb x y ca cb valid lengths strict base fu v hv C hex

theorem convS (v : Int) (h : s64.valid v = true) : s64.convert v = some v :=
  Proofs.MonoidCallCore.convS v h

theorem mul_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (hxy : s64.valid (x*y) = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 Proofs.MonoidInstance.op_MonoidMul_long_long.body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (x*y) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,x*y⟩,⟨s64,x*y⟩] :=
  Proofs.MonoidCallCore.mul_exec P a b x y hxv hyv hxy ha hb

abbrev bT := @Proofs.MonoidCallCore.bT
abbrev selBody := @Proofs.MonoidCallCore.selBody
theorem sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (selBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] :=
  Proofs.MonoidCallCore.sel_exec i j hij P a b x y hxv hyv ha hb

theorem P_cell (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) : (callerP caller)[ba.address]? = some ⟨s64,x⟩ :=
  Proofs.MonoidCallCore.P_cell caller sa ba x ca

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory :=
  Proofs.MonoidCallCore.take_P caller L

theorem e_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.declare s64 true e))
      (.sequence (.primitive (.declare s64 true (.variable s64 0))) (.sequence (.primitive (.ret (.variable s64 1))) Sk)))
    (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.e_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base

abbrev copiedTail : Command :=
 .sequence (.primitive (.declare s64 true (.variable s64 2)))
  (.sequence (.primitive (.declare s64 true (.variable s64 3)))
   (.sequence (.primitive (.declare s64 true (.variable s64 4)))
    (.sequence (.primitive (.ret (.variable s64 5))) Sk)))
abbrev copiedSelBody (i j : Nat) : Command :=
 .sequence (.primitive (.declare s64 true (.variable s64 0)))
  (.sequence (.branch (.binary bT .lt (.variable s64 i) (.variable s64 j))
    (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk) copiedTail)

theorem max_body : Proofs.MonoidInstance.op_MonoidMax_long_long.body = copiedSelBody 0 1 := rfl
theorem min_body : Proofs.MonoidInstance.op_MonoidMin_long_long.body = copiedSelBody 1 0 := rfl

theorem copied_tail_exec (P : List Cell) (a b : Nat) (v : Int) (hv : s64.valid v = true) :
 ∃ r, pexec 1 copiedTail (ws P [⟨a,false⟩,⟨b,false⟩] [⟨s64,v⟩]) = some r ∧
   r.ret = some v ∧ r.cost ≤ 12 ∧ r.need ≤ P.length+16 ∧
   r.ps.mem = P ++ [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩] := by
 let R : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩]
 let L1 : List Cell := [⟨s64,v⟩]
 let L2 : List Cell := L1 ++ [⟨s64,v⟩]
 let L3 : List Cell := L2 ++ [⟨s64,v⟩]
 let L4 : List Cell := L3 ++ [⟨s64,v⟩]
 have e1 : penv (ws P R L1) 2 s64 = some v := ws_env_loc P R L1 0 ⟨s64,v⟩ s64 rfl rfl hv
 have s1 := ws_declare P R L1 s64 (.variable s64 2) v (by rw [den_variable]; exact e1) (convS _ hv)
 have q1 := (pexec_prim 1 _ _).trans s1
 have e2 : penv (ws P R L2) 3 s64 = some v := ws_env_loc P R L2 1 ⟨s64,v⟩ s64 rfl rfl hv
 have s2 := ws_declare P R L2 s64 (.variable s64 3) v (by rw [den_variable]; exact e2) (convS _ hv)
 have q2 := (pexec_prim 1 _ _).trans s2
 have e3 : penv (ws P R L3) 4 s64 = some v := ws_env_loc P R L3 2 ⟨s64,v⟩ s64 rfl rfl hv
 have s3 := ws_declare P R L3 s64 (.variable s64 4) v (by rw [den_variable]; exact e3) (convS _ hv)
 have q3 := (pexec_prim 1 _ _).trans s3
 have e4 : penv (ws P R L4) 5 s64 = some v := ws_env_loc P R L4 3 ⟨s64,v⟩ s64 rfl rfl hv
 have qr := exec_ret 1 (ws P R L4) (.variable s64 5) v (by rw [den_variable]; exact e4)
 have q3r := seq_some q3 rfl qr
 have q23r := seq_some q2 rfl q3r
 have qall := seq_some q1 rfl q23r
 refine ⟨_,qall,rfl,?_,?_,?_⟩
 · simp [NExpr.nodes]
 · simp [NExpr.nodes,ws,R,L1,L2,L3,L4]
 · simp [ws,L1,L2,L3,L4]

theorem copied_sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (copiedSelBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] := by
  have hla : a < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have hlb : b < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl ha rfl hxv
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ s64 true (.variable s64 0) x (by rw [den_variable]; exact e0) x (convS _ hxv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have hmemS1 : ∀ k, k < P.length → (P ++ [(⟨s64,x⟩ : Cell)])[k]? = P[k]? := fun k hk => List.getElem?_append_left hk
  have e0' : penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl (by simpa using (hmemS1 a hla).trans ha) rfl hxv
  have e1' : penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 1 s64 = some y :=
    penv_ok _ 1 s64 ⟨b,false⟩ ⟨s64,y⟩ rfl (by simpa using (hmemS1 b hlb).trans hb) rfl hyv
  obtain ⟨u, hu⟩ : ∃ u, penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ i s64 = some u ∧
      u = if i = 0 then x else y := by
    rcases hij with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨x, e0', by simp⟩
    · exact ⟨y, e1', by simp⟩
  obtain ⟨w, hw⟩ : ∃ w, penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ j s64 = some w ∧
      w = if j = 0 then x else y := by
    rcases hij with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨y, e1', by simp⟩
    · exact ⟨x, e0', by simp⟩
  have hcond : (NExpr.binary bT .lt (.variable s64 i) (.variable s64 j)).denote
      (penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (if u < w then 1 else 0) := by
    rw [den_binary, den_variable, den_variable, hu.1, hw.1]
    simp only [Option.bind_some]
    have : binaryValue .lt u w = if u < w then 1 else 0 := rfl
    rw [this]
    unfold Ty.convert
    by_cases h : u < w <;> simp [h]
  have huw : (u < w) ↔ ((if i = 0 then x else y) < (if j = 0 then x else y)) := by rw [hu.2, hw.2]
  have hskip := pexec_skip 1 ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩
  by_cases hlt : u < w
  · rw [ite_eq_left hlt] at hcond
    have st := pstmt_assign_ok ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 (.variable s64 1) y
      (by rw [den_variable]; exact e1') ⟨P.length,true⟩ ⟨s64,x⟩ (by simp) (by simp) rfl hxv rfl y (convS _ hyv)
    have hset : (P ++ [(⟨s64,x⟩ : Cell)]).set P.length ⟨s64,y⟩ = P ++ [(⟨s64,y⟩ : Cell)] := by
      simp [List.set_append_right]
    rw [hset] at st
    have yes := pexec_braced 1 (.assign 2 s64 (.variable s64 1)) _ _ st rfl (by simp) (by simp)
    have br := pexec_branch_true 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ 1 hcond (by decide) _ yes
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := copied_tail_exec P a b y hyv
    have q3 : pexec 1 copiedTail ⟨P ++ [(⟨s64,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
      simpa [ws] using qt
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_left (huw.mp hlt)]; exact hrt
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega
    · rw [ite_eq_left (huw.mp hlt)]; exact hmt
  · rw [ite_eq_right hlt] at hcond
    have br := pexec_branch_false 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ hcond _ hskip
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := copied_tail_exec P a b x hxv
    have q3 : pexec 1 copiedTail ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
      simpa [ws] using qt
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right (fun h => hlt (huw.mpr h))]; exact hrt
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega
    · rw [ite_eq_right (fun h => hlt (huw.mpr h))]; exact hmt

theorem mul_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (hxy : s64.valid (x*y) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.op_MonoidMul_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.MonoidInstance.op_MonoidMul_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x*y)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  refine refs2_correct _ rfl rfl (by decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x*y) hxy 10 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := mul_exec (callerP caller) ba.address bb.address x y hxv hyv hxy (P_cell caller sa ba x ca)
    (P_cell caller sb bb y cb)
  exact ⟨r,h1,h2,h3,h4,by rw [h5]; exact take_P caller _⟩

theorem max_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.op_MonoidMax_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.MonoidInstance.op_MonoidMax_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((if x < y then y else x))) ∧
      ScalarPost2 caller Sinit res 0 100 caller.scalars.memory := by
  have hres : s64.valid ((if x < y then y else x)) = true := by
    by_cases h : x < y
    · simp only [h, if_true]; exact hyv
    · simp only [h, if_false]; exact hxv
  refine refs2_correct _ rfl rfl (by rw [max_body]; decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 ((if x < y then y else x)) hres 40 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := copied_sel_exec 0 1 (by omega) (callerP caller) ba.address bb.address x y hxv hyv
    (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  refine ⟨r,by rw [max_body]; exact h1,?_,h3,h4,by rw [h5]; exact take_P caller _⟩
  rw [h2]
  simp

theorem min_op_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.op_MonoidMin_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.MonoidInstance.op_MonoidMin_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((if y < x then y else x))) ∧
      ScalarPost2 caller Sinit res 0 100 caller.scalars.memory := by
  have hres : s64.valid ((if y < x then y else x)) = true := by
    by_cases h : y < x
    · simp only [h, if_true]; exact hyv
    · simp only [h, if_false]; exact hxv
  refine refs2_correct _ rfl rfl (by rw [min_body]; decide) caller sa sb ba bb x y ca cb valid lengths strict base 1 ((if y < x then y else x)) hres 40 ?_
  intro P hP
  subst hP
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := copied_sel_exec 1 0 (by omega) (callerP caller) ba.address bb.address x y hxv hyv
    (P_cell caller sa ba x ca) (P_cell caller sb bb y cb)
  refine ⟨r,by rw [min_body]; exact h1,?_,h3,h4,by rw [h5]; exact take_P caller _⟩
  rw [h2]
  simp

theorem mul_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMul_long_long_new1.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMul_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar (1)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory  :=
  Proofs.GroupCall.default_correct _ false (.cast s64 (.literal i32 1)) 1 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base

theorem mul_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMul_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMul_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correct _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

theorem max_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMax_long_long_new1.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMax_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar (-9223372036854775808)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory  :=
  Proofs.GroupCall.default_correct _ false (.literal s64 (-9223372036854775808)) (-9223372036854775808) rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base

theorem max_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMax_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMax_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correct _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

theorem min_default_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMin_long_long_new1.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMin_long_long_new1.callFuel fuel caller [] = .finished (res,.scalar (9223372036854775807)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory  :=
  Proofs.GroupCall.default_correct _ false (.literal s64 9223372036854775807) 9223372036854775807 rfl rfl rfl
    (by intro env; simp [NExpr.denote, Ty.valid])
    (by decide) (by decide) (by decide) (by simp)
    caller valid lengths strict base

theorem min_new_correct (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMin_long_long_new0.parameters [.value e] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMin_long_long_new0.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  ctor_correct _ rfl rfl rfl caller e v hs hty value hv valid lengths strict base

theorem mul_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMul_long_long_e.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMul_long_long_e.callFuel fuel caller [] = .finished (res,.scalar (1)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem max_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMax_long_long_e.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMax_long_long_e.callFuel fuel caller [] = .finished (res,.scalar (-9223372036854775808)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem min_e_correct (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.MonoidInstance.MonoidMin_long_long_e.parameters [] = some Sinit ∧
      Proofs.MonoidInstance.MonoidMin_long_long_e.callFuel fuel caller [] = .finished (res,.scalar (9223372036854775807)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  e_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly])
    (by simp [NExpr.nodes]) (by simp [Ty.valid]) caller valid lengths strict base

theorem mul_friend_op_eq : Proofs.MonoidInstance.MonoidMul_long_long_op = Proofs.MonoidInstance.op_MonoidMul_long_long := rfl
theorem max_friend_op_eq : Proofs.MonoidInstance.MonoidMax_long_long_op = Proofs.MonoidInstance.op_MonoidMax_long_long := rfl
theorem min_friend_op_eq : Proofs.MonoidInstance.MonoidMin_long_long_op = Proofs.MonoidInstance.op_MonoidMin_long_long := rfl

end Proofs.MonoidCall
