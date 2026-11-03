import Proofs.ModIntCall
import Proofs.Generated.Monoid

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

theorem s64_valid_int (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) : s64.valid v = true :=
  s64_valid_of v h0 h1

-- A constructor-like function without parameters whose body is `return e` for a closed expression.
theorem const_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
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
    (by omega) (by rw [takeM]) valid lengths strict base (by rw [hb]; simp [Scalar, hs]) 1 _ hexec _ rfl s64 hr hv
    (by simp; omega) (by simp) 0 70 (by simp; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post

-- The constructor from a value: `return x_`.
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
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ s64 hp e v hs hty value valid hv
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have takeM2 : (callerP caller ++ [(⟨s64,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  have e0 : penv ⟨callerP caller ++ [⟨s64,v⟩],[⟨(callerP caller).length,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨(callerP caller).length,true⟩ ⟨s64,v⟩ rfl (by simpa using get_tail (callerP caller) [⟨s64,v⟩] 0) rfl hv
  have q := exec_ret 1 ⟨callerP caller ++ [⟨s64,v⟩],[⟨(callerP caller).length,true⟩]⟩ (.variable s64 0) v
    (by rw [den_variable]; exact e0)
  have hexec : pexec 1 prog.body ⟨callerP caller ++ [⟨s64,v⟩],[⟨(callerP caller).length,true⟩]⟩ =
      some ⟨(⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[(⟨(callerP caller).length,true⟩ : CppState.Binding)]⟩ : PS),some v,
        (NExpr.variable s64 0).nodes+1,
        (callerP caller ++ [(⟨s64,v⟩ : Cell)]).length+1+(NExpr.variable s64 0).nodes+2⟩ := by rw [hb]; simpa using q
  have gw := good.2.2.1
  have hpost := call_scalar caller prog [.value e] Sinit
    (callerP caller ++ [(⟨s64,v⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame
    (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base (by rw [hb]; simp [Scalar, NExpr.scalarOnly])
    1 _ hexec _ rfl s64 hr hv (by simp [NExpr.nodes]) (by simp) e.nodes 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM2] at post
  exact post

-- Two read-only reference parameters, the body given by an execution hypothesis on the reserved memory.
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

theorem convS (v : Int) (h : s64.valid v = true) : s64.convert v = some v := by
  rw [valid_s64] at h
  have := of_decide_eq_true h
  exact convert_s64 v this.1 this.2

theorem mul_exec (P : List Cell) (a b : Nat) (x y : Int) (hxv : s64.valid x = true) (hyv : s64.valid y = true)
    (hxy : s64.valid (x*y) = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 Proofs.MonoidInstance.op_MonoidMul_long_long.body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (x*y) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,x*y⟩,⟨s64,x*y⟩] := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl ha rfl hxv
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 s64 = some y :=
    penv_ok _ 1 s64 ⟨b,false⟩ ⟨s64,y⟩ rfl hb rfl hyv
  have hbv : binaryValue .mul x y = x*y := rfl
  have d1 : (NExpr.binary s64 .mul (.variable s64 0) (.variable s64 1)).denote (penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩) = some (x*y) := by
    rw [den_binary, den_variable, den_variable, e0, e1]
    simp only [Option.bind_some, hbv]
    exact convS _ hxy
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ s64 true _ (x*y) d1 (x*y) (convS _ hxy)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv ⟨P ++ [(⟨s64,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 = some (x*y) :=
    penv_ok _ 2 s64 ⟨P.length,true⟩ ⟨s64,x*y⟩ (by simp) (by simp) rfl hxy
  have d2 : (NExpr.variable s64 2).denote (penv ⟨P ++ [(⟨s64,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (x*y) := by
    rw [den_variable]; exact e2
  have s2 := pstmt_declare_ok ⟨P ++ [(⟨s64,x*y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ s64 true _ (x*y) d2 (x*y) (convS _ hxy)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e3 : penv ⟨P ++ [(⟨s64,x*y⟩ : Cell)] ++ [⟨s64,x*y⟩],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩] ++ [⟨(P ++ [(⟨s64,x*y⟩ : Cell)]).length,true⟩]⟩ 3 s64 = some (x*y) :=
    penv_ok _ 3 s64 ⟨P.length+1,true⟩ ⟨s64,x*y⟩ (by simp) (by simp) rfl hxy
  have q3 := exec_ret 1 ⟨P ++ [(⟨s64,x*y⟩ : Cell)] ++ [⟨s64,x*y⟩],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩] ++ [⟨(P ++ [(⟨s64,x*y⟩ : Cell)]).length,true⟩]⟩
    (.variable s64 3) (x*y) (by rw [den_variable]; exact e3)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  refine ⟨_, q123, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]
  · simp

abbrev bT : Ty := ⟨1, false, true⟩

abbrev selBody (i j : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.variable s64 0)))
    (.sequence (.branch (.binary bT .lt (.variable s64 i) (.variable s64 j))
        (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk)
      (.sequence (.primitive (.ret (.variable s64 2))) Sk))

theorem max_body : Proofs.MonoidInstance.op_MonoidMax_long_long.body = selBody 0 1 := rfl
theorem min_body : Proofs.MonoidInstance.op_MonoidMin_long_long.body = selBody 1 0 := rfl

theorem sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (selBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] := by
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
  have e2' : penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 = some x :=
    penv_ok _ 2 s64 ⟨P.length,true⟩ ⟨s64,x⟩ (by simp) (by simp) rfl hxv
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
    by_cases h : u < w <;> simp [bT, h]
  have huw : (u < w) ↔ ((if i = 0 then x else y) < (if j = 0 then x else y)) := by rw [hu.2, hw.2]
  have hskip := pexec_skip 1 ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩
  by_cases hlt : u < w
  · rw [if_pos hlt] at hcond
    have st := pstmt_assign_ok ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 (.variable s64 1) y
      (by rw [den_variable]; exact e1') ⟨P.length,true⟩ ⟨s64,x⟩ (by simp) (by simp) rfl hxv rfl y (convS _ hyv)
    have hset : (P ++ [(⟨s64,x⟩ : Cell)]).set P.length ⟨s64,y⟩ = P ++ [(⟨s64,y⟩ : Cell)] := by
      simp [List.set_append_right]
    rw [hset] at st
    have yes := pexec_braced 1 (.assign 2 s64 (.variable s64 1)) _ _ st rfl (by simp) (by simp)
    have br := pexec_branch_true 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ 1 hcond (by decide) _ yes
    have e3 : penv ⟨P ++ [(⟨s64,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 = some y :=
      penv_ok _ 2 s64 ⟨P.length,true⟩ ⟨s64,y⟩ (by simp) (by simp) rfl hyv
    have q3 := exec_ret 1 ⟨P ++ [(⟨s64,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ (.variable s64 2) y
      (by rw [den_variable]; exact e3)
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (huw.mp hlt)]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rw [if_pos (huw.mp hlt)]
  · rw [if_neg hlt] at hcond
    have br := pexec_branch_false 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ hcond _ hskip
    have q3 := exec_ret 1 ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ (.variable s64 2) x
      (by rw [den_variable]; exact e2')
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (fun h => hlt (huw.mpr h))]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rw [if_neg (fun h => hlt (huw.mpr h))]

theorem P_cell (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) : (callerP caller)[ba.address]? = some ⟨s64,x⟩ := by
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory := by
  have : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hl : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
  rw [List.take_append_of_le_length hl]; exact this

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
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := sel_exec 0 1 (by omega) (callerP caller) ba.address bb.address x y hxv hyv
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
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := sel_exec 1 0 (by omega) (callerP caller) ba.address bb.address x y hxv hyv
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
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly]) (by simp [NExpr.nodes])
    (by simp [Ty.valid]) caller valid lengths strict base

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
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64, unaryValue, binaryValue]) (by simp [NExpr.scalarOnly]) (by simp [NExpr.nodes])
    (by simp [Ty.valid]) caller valid lengths strict base

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
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  const_correct _ _ _ rfl rfl rfl (by intro env; simp [NExpr.denote, Ty.valid, Ty.convert, s64]) (by simp [NExpr.scalarOnly]) (by simp [NExpr.nodes])
    (by simp [Ty.valid]) caller valid lengths strict base

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

-- The static `e()`: `declare r = e; declare s = r; return s` for a closed expression `e`.
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
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ hp valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have s1 := pstmt_declare_ok ⟨callerP caller,[]⟩ s64 true e v (he _) v (convS _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e1 : penv ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[] ++ [⟨(callerP caller).length,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨(callerP caller).length,true⟩ ⟨s64,v⟩ (by simp) (by simp) rfl hv
  have s2 := pstmt_declare_ok ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)],[] ++ [⟨(callerP caller).length,true⟩]⟩ s64 true
    (.variable s64 0) v (by rw [den_variable]; exact e1) v (convS _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e2 : penv ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)] ++ [(⟨s64,v⟩ : Cell)],
      [] ++ [⟨(callerP caller).length,true⟩] ++ [⟨(callerP caller ++ [(⟨s64,v⟩ : Cell)]).length,true⟩]⟩ 1 s64 = some v :=
    penv_ok _ 1 s64 ⟨(callerP caller).length+1,true⟩ ⟨s64,v⟩ (by simp) (by simp) rfl hv
  have q3 := exec_ret 1 ⟨callerP caller ++ [(⟨s64,v⟩ : Cell)] ++ [(⟨s64,v⟩ : Cell)],
      [] ++ [⟨(callerP caller).length,true⟩] ++ [⟨(callerP caller ++ [(⟨s64,v⟩ : Cell)]).length,true⟩]⟩
    (.variable s64 1) v (by rw [den_variable]; exact e2)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  have hexec := q123
  rw [← hb] at hexec
  have hpost := call_scalar caller prog [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base (by rw [hb]; simp [Scalar, hs, NExpr.scalarOnly]) 1 _ hexec _ rfl s64 hr hv
    (by simp [NExpr.nodes] at hn ⊢; omega) (by simp) 0 70 (by simp [NExpr.nodes] at hn ⊢; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have e3 : callerP caller ++ [(⟨s64,v⟩ : Cell)] ++ [(⟨s64,v⟩ : Cell)] = callerP caller ++ [(⟨s64,v⟩ : Cell),⟨s64,v⟩] := by
    simp
  rw [e3, take_P caller] at post
  exact post

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

end Proofs.MonoidCall
