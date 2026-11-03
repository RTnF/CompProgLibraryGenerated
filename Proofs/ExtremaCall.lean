import Proofs.ExtremaRef
import Proofs.ScalarCall

namespace Proofs.ExtremaCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ExtremaRef Proofs.ScalarCall
open Proofs.CppState (Cell)

theorem scalarCell_facts {s : NState} {slot : Nat} {ty : Ty} {binding : CppState.Binding} {cell : Cell}
    (h : s.scalarCell slot ty = some (binding,cell)) :
    ∃ idx, s.slots[slot]? = some (.scalar idx) ∧ s.scalars.bindings[idx]? = some binding ∧
      s.scalars.memory[binding.address]? = some cell ∧ cell.type = ty ∧ ty.valid cell.value = true := by
  unfold NState.scalarCell NState.scalarSlot at h
  cases hs : s.slots[slot]? with
  | none => simp [hs] at h
  | some loc =>
    cases loc with
    | vector n => simp [hs] at h
    | scalar idx =>
      simp only [hs,Bind.bind,Option.bind] at h
      cases hb : s.scalars.bindings[idx]? with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h
        cases hm : s.scalars.memory[b.address]? with
        | none => simp [hm] at h
        | some c =>
          simp only [hm] at h
          by_cases ok : c.type = ty ∧ ty.valid c.value
          · simp [ok] at h
            obtain ⟨hb',hc'⟩ := h
            subst hb' hc'
            exact ⟨idx,rfl,hb,hm,ok.1,by simpa using ok.2⟩
          · simp [ok] at h


theorem prepare_ch (caller : NState) (prog : NProgram) (hp : prog.parameters = [.scalar s64 true true,.scalar s64 true false])
    (sa sb : Nat) (ba bb : CppState.Binding) (va vb : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,va⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,vb⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Sinit.slots = slots0 ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = bind0 ba.address bb.address ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have cb' : (caller.charge 1 1).scalarCell sb s64 = some (bb,⟨s64,vb⟩) := cb
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  obtain ⟨ib,_,_,hmb,_,vvb⟩ := scalarCell_facts cb
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hma' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[ba.address]? = some ⟨s64,va⟩ := by rw [List.getElem?_append_left lta]; exact hma
  have hmb' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[bb.address]? = some ⟨s64,vb⟩ := by rw [List.getElem?_append_left ltb]; exact hmb
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,ca,cb',wa]
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,bind0,slots0,
    hma',hmb',vva,vvb]
  refine ⟨rfl,?_⟩
  simp only [charge_scalar_peak]
  omega


theorem take_set_memory (M pad extra : List Cell) (aa : Nat) (v : Cell) (h : aa < M.length) :
    ((M ++ pad).set aa v ++ extra).take M.length = M.set aa v := by
  rw [List.set_append_left aa v h,List.append_assoc]
  exact List.take_left' (by simp)

theorem take_plain_memory (M pad extra : List Cell) : ((M ++ pad) ++ extra).take M.length = M := by
  rw [List.append_assoc]; exact List.take_left

set_option maxHeartbeats 4000000 in
theorem ch_correct (caller : NState) (prog : NProgram) (i j : Nat) (hp : prog.parameters = [.scalar s64 true true,.scalar s64 true false])
    (hbody : prog.body = chCmd i j) (hres : prog.result = ResultKind.scalar bl)
    (sa sb : Nat) (ba bb : CppState.Binding) (va vb x y : Int)
    (hxy : (i = 0 ∧ j = 1 ∧ x = va ∧ y = vb) ∨ (i = 1 ∧ j = 0 ∧ x = vb ∧ y = va))
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,va⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,vb⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (if x < y then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 60
        (if x < y then caller.scalars.memory.set ba.address ⟨s64,vb⟩ else caller.scalars.memory) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_ch caller prog hp sa sb ba bb va vb ca cb wa valid
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  obtain ⟨ib,_,_,hmb,_,vvb⟩ := scalarCell_facts cb
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have hma' : (callerP caller)[ba.address]? = some ⟨s64,va⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hmb' : (callerP caller)[bb.address]? = some ⟨s64,vb⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  have qs : QS Sinit (callerP caller) caller.scalars.baseMemory (caller.scope+1) [] (bind0 ba.address bb.address)
      slots0 := ⟨sSlots,by rw [sMem]; simp,sBind,sBase,sScope⟩
  have fa : FA Sinit.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length := by
    refine ⟨by rw [sState]; exact valid,by rw [sState,sRw]; exact lengths,by rw [sState],by rw [sState],?_,sFb,by rw [sState]⟩
    intro owner c h
    rw [sState] at h
    have := strict owner c h
    omega
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := ch_run (L0 := caller.frame.state.liveSpace) (T0 := caller.frame.state.storage.work)
    (N := caller.frame.state.storage.objects.length) (scq := caller.scope+1) (W := Sinit.scalars.work) i j
    ba.address bb.address va vb x y hxy hma' hmb' vva vvb Sinit qs fa cq
    (by show (callerP caller).length+3-caller.scalars.baseMemory+3+40 ≤ SPB; rw [hSPB]; omega) (Nat.le_refl _)
    (by rw [hTPB]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,D,stepEq,qsD,faD,cqD⟩ := run
  have cval : bl.valid (if x < y then 1 else 0) = true := by by_cases c : x < y <;> simp [c,Ty.valid]
  have memD : D.scalars.memory = (if x < y then (callerP caller).set ba.address ⟨s64,vb⟩ else callerP caller) ++
      [⟨bl,(if x < y then 1 else 0)⟩] := qsD.memory
  have htake : (D.charge 1 0).scalars.memory.take caller.scalars.memory.length =
      (if x < y then caller.scalars.memory.set ba.address ⟨s64,vb⟩ else caller.scalars.memory) := by
    show D.scalars.memory.take caller.scalars.memory.length = _
    rw [memD]
    by_cases c : x < y
    · simp only [c,if_true]
      simp only [callerP]
      exact take_set_memory _ _ _ _ _ lta
    · simp only [c,if_false]
      simp only [callerP]
      exact take_plain_memory _ _ _
  have hmemLen : (if x < y then caller.scalars.memory.set ba.address ⟨s64,vb⟩ else caller.scalars.memory).length =
      caller.scalars.memory.length := by
    by_cases c : x < y <;> simp [c]
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      ((D.charge 1 0).scalars.memory.take caller.scalars.memory.length).map Cell.type =
        caller.scalars.memory.map Cell.type := by
    rw [htake]
    refine ⟨?_,?_⟩
    · show caller.scalars.memory.length ≤ D.scalars.memory.length
      rw [memD]
      by_cases c : x < y <;> simp [c,callerP] <;> omega
    · by_cases c : x < y
      · simp only [c,if_true]
        exact map_type_set caller.scalars.memory ba.address va vb hma
      · simp [c]
  have scopeD : D.scope = caller.scope+1 := qsD.scope
  have fresh : ∀ owner, (D.charge 1 0).frame.state.forest.context owner ≠ some (D.charge 1 0).scope := by
    intro owner h
    have := faD.strict owner _ h
    show False
    have e : (D.charge 1 0).scope = caller.scope+1 := scopeD
    omega
  have fin := finish_scalar caller (D.charge 1 0) bl _ cval cond faD.valid fresh
  refine ⟨Sinit,fuel,finS caller (D.charge 1 0),hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel prog.body Sinit = .finished step := by rw [hbody]; exact hrun
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,hres,ret,stepEq,fin]
    simp
  · have liveD : liveS D = (callerP caller).length+1-caller.scalars.baseMemory+3 := by
      have := qsD.live_eq
      have hl : (if x < y then (callerP caller).set ba.address ⟨s64,vb⟩ else callerP caller).length =
          (callerP caller).length := by by_cases c : x < y <;> simp [c]
      simp [bind0,hl] at this
      omega
    have cqR : Cq SPB TPB (Sinit.scalars.work+30+1) (D.charge 1 0) := by
      have := cqD.good (Good.charge D 1 0) (by
        show liveS D + 0 ≤ SPB
        rw [liveD,hSPB]; omega)
      exact this.mono (by omega)
    exact scalar_post2 caller Sinit (D.charge 1 0) 0 60 _ hSPB hTPB htake hmemLen qsD.base base
      sPeak faD cqR (by
      have := cqD.work
      have c1 : (D.charge 1 0).scalars.work = D.scalars.work+1 := rfl
      omega)


-- `cp::chmax(a, b)`: `a` becomes `b` exactly when `a < b`, and the result tells whether it did.
theorem chmax_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (va vb : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,va⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,vb⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.ExtremaLibInstance.chmax_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.ExtremaLibInstance.chmax_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (if va < vb then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 60
        (if va < vb then caller.scalars.memory.set ba.address ⟨s64,vb⟩ else caller.scalars.memory) :=
  ch_correct caller Proofs.ExtremaLibInstance.chmax_long_long 0 1 rfl chmax_body_eq rfl sa sb ba bb va vb va vb
    (Or.inl ⟨rfl,rfl,rfl,rfl⟩) ca cb wa valid lengths strict base

-- `cp::chmin(a, b)`: `a` becomes `b` exactly when `b < a`.
theorem chmin_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (va vb : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,va⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,vb⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.ExtremaLibInstance.chmin_long_long.parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Proofs.ExtremaLibInstance.chmin_long_long.callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (if vb < va then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 60
        (if vb < va then caller.scalars.memory.set ba.address ⟨s64,vb⟩ else caller.scalars.memory) :=
  ch_correct caller Proofs.ExtremaLibInstance.chmin_long_long 1 0 rfl chmin_body_eq rfl sa sb ba bb va vb vb va
    (Or.inr ⟨rfl,rfl,rfl,rfl⟩) ca cb wa valid lengths strict base

end Proofs.ExtremaCall
