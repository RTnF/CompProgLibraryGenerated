import Proofs.CountLoop
import Proofs.Generated.SearchUtil
import Proofs.DoublingCall

namespace Proofs.CountCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.CountLoop
open Proofs.CppState (Cell)

theorem body_eq : Proofs.SearchUtilInstance.count_std_vector_int.body = cbody := rfl

theorem resolve_i32 (S : NState) (ex : NExpr) (x : Int) (hs : ex.scalarOnly = true)
    (ty : ex.resultType = i32) (value : ex.denote (envOf S) = some x) :
    ∃ t, Good S t ex.nodes ex.nodes ∧ resolve S (.scalar i32 false true) (.value ex) = some (t,.scalar i32 true x) := by
  obtain ⟨t,ran,good⟩ := scalar_eval ex S x hs value
  exact ⟨t,good,by simp [resolve,ty,ran]⟩

theorem prepare_count (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) (vE bE eE : NExpr) (v b e : Int)
    (hv : vE.scalarOnly = true) (hb : bE.scalarOnly = true) (he : eE.scalarOnly = true)
    (tv : vE.resultType = i32) (tb : bE.resultType = i32) (te : eE.resultType = i32)
    (dv : vE.denote (envOf caller) = some v) (db : bE.denote (envOf caller) = some b)
    (de : eE.denote (envOf caller) = some e)
    (vv : i32.valid v = true) (bv : i32.valid b = true) (ev : i32.valid e = true) :
    ∃ t1 t2 t3, Good (caller.charge 1 1) t1 vE.nodes vE.nodes ∧ Good t1 t2 bE.nodes bE.nodes ∧
      Good t2 t3 eE.nodes eE.nodes ∧
      ∃ Sinit, prepare caller Proofs.SearchUtilInstance.count_std_vector_int.parameters
          [.vectorReference vslot,.value vE,.value bE,.value eE] = some Sinit ∧
        Sinit.slots = sl 3 ∧ Sinit.scalars.memory = callerP caller ++ C3 v b e ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[vbind V vsc]⟩ ∧
        Sinit.scalars.work = t3.scalars.work+5 ∧ t3.scalars.peak ≤ Sinit.scalars.peak := by
  have rvec := resolve_vec caller ok
  obtain ⟨t1,g1,r1⟩ := resolve_i32 (caller.charge 1 1) vE v hv tv (by rw [envOf_core (core_charge caller 1 1)]; exact dv)
  obtain ⟨t2,g2,r2⟩ := resolve_i32 t1 bE b hb tb (by rw [envOf_core g1.1,envOf_core (core_charge caller 1 1)]; exact db)
  obtain ⟨t3,g3,r3⟩ := resolve_i32 t2 eE e he te
    (by rw [envOf_core g2.1,envOf_core g1.1,envOf_core (core_charge caller 1 1)]; exact de)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have frameT : t3.frame = caller.frame := by
    rw [g3.1.1,g2.1.1,g1.1.1]; rfl
  have hmem : t3.scalars.memory = caller.scalars.memory := by
    have a := g3.1.2.2.2.1; have b' := g2.1.2.2.2.1; have c := g1.1.2.2.2.1
    rw [a,b',c]; rfl
  have hbind : t3.scalars.bindings = caller.scalars.bindings := by
    have a := g3.1.2.2.2.2.1; have b' := g2.1.2.2.2.2.1; have c := g1.1.2.2.2.2.1
    rw [a,b',c]; rfl
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g3.1.2.2.2.2.2; have b' := g2.1.2.2.2.2.2; have c := g1.1.2.2.2.2.2
    rw [a,b',c]; rfl
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have bound := bindRoot_v caller.frame.state caller.frame.rootWritable ok.valid ok.vtag ok.vfound ok.lengths ok.flag
  simp [prepare,ok.valid,resolveAll,rvec,r1,r2,r3,Proofs.SearchUtilInstance.count_std_vector_int]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,bound,CppState.bindArgument,vv,bv,ev,callerP,sl,C3,
    NState.observe,CppState.State.observe,vbind,atom]
  exact ⟨rfl,Nat.le_max_left _ _⟩


def finScalar (caller R : NState) : NState :=
  let scalars : CppState.State := {caller.scalars with
    memory := R.scalars.memory.take caller.scalars.memory.length,
    work := R.scalars.work+1,peak := max caller.scalars.peak R.scalars.peak}
  let frame : Frame := {noopRetired R.frame with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak R.peak⟩ : NState).observe

theorem finish_count (caller R : NState) (c : Int) (hc : i32.valid c = true)
    (cond : caller.scalars.memory.length ≤ R.scalars.memory.length ∧
      (R.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (valid : R.frame.state.wellFormed = true) (fresh : ∀ owner, R.frame.state.forest.context owner ≠ some R.scope) :
    finish caller R (.scalar i32) (some (.scalar c)) = some (finScalar caller R,.scalar c) := by
  have retired := retireScope_fresh R.frame R.scope valid fresh
  unfold finish
  rw [if_pos cond]
  simp only [hc,if_true,retired,Bind.bind,Option.bind]
  rfl


-- The number of positions j in [b, E) whose entry equals x.
def countSpec (items : List Int) (x : Int) (b E : Nat) : Nat :=
  ((List.range' b (E-b)).filter fun j => items[j]? == some x).length

theorem cntU_eq (items : List Int) (x : Int) (b k : Nat) :
    cntU items x b k = ((List.range' b k).filter fun j => items[j]? == some x).length := by
  induction k with
  | zero => simp [cntU]
  | succ k ih =>
      rw [List.range'_concat,List.filter_append,List.length_append,← ih]
      simp only [cntU,Nat.mul_one]
      by_cases h : items[b+k]? = some x <;> simp [h]

theorem cnt_spec (items : List Int) (x : Int) (b E : Nat) : cntU items x b (E-b) = countSpec items x b E :=
  cntU_eq items x b (E-b)


structure CountPost (caller Sinit res : NState) (kn : Nat) (V : Nat) (vbuf : Buffer Value) (b E : Nat) : Prop where
  valid : res.frame.state.wellFormed = true
  vKept : res.frame.state.storage.lookup V = some vbuf
  rootWritable : res.frame.rootWritable = caller.frame.rootWritable
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak caller.frame.state.liveSpace
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+108*(E-b)+300
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+130-caller.scalars.baseMemory)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+130-caller.scalars.baseMemory) +
    max caller.frame.state.storage.peak caller.frame.state.liveSpace)

def mkF (caller : NState) (V vsc : Nat) (items : List Int) (vbuf : Buffer Value) (SPB TPB : Nat) : Fixed :=
  ⟨callerP caller,caller.scalars.baseMemory,0,items.length,0,V,vsc,caller.frame.state.storage.objects.length,
    caller.scope+1,caller.frame.rootWritable,items,vbuf,SPB,TPB⟩

set_option maxHeartbeats 4000000 in
theorem count_correct (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) (items : List Int)
    (hv : vbuf.items = items.map Value.integer) (hn : items.length < 2147483648)
    (vE bE eE : NExpr) (v : Int) (b : Nat) (e : Int)
    (hsv : vE.scalarOnly = true) (hsb : bE.scalarOnly = true) (hse : eE.scalarOnly = true)
    (tv : vE.resultType = i32) (tb : bE.resultType = i32) (te : eE.resultType = i32)
    (dv : vE.denote (envOf caller) = some v) (db : bE.denote (envOf caller) = some (b : Int))
    (de : eE.denote (envOf caller) = some e)
    (vv : i32.valid v = true) (hb : b < 2147483648) (hev : i32.valid e = true)
    (E : Nat) (hE : (if e = -1 then (items.length : Int) else e) = (E : Int)) (hEl : E ≤ items.length) :
    ∃ Sinit fuel res, prepare caller Proofs.SearchUtilInstance.count_std_vector_int.parameters
        [.vectorReference vslot,.value vE,.value bE,.value eE] = some Sinit ∧
      Proofs.SearchUtilInstance.count_std_vector_int.callFuel fuel caller [.vectorReference vslot,.value vE,.value bE,.value eE] =
        .finished (res,.scalar ((countSpec items v b E : Nat) : Int)) ∧
      CountPost caller Sinit res (vE.nodes+bE.nodes+eE.nodes) V vbuf b E := by
  have bv : i32.valid (b : Int) = true := i32_valid_nat b hb
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_count caller ok vE bE eE v b e hsv hsb hse tv tb te dv db de vv bv hev
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [vbind V vsc] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+130-caller.scalars.baseMemory) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    have := ok.base
    omega
  have hspb : (callerP caller).length+130-caller.scalars.baseMemory ≤ SPB := by rw [hSPB]; omega
  have sPk : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
  have hL : caller.frame.state.liveSpace ≤ TPB := by rw [hTPB]; omega
  have hvn : vbuf.items.length = items.length := by rw [hv]; simp
  have ps : PS (mkF caller V vsc items vbuf SPB TPB) (caller.scope+1) caller.frame.rootWritable Sinit (C3 v b e)
      (bn (mkF caller V vsc items vbuf SPB TPB) 3) (sl 3) := by
    refine ⟨sSlots,sMem,?_,sBase,sScope,sFb,sRw⟩
    rw [sBind]
    simp [bn,mkF,List.range_succ]
  have vf : VF (mkF caller V vsc items vbuf SPB TPB) caller.frame.state.liveSpace caller.frame.state.storage.work
      Sinit.frame := by
    refine ⟨by rw [sState]; exact ok.valid,by rw [sState]; exact ok.vtag,by rw [sState]; exact ok.vfound,
      by rw [sState,sRw]; exact ok.lengths,by rw [sRw]; exact ⟨m,ok.flag⟩,?_,by rw [sState],by rw [sState],
      by rw [sState]; rfl⟩
    intro owner c h
    rw [sState] at h
    have := ok.strict owner c h
    show c < caller.scope+1
    omega
  have cb : Cb (mkF caller V vsc items vbuf SPB TPB) Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sPk]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := CountLoop.body_run (mkF caller V vsc items vbuf SPB TPB) items hv (W := Sinit.scalars.work) (v := v) (e := e)
    (b := b) (E := E) Sinit hn hvn hE hEl hb hev (by show caller.scope+1 ≤ Sinit.scope; omega) hL vv hB hspb ps.self vf cb
  obtain ⟨fuel,step,hrun,ret,brk,psR,vfR,cbR⟩ := run
  have cle := cntU_le items v b (E-b)
  have cv : i32.valid ((cntU items v b (E-b) : Nat) : Int) = true := i32_valid_nat _ (by omega)
  have scopeR : step.state.scope = caller.scope+1 := by rw [psR.scope]; exact sScope
  have memR : step.state.scalars.memory = callerP caller ++ (C3 v b E ++ [⟨i32,(cntU items v b (E-b) : Nat)⟩]) := by
    rw [psR.memory]; rfl
  have take : step.state.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [memR]
    simp only [callerP,List.append_assoc]
    exact List.take_left
  have cond : caller.scalars.memory.length ≤ step.state.scalars.memory.length ∧
      (step.state.scalars.memory.take caller.scalars.memory.length).map Cell.type =
        caller.scalars.memory.map Cell.type := by
    rw [take]
    refine ⟨?_,rfl⟩
    rw [memR]; simp [callerP]
  have fresh : ∀ owner, step.state.frame.state.forest.context owner ≠ some step.state.scope := by
    intro owner h
    rw [scopeR] at h
    have := vfR.strict owner _ h
    show False
    have e2 : (mkF caller V vsc items vbuf SPB TPB).sc = caller.scope+1 := rfl
    omega
  have fin := finish_count caller step.state _ cv cond vfR.valid fresh
  refine ⟨Sinit,fuel,finScalar caller step.state,hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel Proofs.SearchUtilInstance.count_std_vector_int.body Sinit = .finished step := hrun
    have res : Proofs.SearchUtilInstance.count_std_vector_int.result = ResultKind.scalar i32 := rfl
    rw [← cnt_spec] 
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,ret,fin]
    simp
  · have same := noopRetired_same step.state.frame
    have lenP : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have a1 := g1.2.2.2.2.1
      have a2 := g2.2.2.2.2.1
      have a3 := g3.2.2.2.2.1
      have c0 : caller.scalars.peak ≤ (caller.charge 1 1).scalars.peak := by
        rw [charge_scalar_peak]; exact Nat.le_max_left _ _
      omega
    have gw1 := g1.2.2.1
    have gw2 := g2.2.2.1
    have gw3 := g3.2.2.1
    have cw : (caller.charge 1 1).scalars.work = caller.scalars.work+1 := rfl
    have resWork : (finScalar caller step.state).scalars.work = step.state.scalars.work+1 := rfl
    have resSp : (finScalar caller step.state).scalars.peak =
        max (max caller.scalars.peak step.state.scalars.peak)
          ((step.state.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
    have resPeak : (finScalar caller step.state).peak =
        max (max caller.peak step.state.peak) ((finScalar caller step.state).scalars.peak +
          (finScalar caller step.state).frame.state.storage.peak) := rfl
    have takeLen : (step.state.scalars.memory.take caller.scalars.memory.length).length =
        caller.scalars.memory.length := by rw [take]
    have spR := cbR.scalarPeak
    have stR := cbR.storagePeak
    have opR := cbR.outerPeak
    have hbm := ok.base
    have spRes : (finScalar caller step.state).scalars.peak ≤ SPB := by
      rw [resSp,takeLen]
      have : SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+130-caller.scalars.baseMemory) := hSPB
      have h2 : caller.scalars.peak ≤ SPB := by rw [this]; omega
      have h3 : step.state.scalars.peak ≤ SPB := spR
      have h4 : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
        rw [this]; omega
      omega
    have liveR : step.state.frame.state.liveSpace = caller.frame.state.liveSpace := vfR.live
    have stRes : (finScalar caller step.state).frame.state.storage.peak ≤ TPB := by
      show max step.state.frame.state.storage.peak
        (step.state.frame.state.liveSpace-step.state.frame.state.storage.baseSpace) ≤ TPB
      rw [liveR]
      have : TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := hTPB
      have h5 : step.state.frame.state.storage.peak ≤ TPB := stR
      omega
    refine ⟨?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
    · show (noopRetired step.state.frame).state.wellFormed = true
      rw [same.wellFormed]; exact vfR.valid
    · show (noopRetired step.state.frame).state.storage.lookup V = some vbuf
      rw [same.lookup]; exact vfR.vfound
    · show step.state.frame.rootWritable = _
      exact psR.writable
    · show step.state.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
      exact take
    · show step.state.frame.state.storage.work = _
      exact vfR.work
    · rw [hTPB] at stRes
      exact stRes
    · rw [resWork]
      have hw := cbR.work
      omega
    · rw [hSPB] at spRes; exact spRes
    · rw [resPeak]
      rw [hTPB] at stRes
      rw [hSPB] at spRes
      have h6 : step.state.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
          ((callerP caller).length+130-caller.scalars.baseMemory) +
          max caller.frame.state.storage.peak caller.frame.state.liveSpace := by
        have := opR; rw [hSPB,hTPB] at this; exact this
      omega

end Proofs.CountCall
