import Proofs.QuotientBuild
import Proofs.Generated.EnumerateQuotients
import Proofs.DoublingCall

namespace Proofs.QuotientCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.QuotientBuild Proofs.EnumerateQuotientsMath
open Proofs.CppState (Cell)

theorem body_eq : Proofs.EnumerateQuotientsInstance.enumerate_quotients.body = qbody := rfl

theorem prepare_quot_int (caller : NState) (nExpr : NExpr) (v : Int) (hs : nExpr.scalarOnly = true)
    (ty : nExpr.resultType = u64) (value : nExpr.denote (envOf caller) = some v)
    (valid : caller.frame.state.wellFormed = true) (nv : u64.valid v = true) :
    ∃ t, Good caller t nExpr.nodes nExpr.nodes ∧
      ∃ Sinit, prepare caller Proofs.EnumerateQuotientsInstance.enumerate_quotients.parameters [.value nExpr] =
        some Sinit ∧ Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u64,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t,ran,good⟩ := scalar_eval nExpr caller v hs value
  refine ⟨t,good,?_⟩
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have res : resolve caller (.scalar u64 false true) (.value nExpr) = some (t,.scalar u64 true v) := by
    simp [resolve,ty,ran]
  have hparams : Proofs.EnumerateQuotientsInstance.enumerate_quotients.parameters =
      [.scalar u64 false true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,
    NState.observe,CppState.State.observe]
  exact Nat.le_max_left _ _

theorem prepare_quot (caller : NState) (nExpr : NExpr) (n : Nat) (hs : nExpr.scalarOnly = true)
    (ty : nExpr.resultType = u64) (value : nExpr.denote (envOf caller) = some (n : Int))
    (valid : caller.frame.state.wellFormed = true) (hn : n < 18446744073709551616) :
    ∃ t, Good caller t nExpr.nodes nExpr.nodes ∧
      ∃ Sinit, prepare caller Proofs.EnumerateQuotientsInstance.enumerate_quotients.parameters [.value nExpr] =
        some Sinit ∧ Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [qcell n] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ Sinit.scalars.peak :=
  prepare_quot_int caller nExpr (n : Int) hs ty value valid (u64_nat n hn)

theorem flat_fresh {D : NState} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB D.frame R sc L0 T0 b)
    (caller : Nat) (hscope : sc = caller+1) :
    ∀ owner, (D.frame.state.forest.transferred R caller (flatTag u64 sc)).context owner ≠ some sc := by
  intro owner h
  rw [context_transferred D.frame.state.forest R caller (flatTag u64 sc) fb.tag rfl owner] at h
  have rooted : D.frame.state.forest.rootOwner R = some R := CppVectorOwnership.root_runs _ R _ fb.tag rfl
  by_cases inTree : D.frame.state.forest.rootOwner owner = some R
  · simp [inTree] at h
    omega
  · simp [inTree] at h
    rcases fb.ctx owner sc h with lt | ⟨_,eq⟩
    · omega
    · subst eq; exact inTree rooted

theorem moved_valid_flat {D : NState} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB D.frame R sc L0 T0 b)
    (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred R caller (flatTag u64 sc))).state.wellFormed = true := by
  have := wellFormed_transferred D.frame.state R caller _ fb.tag rfl (by simp [flatTag])
  exact this.trans fb.valid

theorem finish_quot (caller D : NState) {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB D.frame R sc L0 T0 b)
    (hscope : sc = caller.scope+1) (dscope : D.scope = sc) (cells : List Cell)
    (mem : D.scalars.memory = callerP caller ++ cells) :
    finish caller (D.charge 1 0) (.vector (.integer u64)) (some (.vector R (.integer u64))) =
      some (finishResult caller D (D.frame.state.forest.transferred R caller.scope (flatTag u64 sc)),
        .vector R (.integer u64)) := by
  have take : (D.scalars.memory.take caller.scalars.memory.length) = caller.scalars.memory := by
    rw [mem]
    simp only [callerP,List.append_assoc]
    exact List.take_left
  have transfer := Proofs.CppNestedVectorStore.transfer_valid_root D.frame.state R (.integer u64) sc caller.scope
    (flatTag u64 sc) fb.valid fb.tag rfl rfl rfl
  have fresh := retireScope_fresh (movedFrame D.frame (D.frame.state.forest.transferred R caller.scope
    (flatTag u64 sc))) sc (moved_valid_flat fb caller.scope) (flat_fresh fb caller.scope hscope)
  have scopeEq : (D.charge 1 0).scope = sc := dscope
  have chargeMem : (D.charge 1 0).scalars.memory = D.scalars.memory := rfl
  have chargeFrame : (D.charge 1 0).frame = D.frame := rfl
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      List.map Cell.type (List.take caller.scalars.memory.length (D.charge 1 0).scalars.memory) =
        List.map Cell.type caller.scalars.memory := by
    rw [chargeMem,take]
    refine ⟨?_,rfl⟩
    rw [mem]; simp [callerP]
  have trf : (D.charge 1 0).frame.transferRoot R (.integer u64) sc caller.scope =
      some (movedFrame D.frame (D.frame.state.forest.transferred R caller.scope (flatTag u64 sc))) := by
    rw [chargeFrame]
    simp [Frame.transferRoot,transfer,movedFrame]
  unfold finish
  rw [if_pos cond]
  dsimp only
  rw [if_pos rfl]
  simp only [scopeEq,trf,Bind.bind,Option.bind,fresh]
  rfl

theorem moved_live_flat {D : NState} {R sc L0 T0 : Nat} {b : Buffer Value} (fb : FB D.frame R sc L0 T0 b)
    (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred R caller (flatTag u64 sc))).state.liveSpace =
      D.frame.state.liveSpace := by
  unfold State.liveSpace
  congr 1
  apply List.map_congr_left
  intro o _
  simp only [movedFrame,State.nodeSpace]
  by_cases same : o = R
  · subst same
    rw [transferred_lookup_root D.frame.state.forest o caller _ fb.tag,fb.tag]
    cases D.frame.state.storage.lookup o <;> rfl
  · rw [transferred_lookup_other D.frame.state.forest R o caller _ same]

theorem peak_final (SPB TPB cp tp tsp live tst rsp rst : Nat) (h1 : tp ≤ SPB+TPB) (h2 : tsp ≤ SPB)
    (h3 : live ≤ SPB) (h4 : tst ≤ TPB) (h5 : rsp ≤ SPB) (h6 : rst ≤ TPB) :
    max (max cp (max tp (max tsp live + tst))) (rsp+rst) ≤ max cp (SPB+TPB) := by omega

structure QPost (caller Sinit res : NState) (kn n K : Nat) : Prop where
  valid : res.frame.state.wellFormed = true
  items : ∃ b, res.frame.state.storage.lookup caller.frame.state.storage.objects.length = some b ∧
    b.items = vals (qlist n K) ∧ b.capacity = n/K+K-1
  rootScope : res.frame.state.forest.context caller.frame.state.storage.objects.length = some caller.scope
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  rootFlag : res.frame.rootWritable[caller.frame.state.storage.objects.length]? = some true
  rwLength : res.frame.rootWritable.length = caller.frame.state.storage.objects.length+1
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work+1+1+2*(n/K)+2*(K-1)
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+(n/K+K-1)+3)
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+40*(n/K+K-1)+2410
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+40)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+12-caller.scalars.baseMemory+40) +
    max caller.frame.state.storage.peak (caller.frame.state.liveSpace+(n/K+K-1)+3))

set_option maxHeartbeats 2000000 in
theorem quotients_correct (caller : NState) (nExpr : NExpr) (n : Nat) (hs : nExpr.scalarOnly = true)
    (ty : nExpr.resultType = u64) (value : nExpr.denote (envOf caller) = some (n : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hn : n < 18446744073709551616) :
    ∃ K, 1 ≤ K ∧ K ≤ 4294967296 ∧ n ≤ K*(K+1) ∧ (K = 1 ∨ (K-1)*K < n) ∧
      ∃ Sinit fuel res, prepare caller Proofs.EnumerateQuotientsInstance.enumerate_quotients.parameters
          [.value nExpr] = some Sinit ∧
        Proofs.EnumerateQuotientsInstance.enumerate_quotients.callFuel fuel caller [.value nExpr] =
          .finished (res,.vector caller.frame.state.storage.objects.length (.integer u64)) ∧
        QPost caller Sinit res nExpr.nodes n K := by
  obtain ⟨K,hK1,hKs,hKn,hKm⟩ := exists_K n hn
  refine ⟨K,hK1,hKs,hKn,hKm,?_⟩
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_quot caller nExpr n hs ty value valid hn
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+40) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max Sinit.frame.state.storage.peak
    (caller.frame.state.liveSpace+(n/K+K-1)+3) := ⟨_,rfl⟩
  have qs : QS Sinit (callerP caller) caller.scalars.baseMemory (caller.scope+1) [qcell n] [⟨(callerP caller).length,true⟩] [.scalar 0] :=
    ⟨sSlots,sMem,sBind,sBase,sScope⟩
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
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have spb : (callerP caller).length+12-caller.scalars.baseMemory+40 ≤ SPB := by rw [hSPB]; omega
  have hspace : caller.frame.state.liveSpace+(n/K+K-1)+3 ≤ TPB := by rw [hTPB]; omega
  have run := qbody_run (K := K) Sinit qs fa sFb cq hB spb hn hK1 hKs hKn hKm hspace
  obtain ⟨fuel,step,hrun,ret,brk,t6,b,stepEq,qs6,fb6,items6,cap6,cq6⟩ := run
  have objN : Sinit.frame.state.storage.objects.length = caller.frame.state.storage.objects.length := by
    rw [sState]
  have fin := finish_quot caller t6 fb6 rfl qs6.scope _ qs6.memory
  rw [objN] at ret fin fb6
  refine ⟨Sinit,fuel,finishResult caller t6 (t6.frame.state.forest.transferred
    caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1))),hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel Proofs.EnumerateQuotientsInstance.enumerate_quotients.body Sinit =
        .finished step := hrun
    have res : Proofs.EnumerateQuotientsInstance.enumerate_quotients.result = ResultKind.vector (.integer u64) := rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,stepEq,ret,fin]
    simp
  · have forestLen : caller.frame.state.forest.objects.length = caller.frame.state.storage.objects.length :=
      (wellFormed_parts _ valid).1
    have memT : t6.scalars.memory = callerP caller ++ cellsQ4 n K (K-1) (n/K) := qs6.memory
    have take : t6.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [memT]; simp only [callerP,List.append_assoc]; exact List.take_left
    have liveT : liveS t6 = (callerP caller).length+4-caller.scalars.baseMemory+4 := by
      rw [qs6.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
    have rooted : t6.frame.state.forest.rootOwner caller.frame.state.storage.objects.length =
        some caller.frame.state.storage.objects.length := CppVectorOwnership.root_runs _ _ _ fb6.tag rfl
    have same := noopRetired_same (movedFrame t6.frame (t6.frame.state.forest.transferred
      caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1))))
    have hl : ∀ o, (finishResult caller t6 (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).frame.state.storage.lookup o
        = t6.frame.state.storage.lookup o := fun o => same.lookup o
    have eS : (fx SPB TPB).SPB = SPB := rfl
    have eT : (fx SPB TPB).TPB = TPB := rfl
    have st6 := cq6.storagePeak
    have sp6 := cq6.scalarPeak
    have op6 := cq6.outerPeak
    have w6 := cq6.work
    have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have := good.2.2.2.2.1
      have := sPeak
      omega
    have gw := good.2.2.1
    have livePost : t6.frame.state.liveSpace = caller.frame.state.liveSpace+1+(n/K+K-1) := by
      rw [fb6.live,cap6]
    have workPost : t6.frame.state.storage.work =
        caller.frame.state.storage.work+1+1+2*(n/K)+2*(K-1) := fb6.work
    have resWork : (finishResult caller t6 (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).scalars.work =
        t6.scalars.work+1+1 := rfl
    have resSp : (finishResult caller t6 (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).scalars.peak =
        max (max caller.scalars.peak (max t6.scalars.peak
          (t6.scalars.memory.length-t6.scalars.baseMemory+t6.scalars.bindings.length+0)))
          ((t6.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
    have lenMem : t6.scalars.memory.length = (callerP caller).length+4 := by rw [memT]; simp [cellsQ4,cellsQ3]
    have bindT : t6.scalars.bindings.length = 4 := by rw [qs6.bindings]; simp [bindsQ4,bindsQ3]
    have baseT : t6.scalars.baseMemory = caller.scalars.baseMemory := qs6.base
    have takeLen : (t6.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      rw [take]
    have lenP : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    have spRes : (finishResult caller t6 (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).scalars.peak ≤ SPB := by
      rw [resSp,lenMem,bindT,baseT,takeLen]
      omega
    have stRes : (finishResult caller t6 (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).frame.state.storage.peak
        ≤ TPB := by
      have ml := moved_live_flat fb6 caller.scope
      show max t6.frame.state.storage.peak ((movedFrame t6.frame (t6.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).state.liveSpace
          - t6.frame.state.storage.baseSpace) ≤ TPB
      rw [ml,livePost]
      omega
    refine ⟨?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact same.wellFormed.trans (moved_valid_flat fb6 caller.scope)
    · exact ⟨b,by rw [hl]; exact fb6.found,items6,cap6⟩
    · show (t6.frame.state.forest.transferred caller.frame.state.storage.objects.length caller.scope
        (flatTag u64 (caller.scope+1))).context caller.frame.state.storage.objects.length = _
      rw [context_transferred t6.frame.state.forest _ caller.scope _ fb6.tag rfl _]
      simp [rooted]
    · show t6.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
      exact take
    · exact fb6.flag
    · show t6.frame.rootWritable.length = _
      have := fb6.lengths
      have wf := (wellFormed_parts _ fb6.valid).1
      have := fb6.count
      omega
    · show t6.frame.state.storage.work = _
      exact workPost
    · have : (hTPB ▸ stRes) = stRes := rfl
      rw [hTPB] at stRes
      have e : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
      rw [e] at stRes
      exact stRes
    · rw [resWork]
      have hw : Sinit.scalars.work ≤ caller.scalars.work + nExpr.nodes + 2 := by
        have := sWork; omega
      omega
    · rw [hSPB] at spRes; exact spRes
    · have resPeak : (finishResult caller t6 (t6.frame.state.forest.transferred
          caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).peak =
          max (max caller.peak (t6.charge 1 0).peak)
            ((finishResult caller t6 (t6.frame.state.forest.transferred
              caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).scalars.peak +
            (finishResult caller t6 (t6.frame.state.forest.transferred
              caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).frame.state.storage.peak) := rfl
      have chP := charge_peak t6 1 0
      have e : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
      have hT' : max caller.frame.state.storage.peak (caller.frame.state.liveSpace+(n/K+K-1)+3) = TPB := by
        rw [hTPB,e]
      have hS' : max (max Sinit.scalars.peak Sinit.peak)
          ((callerP caller).length+12-caller.scalars.baseMemory+40) = SPB := hSPB.symm
      have liveT' : t6.scalars.memory.length-t6.scalars.baseMemory+t6.scalars.bindings.length+0 ≤ SPB := by
        rw [lenMem,bindT,baseT]; omega
      have key : (finishResult caller t6 (t6.frame.state.forest.transferred
          caller.frame.state.storage.objects.length caller.scope (flatTag u64 (caller.scope+1)))).peak
          ≤ max caller.peak (SPB+TPB) := by
        refine le_of_eq_of_le resPeak ?_
        refine le_of_eq_of_le (congrArg (fun x => max (max caller.peak x) _) chP) ?_
        exact peak_final SPB TPB _ _ _ _ _ _ _ op6 sp6 liveT' st6 spRes stRes
      rw [← hS', ← hT'] at key
      exact key

end Proofs.QuotientCall
