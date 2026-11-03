import Proofs.InvPermLoop
import Proofs.Generated.SortUtil
import Proofs.DoublingCall

namespace Proofs.InvPermCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.FlatVectorStmt Proofs.InvPermFrame Proofs.InvPermMath Proofs.InvPermEval Proofs.InvPermLoop
open Proofs.CppState (Cell)

theorem body_eq : Proofs.SortUtilInstance.inv_perm_std_vector_int.body = invBody := rfl

theorem prepare_inv (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) :
    ∃ Sinit, prepare caller Proofs.SortUtilInstance.inv_perm_std_vector_int.parameters [.vectorReference vslot] = some Sinit ∧
      Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[vbind V vsc]⟩ ∧
      Sinit.scalars.work = (caller.charge 1 1).scalars.work+2 ∧
      (caller.charge 1 1).scalars.peak ≤ Sinit.scalars.peak := by
  have rvec := resolve_vec caller ok
  have bound := bindRoot_v caller.frame.state caller.frame.rootWritable ok.valid ok.vtag ok.vfound ok.lengths ok.flag
  simp [prepare,ok.valid,resolveAll,rvec,Proofs.SortUtilInstance.inv_perm_std_vector_int]
  simp [bindAll,bindOne,bound,callerP,NState.observe,CppState.State.observe,vbind,atom]


theorem inv_fresh {D : NState} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF D.frame V vsc R sc L0 T0 vbuf b) (caller : Nat) (hscope : sc = caller+1) :
    ∀ owner, (D.frame.state.forest.transferred R caller (flatTag i32 sc)).context owner ≠ some sc := by
  intro owner h
  rw [context_transferred D.frame.state.forest R caller (flatTag i32 sc) fb.tag rfl owner] at h
  have rooted : D.frame.state.forest.rootOwner R = some R := CppVectorOwnership.root_runs _ R _ fb.tag rfl
  by_cases inTree : D.frame.state.forest.rootOwner owner = some R
  · simp [inTree] at h
    omega
  · simp [inTree] at h
    rcases fb.ctx owner sc h with lt | ⟨_,eq⟩
    · omega
    · subst eq; exact inTree rooted

theorem inv_moved_valid {D : NState} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF D.frame V vsc R sc L0 T0 vbuf b) (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred R caller (flatTag i32 sc))).state.wellFormed = true := by
  have := wellFormed_transferred D.frame.state R caller _ fb.tag rfl (by simp [flatTag])
  exact this.trans fb.valid

theorem inv_moved_live {D : NState} {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF D.frame V vsc R sc L0 T0 vbuf b) (caller : Nat) :
    (movedFrame D.frame (D.frame.state.forest.transferred R caller (flatTag i32 sc))).state.liveSpace =
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

theorem finish_inv (caller D : NState) {V vsc R sc L0 T0 : Nat} {vbuf b : Buffer Value}
    (fb : IF D.frame V vsc R sc L0 T0 vbuf b)
    (hscope : sc = caller.scope+1) (dscope : D.scope = sc) (cells : List Cell)
    (mem : D.scalars.memory = callerP caller ++ cells) :
    finish caller (D.charge 1 0) (.vector (.integer i32)) (some (.vector R (.integer i32))) =
      some (finishResult caller D (D.frame.state.forest.transferred R caller.scope (flatTag i32 sc)),
        .vector R (.integer i32)) := by
  have take : (D.scalars.memory.take caller.scalars.memory.length) = caller.scalars.memory := by
    rw [mem]
    simp only [callerP,List.append_assoc]
    exact List.take_left
  have transfer := Proofs.CppNestedVectorStore.transfer_valid_root D.frame.state R (.integer i32) sc caller.scope
    (flatTag i32 sc) fb.valid fb.tag rfl rfl rfl
  have fresh := retireScope_fresh (movedFrame D.frame (D.frame.state.forest.transferred R caller.scope
    (flatTag i32 sc))) sc (inv_moved_valid fb caller.scope) (inv_fresh fb caller.scope hscope)
  have scopeEq : (D.charge 1 0).scope = sc := dscope
  have chargeMem : (D.charge 1 0).scalars.memory = D.scalars.memory := rfl
  have chargeFrame : (D.charge 1 0).frame = D.frame := rfl
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      List.map Cell.type (List.take caller.scalars.memory.length (D.charge 1 0).scalars.memory) =
        List.map Cell.type caller.scalars.memory := by
    rw [chargeMem,take]
    refine ⟨?_,rfl⟩
    rw [mem]; simp [callerP]
  have trf : (D.charge 1 0).frame.transferRoot R (.integer i32) sc caller.scope =
      some (movedFrame D.frame (D.frame.state.forest.transferred R caller.scope (flatTag i32 sc))) := by
    rw [chargeFrame]
    simp [Frame.transferRoot,transfer,movedFrame]
  unfold finish
  rw [if_pos cond]
  dsimp only
  rw [if_pos rfl]
  simp only [scopeEq,trf,Bind.bind,Option.bind,fresh]
  rfl


theorem peak_final2 (SPB TPB cp tp tsp live tst rsp rst : Nat) (h1 : tp ≤ SPB+TPB) (h2 : tsp ≤ SPB)
    (h3 : live ≤ SPB) (h4 : tst ≤ TPB) (h5 : rsp ≤ SPB) (h6 : rst ≤ TPB) :
    max (max cp (max tp (max tsp live + tst))) (rsp+rst) ≤ max cp (SPB+TPB) := by omega

structure InvPost (caller Sinit res : NState) (V : Nat) (vbuf : Buffer Value) (items : List Int) : Prop where
  valid : res.frame.state.wellFormed = true
  vKept : res.frame.state.storage.lookup V = some vbuf
  result : ∃ b, res.frame.state.storage.lookup caller.frame.state.storage.objects.length = some b ∧
    b.items = (pinv items items.length items.length).map Value.integer ∧ b.capacity = items.length
  rootScope : res.frame.state.forest.context caller.frame.state.storage.objects.length = some caller.scope
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = caller.scalars.memory
  rootFlag : res.frame.rootWritable[caller.frame.state.storage.objects.length]? = some true
  rwLength : res.frame.rootWritable.length = caller.frame.state.storage.objects.length+1
  storageWork : res.frame.state.storage.work = caller.frame.state.storage.work+items.length+1+items.length
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+items.length+3)
  scalarWork : res.scalars.work ≤ caller.scalars.work+320*items.length+600
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+300-caller.scalars.baseMemory)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+300-caller.scalars.baseMemory) +
    max caller.frame.state.storage.peak (caller.frame.state.liveSpace+items.length+3))

def mkFI (caller : NState) (V vsc : Nat) (items : List Int) (vbuf : Buffer Value) (SPB TPB : Nat) : Fixed :=
  ⟨callerP caller,caller.scalars.baseMemory,0,items.length,0,V,vsc,caller.frame.state.storage.objects.length,
    caller.scope+1,caller.frame.rootWritable,items,vbuf,SPB,TPB⟩

set_option maxHeartbeats 4000000 in
theorem inv_perm_correct (caller : NState) {vslot vb V vsc : Nat} {wV m : Bool} {vbuf : Buffer Value}
    (ok : CallerOK caller vslot vb V vsc wV m vbuf) (items : List Int)
    (hv : vbuf.items = items.map Value.integer) (hn : items.length < 2147483648)
    (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k) :
    ∃ Sinit fuel res, prepare caller Proofs.SortUtilInstance.inv_perm_std_vector_int.parameters [.vectorReference vslot] =
        some Sinit ∧
      Proofs.SortUtilInstance.inv_perm_std_vector_int.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.vector caller.frame.state.storage.objects.length (.integer i32)) ∧
      InvPost caller Sinit res V vbuf items := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_inv caller ok
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [vbind V vsc] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+300-caller.scalars.baseMemory) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+items.length+3) := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    have := ok.base
    omega
  have hvn : vbuf.items.length = items.length := by rw [hv]; simp
  have bound : V < caller.frame.state.storage.objects.length :=
    CppVectorStore.lookup_bound caller.frame.state.storage V vbuf ok.vfound
  have sPk : Sinit.frame.state.storage.peak = caller.frame.state.storage.peak := by rw [sState]
  have ps : PS (mkFI caller V vsc items vbuf SPB TPB) (caller.scope+1) caller.frame.rootWritable Sinit [] []
      [.vector 0] := ⟨sSlots,by rw [sMem]; simp [mkFI],by rw [sBind],sBase,sScope,sFb,sRw⟩
  have vf : VF (mkFI caller V vsc items vbuf SPB TPB) caller.frame.state.liveSpace
      caller.frame.state.storage.work Sinit.frame := by
    refine ⟨by rw [sState]; exact ok.valid,by rw [sState]; exact ok.vtag,by rw [sState]; exact ok.vfound,
      by rw [sState,sRw]; exact ok.lengths,by rw [sRw]; exact ⟨m,ok.flag⟩,?_,by rw [sState],by rw [sState],
      by rw [sState]; rfl⟩
    intro owner c h
    rw [sState] at h
    have := ok.strict owner c h
    show c < caller.scope+1
    omega
  have cb : Cb (mkFI caller V vsc items vbuf SPB TPB) Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sPk]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := inv_body (F := mkFI caller V vsc items vbuf SPB TPB) (items := items) (W := Sinit.scalars.work)
    (S := Sinit) hv hvn hn bound sScope hrange hinj ps vf cb
    (by show (callerP caller).length-caller.scalars.baseMemory+300 ≤ SPB; rw [hSPB]; omega) hB
    (by show caller.frame.state.liveSpace+items.length+3 ≤ TPB; rw [hTPB]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,D,b,stepEq,ptR,fbR,hb,hc,cbR⟩ := run
  have objN : Sinit.frame.state.storage.objects.length = caller.frame.state.storage.objects.length := by rw [sState]
  have fin : finish caller (D.charge 1 0) (.vector (.integer i32))
      (some (.vector caller.frame.state.storage.objects.length (.integer i32))) =
      some (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1))),
        .vector caller.frame.state.storage.objects.length (.integer i32)) :=
    finish_inv caller D fbR rfl ptR.scope (cellsN items.length) ptR.memory
  have ret' : step.returned = some (.vector caller.frame.state.storage.objects.length (.integer i32)) := ret
  refine ⟨Sinit,fuel,finishResult caller D (D.frame.state.forest.transferred
    caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1))),hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel Proofs.SortUtilInstance.inv_perm_std_vector_int.body Sinit = .finished step := hrun
    have res : Proofs.SortUtilInstance.inv_perm_std_vector_int.result = ResultKind.vector (.integer i32) := rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,ret',stepEq,fin]
    simp
  · have forestLen : caller.frame.state.forest.objects.length = caller.frame.state.storage.objects.length :=
      (wellFormed_parts _ ok.valid).1
    have memD : D.scalars.memory = callerP caller ++ cellsN items.length := ptR.memory
    have take : D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [memD]; simp only [callerP,List.append_assoc]; exact List.take_left
    have liveD : liveS D = (callerP caller).length+1-caller.scalars.baseMemory+1 := by
      rw [ptR.live_eq]; simp [cellsN,bindsN,mkFI]
    have rooted : D.frame.state.forest.rootOwner caller.frame.state.storage.objects.length =
        some caller.frame.state.storage.objects.length := CppVectorOwnership.root_runs _ _ _ fbR.tag rfl
    have same := noopRetired_same (movedFrame D.frame (D.frame.state.forest.transferred
      caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1))))
    have hl : ∀ o, (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).frame.state.storage.lookup o
        = D.frame.state.storage.lookup o := fun o => same.lookup o
    have st6 := cbR.storagePeak
    have sp6 := cbR.scalarPeak
    have op6 := cbR.outerPeak
    have w6 := cbR.work
    have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have c0 : caller.scalars.peak ≤ (caller.charge 1 1).scalars.peak := by
        rw [charge_scalar_peak]; exact Nat.le_max_left _ _
      omega
    have livePost : D.frame.state.liveSpace = caller.frame.state.liveSpace+1+items.length := by
      rw [fbR.live,hc]
    have workPost : D.frame.state.storage.work = caller.frame.state.storage.work+items.length+1+items.length := fbR.work
    have resWork : (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).scalars.work =
        D.scalars.work+1+1 := rfl
    have resSp : (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).scalars.peak =
        max (max caller.scalars.peak (max D.scalars.peak
          (D.scalars.memory.length-D.scalars.baseMemory+D.scalars.bindings.length+0)))
          ((D.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
    have lenMem : D.scalars.memory.length = (callerP caller).length+1 := by rw [memD]; simp [cellsN]
    have bindD : D.scalars.bindings.length = 1 := by rw [ptR.bindings]; simp [bindsN]
    have baseD : D.scalars.baseMemory = caller.scalars.baseMemory := ptR.base
    have takeLen : (D.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      rw [take]
    have lenP : (callerP caller).length = caller.scalars.memory.length+
        (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
    have hbm := ok.base
    have spRes : (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).scalars.peak ≤ SPB := by
      rw [resSp,lenMem,bindD,baseD,takeLen]
      have h1 : D.scalars.peak ≤ SPB := sp6
      have h2 : caller.scalars.peak ≤ SPB := by rw [hSPB]; omega
      have h3 : (callerP caller).length+1-caller.scalars.baseMemory+1+0 ≤ SPB := by rw [hSPB]; omega
      have h4 : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
        rw [hSPB]; omega
      omega
    have stRes : (finishResult caller D (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).frame.state.storage.peak
        ≤ TPB := by
      have ml : (movedFrame D.frame (D.frame.state.forest.transferred caller.frame.state.storage.objects.length
          caller.scope (flatTag i32 (caller.scope+1)))).state.liveSpace = D.frame.state.liveSpace :=
        inv_moved_live fbR caller.scope
      show max D.frame.state.storage.peak ((movedFrame D.frame (D.frame.state.forest.transferred
        caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).state.liveSpace
          - D.frame.state.storage.baseSpace) ≤ TPB
      rw [ml,livePost]
      have : TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+items.length+3) := hTPB
      have h5 : D.frame.state.storage.peak ≤ TPB := st6
      omega
    refine ⟨?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact same.wellFormed.trans (inv_moved_valid fbR caller.scope)
    · show (noopRetired (movedFrame D.frame _)).state.storage.lookup V = some vbuf
      rw [same.lookup]; exact fbR.vfound
    · exact ⟨b,by rw [hl]; exact fbR.found,hb,hc⟩
    · show (D.frame.state.forest.transferred caller.frame.state.storage.objects.length caller.scope
        (flatTag i32 (caller.scope+1))).context caller.frame.state.storage.objects.length = _
      rw [context_transferred D.frame.state.forest caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)) fbR.tag rfl _]
      simp [rooted]
    · show D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory
      exact take
    · exact fbR.flag
    · show D.frame.rootWritable.length = _
      have a1 := fbR.lengths
      have wf := (wellFormed_parts _ fbR.valid).1
      have cnt : D.frame.state.storage.objects.length = caller.frame.state.storage.objects.length+1 := fbR.count
      omega
    · show D.frame.state.storage.work = _
      exact workPost
    · rw [hTPB] at stRes
      exact stRes
    · rw [resWork]
      have hw : Sinit.scalars.work = caller.scalars.work+3 := by rw [sWork]; rfl
      omega
    · rw [hSPB] at spRes; exact spRes
    · have resPeak : (finishResult caller D (D.frame.state.forest.transferred
          caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).peak =
          max (max caller.peak (D.charge 1 0).peak)
            ((finishResult caller D (D.frame.state.forest.transferred
              caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).scalars.peak +
            (finishResult caller D (D.frame.state.forest.transferred
              caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).frame.state.storage.peak) := rfl
      have chP := charge_peak D 1 0
      have hT' : max caller.frame.state.storage.peak (caller.frame.state.liveSpace+items.length+3) = TPB := hTPB.symm
      have hS' : max (max Sinit.scalars.peak Sinit.peak)
          ((callerP caller).length+300-caller.scalars.baseMemory) = SPB := hSPB.symm
      have liveD' : D.scalars.memory.length-D.scalars.baseMemory+D.scalars.bindings.length+0 ≤ SPB := by
        rw [lenMem,bindD,baseD,hSPB]; omega
      have key : (finishResult caller D (D.frame.state.forest.transferred
          caller.frame.state.storage.objects.length caller.scope (flatTag i32 (caller.scope+1)))).peak
          ≤ max caller.peak (SPB+TPB) := by
        refine le_of_eq_of_le resPeak ?_
        refine le_of_eq_of_le (congrArg (fun x => max (max caller.peak x) _) chP) ?_
        exact peak_final2 SPB TPB _ _ _ _ _ _ _ op6 sp6 liveD' st6 spRes stRes
      rw [← hS', ← hT'] at key
      exact key


-- The returned array is the inverse permutation: position `j` is stored at index `items[j]`,
-- and an index that no entry points to keeps -1.
theorem inv_perm_spec (items : List Int)
    (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < items.length)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k) :
    (∀ (j : Nat) (x : Int), items[j]? = some x → (pinv items items.length items.length)[x.toNat]? = some (j : Int)) ∧
    (∀ p, p < items.length → (∀ (j : Nat) (y : Int), items[j]? = some y → y.toNat ≠ p) →
      (pinv items items.length items.length)[p]? = some (-1)) :=
  ⟨fun j x item => pinv_written items items.length hrange hinj items.length (Nat.le_refl _) j x
      ((List.getElem?_eq_some_iff.mp item).1) item,
   fun p hp avoid => pinv_untouched items items.length hrange items.length (Nat.le_refl _) p hp
      (fun j x _ item => avoid j x item)⟩

end Proofs.InvPermCall
