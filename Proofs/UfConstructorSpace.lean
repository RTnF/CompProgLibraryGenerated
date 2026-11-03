import Proofs.UfPreparePeak
import Proofs.CppConstructionSpace
import Proofs.UfConstructionWork

namespace Proofs.UfConstructorSpace
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedEval
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.MultiVecDynamic
open Proofs.UfConstructionStage Proofs.CppConstructionFootprint Proofs.UfConstructionFootprint
open Proofs.CppConstructorWork Proofs.CppConstructorPeak
open Proofs.CppRootModel Proofs.UfConstructionExport Proofs.CppConstructorFinish
open Proofs.UfBalancedReceiver (Strong)
open Proofs.DoublingNested (i32)
open Proofs.UfConstructionWork (profile_vector)

theorem finish_scalar_fields (caller callee out : NState) (vslot : Nat) (element : Proofs.CppVectorOwnership.Element)
    (fieldList : List ScalarField) (values : List ScalarValue) (object : ObjectRef)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (captured : captureAll callee fieldList = some values)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fieldList = some (out,object)) :
    out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (liveS caller+2*values.length) ∧
      out.frame.bindings.length = caller.frame.bindings.length+1 := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · rename_i guarded
    obtain ⟨index,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    split at rest
    · obtain ⟨actualValues,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have valuesEq : actualValues = values := Option.some.inj (found.symm.trans captured)
      subst actualValues
      obtain ⟨moved,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have eq := (Prod.mk.inj (Option.some.inj same)).1
      subst out
      constructor
      · have live := restored_live caller callee retired binding values guarded.2.1 baseline
        simp only [restored,NState.observe,Proofs.CppState.State.observe,liveS,
          List.length_append,List.length_take,List.length_map,scalarBindings_length,Nat.min_eq_left guarded.2.1] at live ⊢
        omega
      · simp only [restored,NState.observe,List.length_append,List.length_cons,List.length_nil]
    · simp at rest
  · simp at actual

theorem export_storage_components (caller callee out : NState) (h : ContentsHeap) (vec : List Int) (count n : Int)
    (hasArgument : Bool) (_cv : i32.valid count = true) (_nv : i32.valid n = true)
    (valid : caller.frame.state.wellFormed = true)
    (strict : ∀ owner k, caller.frame.state.forest.context owner = some k → k ≤ caller.scope)
    (real : Realizes (profile caller h vec count n hasArgument) callee)
    (forest : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1))
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (objects : callee.frame.state.storage.objects = caller.frame.state.storage.objects++[some buffer])
    (actual : Proofs.CppConstructorFinish.finish caller callee (vectorField hasArgument) (.integer i32)
      (fields hasArgument) = some (out,reference caller 2)) :
    out.frame.state.liveSpace = caller.frame.state.liveSpace+buffer.capacity+1 ∧
    out.frame.state.storage.peak = max callee.frame.state.storage.peak
      (caller.frame.state.liveSpace+buffer.capacity+1-callee.frame.state.storage.baseSpace) ∧
      out.frame.state.storage.baseSpace = callee.frame.state.storage.baseSpace := by
  obtain ⟨slot,binding,model⟩ := profile_vector caller callee h vec count n hasArgument real
  have scopeEq : callee.scope = caller.scope+1 := real.scopedState
  obtain ⟨frame,_,_⟩ := Proofs.CppConstructionRetire.finish_frame caller callee out (vectorField hasArgument)
    0 (.integer i32) (fields hasArgument) (reference caller 2) _ (.flat i32 (caller.scope+1) vec)
    slot binding model rfl scopeEq.symm actual
  let moved := Proofs.DynamicTransfer.movedFrame callee.frame caller.frame.state.storage.objects.length caller.scope
    (.flat i32 (caller.scope+1) vec)
  have lengths := (Proofs.CppNestedVectorStore.wellFormed_parts caller.frame.state valid).1
  have movedForest : moved.state.forest = caller.frame.state.forest.declareRoot i32 caller.scope := by
    change (callee.frame.state.forest.transferred caller.frame.state.storage.objects.length caller.scope
      (Proofs.CppNestedConstruct.flatTag i32 (caller.scope+1))) = _
    rw [forest,← lengths,declared_transferred]
  have fresh : ∀ owner, moved.state.forest.context owner ≠ some callee.scope := by
    intro owner found
    rw [movedForest] at found
    have bound := declared_scope_bound caller.frame.state.forest i32 caller.scope strict owner callee.scope found
    rw [scopeEq] at bound
    omega
  have retired := Proofs.CppNestedScope.retired_fresh moved.state callee.scope fresh
  have movedObjects : moved.state.storage.objects = caller.frame.state.storage.objects++[some buffer] := objects
  have live := Proofs.CppConstructionSpace.appended_root_live caller.frame.state moved.state i32 caller.scope buffer
    lengths movedForest movedObjects
  rw [frame,retired]
  constructor
  · change moved.state.liveSpace = _
    exact live
  · constructor
    · change max moved.state.storage.peak (moved.state.liveSpace-moved.state.storage.baseSpace) = _
      rw [live]
      rfl
    · rfl

theorem construct_sized_components (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
      (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) ∧
      out.work ≤ caller.work+en.nodes+n+30 ∧ liveS out = liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+n+1 ∧
      out.peak ≤ max caller.peak (max caller.scalars.peak
        (liveS caller+caller.frame.bindings.length+en.nodes+12)+
        max caller.frame.state.storage.peak (caller.frame.state.liveSpace+(n+2)-caller.frame.state.storage.baseSpace)) ∧
      out.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+en.nodes+12) ∧
      out.frame.state.storage.peak ≤ max caller.frame.state.storage.peak (caller.frame.state.liveSpace+(n+2)-caller.frame.state.storage.baseSpace) ∧
      out.frame.state.storage.baseSpace = caller.frame.state.storage.baseSpace ∧
      out.frame.bindings.length = caller.frame.bindings.length+1 := by
  obtain ⟨init,prepared,locals,initFrame,initScope,initBase,initLive,initScalar,initPeak⟩ :=
    Proofs.UfPreparePeak.prepare_sized_peak caller valid base en n scalar type value (nat_i32 n small)
  have real := Proofs.UfConstructionPrepare.sized_real caller init heap valid models lengths n locals initFrame initScope
  obtain ⟨callee,ran,after,frame,_,_,_,stageScalar,stagePeak⟩ :=
    Proofs.UfConstructionPeak.sized_stage_peak _ _ _ _ _ _ n small init real
  have profileReal : Realizes (profile caller (eraseHeap heap) (List.replicate n (-1)) n n true) callee := after
  obtain ⟨out,finished,initialized⟩ := export_fields caller callee (eraseHeap heap) (List.replicate n (-1)) n n true
    (nat_i32 n small) (nat_i32 n small) profileReal
  have forestEq : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1) := by
    rw [frame,initFrame,initScope]; rfl
  let buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value :=
    ⟨caller.frame.state.storage.objects.length,List.replicate n (.integer (-1)),n,Proofs.CppVectorBindings.sizeLimit i32,0⟩
  have objects : callee.frame.state.storage.objects = caller.frame.state.storage.objects++[some buffer] := by
    rw [frame,initFrame]; rfl
  obtain ⟨liveSpace,endStorage,endBase⟩ := export_storage_components caller callee out (eraseHeap heap) (List.replicate n (-1)) n n true
    (nat_i32 n small) (nat_i32 n small) valid strict profileReal forestEq buffer objects finished
  have captured := captureAll_ok callee (fields true) (payload n n)
    (fields_match callee _ n n true (nat_i32 n small) (nat_i32 n small) profileReal.data.locals)
  have scalarFields := finish_scalar_fields caller callee out (vectorField true) (.integer i32) (fields true)
    (payload n n) (reference caller 2) base captured finished
  simp only [payload,List.length_cons,List.length_nil] at scalarFields
  have endPeak := finish_peak caller callee out (vectorField true) (.integer i32) (fields true)
    (payload n n) (reference caller 2) base captured finished
  have endLive := Proofs.CppConstructionSpace.finish_live caller callee out (vectorField true) (.integer i32)
    (fields true) (payload n n) (reference caller 2) base captured finished
  simp only [payload,List.length_cons,List.length_nil] at endPeak endLive
  let K := liveS caller+caller.frame.bindings.length+en.nodes+12
  let V := max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+(n+2)-caller.frame.state.storage.baseSpace)
  have storage : callee.frame.state.storage.peak = V := by rw [frame,initFrame]; rfl
  have storageBase : callee.frame.state.storage.baseSpace = caller.frame.state.storage.baseSpace := by rw [frame,initFrame]; rfl
  have oldStorage : init.frame.state.storage.peak ≤ V := by rw [initFrame]; exact Nat.le_max_left _ _
  have initScalarK : init.scalars.peak ≤ max caller.scalars.peak K :=
    initScalar.trans (max_le_max (Nat.le_refl _) (by dsimp [K]; omega))
  have calleeScalar : callee.scalars.peak ≤ max caller.scalars.peak K :=
    stageScalar.trans (max_le initScalarK ((by dsimp [K]; omega : liveS init+7 ≤ K).trans (Nat.le_max_right _ _)))
  have initPeakK : init.peak ≤ max caller.peak (max caller.scalars.peak K+V) := by
    apply initPeak.trans
    apply max_le_max (Nat.le_refl _)
    exact Nat.add_le_add (max_le_max (Nat.le_refl _) (by dsimp [K]; omega))
      (by dsimp [V]; exact Nat.le_max_left _ _)
  have stageStorage : max init.frame.state.storage.peak
      (init.frame.state.liveSpace+(n+2)-init.frame.state.storage.baseSpace) = V := by rw [initFrame]
  rw [stageStorage] at stagePeak
  have calleePeak : callee.peak ≤ max caller.peak (max caller.scalars.peak K+V) :=
    stagePeak.trans (max_le initPeakK ((Nat.add_le_add_right
      (max_le initScalarK ((by dsimp [K]; omega : liveS init+10 ≤ K).trans (Nat.le_max_right _ _))) V).trans
        (Nat.le_max_right _ _)))
  have outStorage : out.frame.state.storage.peak ≤ V := by
    rw [endStorage,storage,storageBase]
    apply max_le (Nat.le_refl _)
    exact (Nat.sub_le_sub_right (by dsimp [buffer]; omega) _).trans (Nat.le_max_right _ _)
  have outScalar : out.scalars.peak ≤ max caller.scalars.peak K := by
    rw [scalarFields.1]
    apply max_le (max_le (Nat.le_max_left _ _) calleeScalar)
    exact (by dsimp [K]; omega : liveS caller+2*(1+(1+0)) ≤ K).trans (Nat.le_max_right _ _)
  have outPeak : out.peak ≤ max caller.peak (max caller.scalars.peak K+V) := by
    rw [endPeak]
    apply max_le (max_le (Nat.le_max_left _ _) calleePeak)
    apply le_trans (Nat.add_le_add ?_ outStorage) (Nat.le_max_right _ _)
    apply max_le (max_le (Nat.le_max_left _ _) calleeScalar)
    exact (by dsimp [K]; omega : liveS caller+2*(1+(1+0)) ≤ K).trans (Nat.le_max_right _ _)
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct1 8 caller init callee out
    [.value en] (vectorField true) (.integer i32) (fields true) (reference caller 2) rfl prepared ran finished
  obtain ⟨other,otherRun,strong,work⟩ := Proofs.UfConstructionWork.construct_sized_work caller heap valid models lengths strict base en n small scalar type value
  have same : other = out := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans executed))
  rw [same] at strong work
  exact ⟨out,executed,strong,work,endLive,liveSpace,outPeak,outScalar,outStorage,endBase.trans storageBase,scalarFields.2⟩

theorem construct_default_components (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
 :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
      (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) [] 0 (fun _ => 0) ∧
      out.work ≤ caller.work+12 ∧ liveS out = liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+1 ∧
      out.peak ≤ max caller.peak (max caller.scalars.peak
        (liveS caller+caller.frame.bindings.length+6)+
        max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1-caller.frame.state.storage.baseSpace)) ∧
      out.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+6) ∧
      out.frame.state.storage.peak ≤ max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1-caller.frame.state.storage.baseSpace) ∧
      out.frame.state.storage.baseSpace = caller.frame.state.storage.baseSpace ∧
      out.frame.bindings.length = caller.frame.bindings.length+1 := by
  obtain ⟨init,prepared,locals,initFrame,initScope,initBase,initLive,initScalar,initPeak⟩ :=
    Proofs.UfPreparePeak.prepare_default_peak caller valid base
  have real := Proofs.UfConstructionPrepare.default_real caller init heap valid models lengths locals initFrame initScope
  obtain ⟨callee,ran,after,frame,_,_,_,stageScalar,stagePeak⟩ :=
    Proofs.UfConstructionPeak.default_stage_peak _ _ _ _ _ _ init real
  have profileReal : Realizes (profile caller (eraseHeap heap) [] 0 0 false) callee := after
  obtain ⟨out,finished,initialized⟩ := export_fields caller callee (eraseHeap heap) [] 0 0 false
    rfl rfl profileReal
  have forestEq : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1) := by
    rw [frame,initFrame,initScope]; rfl
  let buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value :=
    Proofs.CppNestedConstruct.flatBuffer i32 caller.frame.state.storage.objects.length
  have objects : callee.frame.state.storage.objects = caller.frame.state.storage.objects++[some buffer] := by
    rw [frame,initFrame]; rfl
  obtain ⟨liveSpace,endStorage,endBase⟩ := export_storage_components caller callee out (eraseHeap heap) [] 0 0 false
    rfl rfl valid strict profileReal forestEq buffer objects finished
  have captured := captureAll_ok callee (fields false) (payload 0 0)
    (fields_match callee _ 0 0 false rfl rfl profileReal.data.locals)
  have scalarFields := finish_scalar_fields caller callee out (vectorField false) (.integer i32) (fields false)
    (payload 0 0) (reference caller 2) base captured finished
  simp only [payload,List.length_cons,List.length_nil] at scalarFields
  have endPeak := finish_peak caller callee out (vectorField false) (.integer i32) (fields false)
    (payload 0 0) (reference caller 2) base captured finished
  have endLive := Proofs.CppConstructionSpace.finish_live caller callee out (vectorField false) (.integer i32)
    (fields false) (payload 0 0) (reference caller 2) base captured finished
  simp only [payload,List.length_cons,List.length_nil] at endPeak endLive
  let K := liveS caller+caller.frame.bindings.length+6
  let V := max caller.frame.state.storage.peak
    (caller.frame.state.liveSpace+1-caller.frame.state.storage.baseSpace)
  have storage : callee.frame.state.storage.peak = V := by rw [frame,initFrame]; rfl
  have storageBase : callee.frame.state.storage.baseSpace = caller.frame.state.storage.baseSpace := by rw [frame,initFrame]; rfl
  have oldStorage : init.frame.state.storage.peak ≤ V := by rw [initFrame]; exact Nat.le_max_left _ _
  have initScalarK : init.scalars.peak ≤ max caller.scalars.peak K :=
    (le_of_eq initScalar).trans (Nat.le_max_left _ _)
  have calleeScalar : callee.scalars.peak ≤ max caller.scalars.peak K :=
    stageScalar.trans (max_le initScalarK ((by dsimp [K]; omega : liveS init+5 ≤ K).trans (Nat.le_max_right _ _)))
  have initPeakK : init.peak ≤ max caller.peak (max caller.scalars.peak K+V) := by
    rw [initPeak]
    exact max_le_max (Nat.le_refl _) (Nat.add_le_add (Nat.le_max_left _ _) (by dsimp [V]; exact Nat.le_max_left _ _))
  have stageStorage : max init.frame.state.storage.peak
      (init.frame.state.liveSpace+1-init.frame.state.storage.baseSpace) = V := by rw [initFrame]
  rw [stageStorage] at stagePeak
  have calleePeak : callee.peak ≤ max caller.peak (max caller.scalars.peak K+V) :=
    stagePeak.trans (max_le initPeakK ((Nat.add_le_add_right
      (max_le initScalarK ((by dsimp [K]; omega : liveS init+6 ≤ K).trans (Nat.le_max_right _ _))) V).trans
        (Nat.le_max_right _ _)))
  have outStorage : out.frame.state.storage.peak ≤ V := by
    rw [endStorage,storage,storageBase]
    dsimp [buffer,Proofs.CppNestedConstruct.flatBuffer]
    exact max_le (Nat.le_refl _) (Nat.le_max_right _ _)
  have outScalar : out.scalars.peak ≤ max caller.scalars.peak K := by
    rw [scalarFields.1]
    apply max_le (max_le (Nat.le_max_left _ _) calleeScalar)
    exact (by dsimp [K]; omega : liveS caller+2*(1+(1+0)) ≤ K).trans (Nat.le_max_right _ _)
  have outPeak : out.peak ≤ max caller.peak (max caller.scalars.peak K+V) := by
    rw [endPeak]
    apply max_le (max_le (Nat.le_max_left _ _) calleePeak)
    apply le_trans (Nat.add_le_add ?_ outStorage) (Nat.le_max_right _ _)
    apply max_le (max_le (Nat.le_max_left _ _) calleeScalar)
    exact (by dsimp [K]; omega : liveS caller+2*(1+(1+0)) ≤ K).trans (Nat.le_max_right _ _)
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct0 8 caller init callee out
    [] (vectorField false) (.integer i32) (fields false) (reference caller 2) rfl prepared ran finished
  obtain ⟨other,otherRun,strong,work⟩ := Proofs.UfConstructionWork.construct_default_work caller heap valid models lengths strict base
  have same : other = out := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans executed))
  rw [same] at strong work
  exact ⟨out,executed,strong,work,endLive,by simpa [buffer,Proofs.CppNestedConstruct.flatBuffer] using liveSpace,outPeak,outScalar,outStorage,endBase.trans storageBase,scalarFields.2⟩


theorem export_storage (caller callee out : NState) (h : ContentsHeap) (vec : List Int) (count n : Int)
    (hasArgument : Bool) (_cv : i32.valid count = true) (_nv : i32.valid n = true)
    (valid : caller.frame.state.wellFormed = true)
    (strict : ∀ owner k, caller.frame.state.forest.context owner = some k → k ≤ caller.scope)
    (real : Realizes (profile caller h vec count n hasArgument) callee)
    (forest : callee.frame.state.forest = caller.frame.state.forest.declareRoot i32 (caller.scope+1))
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (objects : callee.frame.state.storage.objects = caller.frame.state.storage.objects++[some buffer])
    (actual : Proofs.CppConstructorFinish.finish caller callee (vectorField hasArgument) (.integer i32)
      (fields hasArgument) = some (out,reference caller 2)) :
    out.frame.state.liveSpace = caller.frame.state.liveSpace+buffer.capacity+1 ∧
    out.frame.state.storage.peak = max callee.frame.state.storage.peak
      (caller.frame.state.liveSpace+buffer.capacity+1-callee.frame.state.storage.baseSpace) := by
  obtain ⟨live,peak,_⟩ := export_storage_components caller callee out h vec count n hasArgument _cv _nv valid strict real forest buffer objects actual
  exact ⟨live,peak⟩

theorem construct_sized (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
      (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) ∧
      out.work ≤ caller.work+en.nodes+n+30 ∧ liveS out = liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+n+1 ∧
      out.peak ≤ max caller.peak (max caller.scalars.peak
        (liveS caller+caller.frame.bindings.length+en.nodes+12)+
        max caller.frame.state.storage.peak (caller.frame.state.liveSpace+(n+2)-caller.frame.state.storage.baseSpace)) := by
  obtain ⟨out,ran,strong,work,scalarLive,vectorLive,peak,_⟩ := construct_sized_components caller heap valid models lengths strict base en n small scalar type value
  exact ⟨out,ran,strong,work,scalarLive,vectorLive,peak⟩

theorem construct_default (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
 :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
      (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Strong out (Proofs.UfReceiverState.layoutOf caller) [] 0 (fun _ => 0) ∧
      out.work ≤ caller.work+12 ∧ liveS out = liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+1 ∧
      out.peak ≤ max caller.peak (max caller.scalars.peak
        (liveS caller+caller.frame.bindings.length+6)+
        max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1-caller.frame.state.storage.baseSpace)) := by
  obtain ⟨out,ran,strong,work,scalarLive,vectorLive,peak,_⟩ := construct_default_components caller heap valid models lengths strict base
  exact ⟨out,ran,strong,work,scalarLive,vectorLive,peak⟩

end Proofs.UfConstructorSpace
