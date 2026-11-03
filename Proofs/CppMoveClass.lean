import Proofs.CppMoveReturn
import Proofs.CppClassAssignValues

namespace Proofs.CppMoveClass
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppScalar

-- Reuse the actual scalar member assignment evaluator, including sequential
-- source loads and aliasing, rather than copying a snapshot of source values.
def scalarFields (s : Context) (vectorTy : Ty) (targets sources : List Nat) (fields : List (Ty × Bool)) :
    Option Context := do
  let out ← Proofs.CppClassAssign.assignFields (project s vectorTy) targets sources fields
  some (resumeExpression s out)

theorem project_scalarFields (s : Context) (vectorTy : Ty) (targets sources : List Nat)
    (fields : List (Ty × Bool)) (out : NState)
    (run : Proofs.CppClassAssign.assignFields (project s vectorTy) targets sources fields = some out) :
    project (resumeExpression s out) vectorTy = out := by
  have metadata := Proofs.CppClassAssign.fields_metadata (project s vectorTy) out targets sources fields run
  change (⟨out.scalars,(project s vectorTy).frame,(project s vectorTy).slots,(project s vectorTy).scope,out.peak⟩ : NState) =
    ⟨out.scalars,out.frame,out.slots,out.scope,out.peak⟩
  rw [metadata.1,metadata.2.1,metadata.2.2.1]

theorem scalarFields_correspondence (s : Context) (vectorTy : Ty) (targets sources : List Nat)
    (fields : List (Ty × Bool)) :
    (scalarFields s vectorTy targets sources fields).map (fun out => project out vectorTy) =
      Proofs.CppClassAssign.assignFields (project s vectorTy) targets sources fields := by
  cases run : Proofs.CppClassAssign.assignFields (project s vectorTy) targets sources fields with
  | none => simp [scalarFields,run]
  | some out => simp [scalarFields,run,project_scalarFields s vectorTy targets sources fields out run]

theorem scalarFields_ready (s : Context) (vectorTy : Ty) (targets sources : List Nat)
    (fields : List (Ty × Bool)) (ready : Proofs.CppClassAssign.Ready (project s vectorTy) targets sources fields) :
    ∃ out, scalarFields s vectorTy targets sources fields = some out := by
  obtain ⟨out,run⟩ := Proofs.CppClassAssign.fields_terminate (project s vectorTy) targets sources fields ready
  exact ⟨resumeExpression s out,by simp [scalarFields,run]⟩

theorem scalarFields_effects (s out : Context) (vectorTy : Ty) (targets sources : List Nat)
    (fields : List (Ty × Bool)) (run : scalarFields s vectorTy targets sources fields = some out) :
    out.objects = s.objects ∧ out.slots = s.slots ∧ out.scope = s.scope ∧
      out.scalars.bindings = s.scalars.bindings ∧ out.scalars.memory.length = s.scalars.memory.length ∧
      work out = work s+2*fields.length := by
  unfold scalarFields at run
  obtain ⟨result,lowRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have eq := Option.some.inj rest
  subst out
  have metadata := Proofs.CppClassAssign.fields_metadata (project s vectorTy) result targets sources fields lowRun
  have projected := project_scalarFields s vectorTy targets sources fields result lowRun
  have workEq : work (resumeExpression s result) = result.work := by
    rw [← project_work (resumeExpression s result) vectorTy,projected]
  exact ⟨rfl,rfl,rfl,metadata.2.2.2.1,metadata.2.2.2.2.1,
    workEq.trans (metadata.2.2.2.2.2.trans (by rw [project_work]))⟩


theorem scalarFields_peak (s out : Context) (vectorTy : Ty) (targets sources : List Nat)
    (fields : List (Ty × Bool)) (run : scalarFields s vectorTy targets sources fields = some out) :
    out.scalars.baseMemory = s.scalars.baseMemory ∧
      out.scalars.peak ≤ max s.scalars.peak (scalarLive s+1) ∧
      out.peak ≤ max s.peak (max s.scalars.peak (scalarLive s+1)+s.objects.heap.peak) := by
  unfold scalarFields at run
  obtain ⟨result,lowRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have eq := Option.some.inj rest
  subst out
  exact Proofs.CppClassAssign.fields_peak (project s vectorTy) result targets sources fields lowRun


-- The existing class move audit currently selects one vector followed by
-- scalar fields. Other layouts remain outside that audit until extended.
def assignClass (s : Context) (target source : Proofs.CppConstructorFinish.ObjectRef)
    (profile : Proofs.CppClassCopy.Profile) : Option (Context × Proofs.CppConstructorFinish.ObjectRef) := do
  if profile.vectorWritable then
    let tv ← vectorView s target.vectorSlot
    let sv ← vectorView s source.vectorSlot
    let objects ← Proofs.CppMoveViews.assign s.objects profile.element.valid tv sv
    let next := observe {s with objects := objects}
    let out ← scalarFields next profile.element target.scalarSlots source.scalarSlots profile.scalarFields
    some (charge out 1 0,target)
  else none


theorem assignClass_ready (s : Context) (target source : Proofs.CppConstructorFinish.ObjectRef)
    (profile : Proofs.CppClassCopy.Profile) (tvSlot svSlot : Nat)
    (tv sv : Proofs.CppMoveViews.View) (th sh : Proofs.CppMoveHeaders.Header)
    (vectorWritable : profile.vectorWritable = true)
    (targetSlot : vectorView s target.vectorSlot = some tvSlot)
    (sourceSlot : vectorView s source.vectorSlot = some svSlot)
    (targetFound : Proofs.CppMoveViews.resolve s.objects tvSlot = some (tv,th))
    (sourceFound : Proofs.CppMoveViews.resolve s.objects svSlot = some (sv,sh))
    (targetWritable : tv.writable = true) (sourceWritable : sv.writable = true)
    (targetReadable : Proofs.CppMoveHeaders.readable s.objects.heap th profile.element.valid = true)
    (sourceReadable : Proofs.CppMoveHeaders.readable s.objects.heap sh profile.element.valid = true)
    (limit : th.limit = sh.limit) (unique : Proofs.CppMoveHeaders.Unique s.objects.heap)
    (ready : Proofs.CppClassAssign.Ready (project s profile.element) target.scalarSlots source.scalarSlots profile.scalarFields) :
    ∃ out, assignClass s target source profile = some (out,target) := by
  have tp := Proofs.CppMoveViews.resolve_parts s.objects tvSlot tv th targetFound
  have sp := Proofs.CppMoveViews.resolve_parts s.objects svSlot sv sh sourceFound
  have core := Proofs.CppMoveAssign.move_assign_runs s.objects.heap profile.element.valid tv.header sv.header th sh
    tp.2.1 sp.2.1 (tp.2.2 targetWritable) (sp.2.2 sourceWritable) targetReadable sourceReadable limit unique
  let objects : Proofs.CppMoveViews.State Int :=
    ⟨Proofs.CppMoveAssign.assigned s.objects.heap tv.header sv.header th sh,s.objects.views⟩
  have moved : Proofs.CppMoveViews.assign s.objects profile.element.valid tvSlot svSlot = some objects :=
    Proofs.CppMoveViews.assign_runs s.objects profile.element.valid tvSlot svSlot tv sv th sh _
      targetFound sourceFound targetWritable sourceWritable core
  let next := observe {s with objects := objects}
  have nextReady : Proofs.CppClassAssign.Ready (project next profile.element)
      target.scalarSlots source.scalarSlots profile.scalarFields :=
    Proofs.CppClassAssign.ready_transfer (project s profile.element) (project next profile.element)
      target.scalarSlots source.scalarSlots profile.scalarFields (by
        intro slot ty
        simp only [NState.scalarCell,project_scalarSlot]
        rfl) ready
  obtain ⟨out,fieldsRun⟩ := scalarFields_ready next profile.element target.scalarSlots source.scalarSlots profile.scalarFields nextReady
  exact ⟨charge out 1 0,by simp [assignClass,vectorWritable,targetSlot,sourceSlot,moved,next,fieldsRun]⟩



theorem assignClass_success (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result)) :
    ∃ tv sv objects fieldsOut,
      profile.vectorWritable = true ∧ vectorView s target.vectorSlot = some tv ∧
      vectorView s source.vectorSlot = some sv ∧
      Proofs.CppMoveViews.assign s.objects profile.element.valid tv sv = some objects ∧
      scalarFields (observe {s with objects := objects}) profile.element target.scalarSlots source.scalarSlots
        profile.scalarFields = some fieldsOut ∧ out = charge fieldsOut 1 0 ∧ result = target := by
  unfold assignClass at run
  split at run
  next permission =>
    obtain ⟨tv,targetSlot,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    obtain ⟨sv,sourceSlot,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    obtain ⟨objects,moved,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    dsimp only at rest
    obtain ⟨fieldsOut,fieldsRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have eq := Prod.mk.inj (Option.some.inj rest)
    exact ⟨tv,sv,objects,fieldsOut,permission,targetSlot,sourceSlot,moved,fieldsRun,eq.1.symm,eq.2.symm⟩
  next => simp at run

theorem assignClass_heap (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result)) :
    ∃ tv sv objects,
      vectorView s target.vectorSlot = some tv ∧ vectorView s source.vectorSlot = some sv ∧
      Proofs.CppMoveViews.assign s.objects profile.element.valid tv sv = some objects ∧ out.objects = objects := by
  obtain ⟨tv,sv,objects,fieldsOut,_,targetSlot,sourceSlot,moved,fieldsRun,outEq,_⟩ :=
    assignClass_success s out target source result profile run
  have metadata := scalarFields_effects (observe {s with objects := objects}) fieldsOut profile.element
    target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  refine ⟨tv,sv,objects,targetSlot,sourceSlot,moved,?_⟩
  rw [outEq]
  exact metadata.1

theorem assignClass_invariants (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result))
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (valid : Proofs.CppMoveFrame.AllocationsValid s.objects.heap profile.element)
    (bounds : Proofs.CppMoveWrite.GrantBounds s.objects.heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap) :
    Proofs.CppMoveHeaders.Unique out.objects.heap ∧ Proofs.CppMoveHeaders.OwnsAll out.objects.heap ∧
      Proofs.CppMoveFrame.AllocationsValid out.objects.heap profile.element ∧
      Proofs.CppMoveWrite.GrantBounds out.objects.heap ∧ Proofs.CppMoveSpace.HeadersLive out.objects.heap := by
  obtain ⟨tv,sv,objects,_,_,moved,heapEq⟩ := assignClass_heap s out target source result profile run
  rw [heapEq]
  exact ⟨Proofs.CppMoveViews.assign_unique _ _ _ _ _ moved unique,
    Proofs.CppMoveViews.assign_ownsAll _ _ _ _ _ moved covered,
    Proofs.CppMoveFrame.assign_allocationsValid _ _ _ _ _ _ moved valid,
    Proofs.CppMoveWrite.assign_grantBounds _ _ _ _ _ moved bounds,
    Proofs.CppMoveSpace.assign_headersLive _ _ _ _ _ moved unique live⟩

theorem assignClass_no_resurrection (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (reference : Nat) (run : assignClass s target source profile = some (out,result))
    (old : Proofs.CppMoveHeaders.read s.objects.heap profile.element.valid reference = none) :
    Proofs.CppMoveHeaders.read out.objects.heap profile.element.valid reference = none := by
  obtain ⟨tv,sv,objects,_,_,moved,heapEq⟩ := assignClass_heap s out target source result profile run
  rw [heapEq]
  exact Proofs.CppMoveViews.assign_no_resurrection s.objects objects profile.element.valid tv sv reference moved old



theorem assignClass_metadata (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result)) :
    result = target ∧ out.slots = s.slots ∧ out.scope = s.scope ∧
      out.scalars.bindings = s.scalars.bindings ∧ out.scalars.memory.length = s.scalars.memory.length := by
  obtain ⟨_,_,objects,fieldsOut,_,_,_,_,fieldsRun,outEq,resultEq⟩ :=
    assignClass_success s out target source result profile run
  have metadata := scalarFields_effects (observe {s with objects := objects}) fieldsOut profile.element
    target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  rw [outEq]
  exact ⟨resultEq,metadata.2.1,metadata.2.2.1,metadata.2.2.2.1,metadata.2.2.2.2.1⟩

theorem assignClass_resources (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result)) :
    ∃ slot view header,
      vectorView s target.vectorSlot = some slot ∧ Proofs.CppMoveViews.resolve s.objects slot = some (view,header) ∧
      work out = work s+Proofs.CppMoveAssign.oldLength s.objects.heap header+2*profile.scalarFields.length+2 ∧
      out.objects.heap.liveSpace+Proofs.CppMoveAssign.oldCapacity s.objects.heap header = s.objects.heap.liveSpace ∧
      out.objects.heap.peak = max s.objects.heap.peak (s.objects.heap.liveSpace+1-s.objects.heap.baseSpace) ∧
      out.objects.heap.baseSpace = s.objects.heap.baseSpace := by
  obtain ⟨tv,sv,objects,fieldsOut,_,targetSlot,_,moved,fieldsRun,outEq,_⟩ :=
    assignClass_success s out target source result profile run
  obtain ⟨view,header,resolved,heapWork,space,peak,base,_⟩ :=
    Proofs.CppMoveViews.assign_resources s.objects objects profile.element.valid tv sv moved
  have metadata := scalarFields_effects (observe {s with objects := objects}) fieldsOut profile.element
    target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  have heapEq : out.objects = objects := by rw [outEq]; exact metadata.1
  have returnedWork : work out = work fieldsOut+1 := by
    rw [outEq]
    simp [work,charge,Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  have nextWork : work (observe {s with objects := objects}) =
      work s+Proofs.CppMoveAssign.oldLength s.objects.heap header+1 := by
    change s.scalars.work+objects.heap.work = work s+Proofs.CppMoveAssign.oldLength s.objects.heap header+1
    have original : work s = s.scalars.work+s.objects.heap.work := rfl
    clear * - heapWork original
    omega
  have fieldsWork := metadata.2.2.2.2.2
  refine ⟨tv,view,header,targetSlot,resolved,?_,?_,?_,?_⟩
  · clear * - returnedWork nextWork fieldsWork
    omega
  · rw [heapEq]; exact space
  · rw [heapEq]; exact peak
  · rw [heapEq]; exact base



theorem assignClass_peak (s out : Context)
    (target source result : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (run : assignClass s target source profile = some (out,result)) :
    out.scalars.peak ≤ max s.scalars.peak (scalarLive s+1) ∧
      out.peak ≤ max s.peak (max s.scalars.peak (scalarLive s+1)+
        max s.objects.heap.peak (s.objects.heap.liveSpace+1-s.objects.heap.baseSpace)) := by
  obtain ⟨tv,sv,objects,fieldsOut,_,_,_,moved,fieldsRun,outEq,_⟩ :=
    assignClass_success s out target source result profile run
  have metadata := scalarFields_effects (observe {s with objects := objects}) fieldsOut profile.element
    target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  have peaks := scalarFields_peak (observe {s with objects := objects}) fieldsOut profile.element
    target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  obtain ⟨_,_,_,_,_,heapPeak,_,_⟩ := Proofs.CppMoveViews.assign_resources s.objects objects profile.element.valid tv sv moved
  have sameLive : scalarLive fieldsOut = scalarLive s := by
    unfold scalarLive
    rw [metadata.2.2.2.2.1,metadata.2.2.2.1,peaks.1]
    rfl
  have scalar := peaks.2.1
  change fieldsOut.scalars.peak ≤ max s.scalars.peak (scalarLive s+1) at scalar
  have contextPeak := peaks.2.2
  change fieldsOut.peak ≤ max (max s.peak (s.scalars.peak+objects.heap.peak))
    (max s.scalars.peak (scalarLive s+1)+objects.heap.peak) at contextPeak
  have finalScalar : out.scalars.peak = max fieldsOut.scalars.peak (scalarLive fieldsOut) := by rw [outEq]; rfl
  have finalPeak : out.peak = max fieldsOut.peak (out.scalars.peak+fieldsOut.objects.heap.peak) := by rw [outEq]; rfl
  rw [metadata.1] at finalPeak
  change out.peak = max fieldsOut.peak (out.scalars.peak+objects.heap.peak) at finalPeak
  have scalarBound : out.scalars.peak ≤ max s.scalars.peak (scalarLive s+1) := by
    clear * - finalScalar sameLive scalar
    omega
  refine ⟨scalarBound,?_⟩
  have oldScalar : s.scalars.peak ≤ max s.scalars.peak (scalarLive s+1) := Nat.le_max_left _ _
  clear * - contextPeak finalPeak scalarBound oldScalar heapPeak
  omega


end Proofs.CppMoveClass
