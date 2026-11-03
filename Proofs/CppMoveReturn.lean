import Proofs.CppMoveDestroy

namespace Proofs.CppMoveReturn
open Proofs.CppMoveHeaders Proofs.CppMoveAssign Proofs.CppMoveDestroy
open Proofs.CppMoveContext

-- A returned vector is first move-constructed in the caller's scope.
-- The source object remains local and is destroyed only after the transfer.
def returnOwned (caller callee : Context) (ty : Proofs.CppScalar.Ty)
    (source : Nat) (writable : Bool) : Option (Context × Nat) := do
  let (objects,slot) ← Proofs.CppMoveViews.construct callee.objects ty.valid source caller.scope writable
  let next := observe {callee with objects := objects}
  let out ← finishScope caller next ty
  some (out,slot)

theorem constructed_readable (s : Heap α) (source : Nat) (header : Header) (scope : Nat) (writable : Bool)
    (accept : α → Bool) (found : s.header source = some header) (valid : ReadableHeaders s accept) :
    ReadableHeaders (constructed s source header scope writable) accept := by
  intro id actual actualFound
  cases owns : actual.allocation with
  | none => simp [readable,owns]
  | some owner =>
    rcases constructed_owner_cases s source id header actual scope writable found actualFound owner owns with
      ⟨_,rfl⟩ | ⟨_,_,previous⟩
    · change readable s header accept = true
      exact valid source header found
    · change readable s actual accept = true
      exact valid id actual previous

theorem destroyAtScope_keeps (s out : Heap α) (accept : α → Bool) (scope id other : Nat) (header : Header)
    (run : destroyAtScope s accept scope id = some out)
    (found : s.header other = some header) (outside : header.scope ≠ scope) : out.header other = some header := by
  rcases destroyAtScope_success s out accept scope id run with eq | ⟨actual,actualFound,same,eq⟩
  · subst out; exact found
  · subst out
    have different : id ≠ other := by
      intro eq
      subst other
      have h := Option.some.inj (actualFound.symm.trans found)
      subst actual
      exact outside same
    rw [destroyed_other s id other actual different]
    exact found

theorem destroyList_keeps (s out : Heap α) (accept : α → Bool) (scope : Nat) (ids : List Nat)
    (other : Nat) (header : Header) (run : destroyList s accept scope ids = some out)
    (found : s.header other = some header) (outside : header.scope ≠ scope) : out.header other = some header := by
  induction ids generalizing s with
  | nil => cases Option.some.inj run; exact found
  | cons id tail ih =>
    simp only [destroyList] at run
    obtain ⟨next,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
    exact ih next rest (destroyAtScope_keeps s next accept scope id other header first found outside)


theorem finishScope_keeps (caller callee out : Context) (ty : Proofs.CppScalar.Ty) (id : Nat) (header : Header)
    (run : finishScope caller callee ty = some out)
    (found : callee.objects.heap.header id = some header) (outside : header.scope ≠ callee.scope) :
    out.objects.heap.header id = some header := by
  unfold finishScope at run
  obtain ⟨heap,destroyRun,finishRun⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have metadata := finishBorrowed_metadata caller
    (observe {callee with objects := {callee.objects with heap := heap}}) out finishRun
  rw [metadata.1]
  exact destroyList_keeps callee.objects.heap heap ty.valid callee.scope (scopeOrder callee.objects.heap)
    id header destroyRun found outside

theorem finishScope_views (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (run : finishScope caller callee ty = some out) : out.objects.views = callee.objects.views := by
  unfold finishScope at run
  obtain ⟨heap,_,finishRun⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have metadata := finishBorrowed_metadata caller
    (observe {callee with objects := {callee.objects with heap := heap}}) out finishRun
  rw [metadata.1]
  rfl

theorem returnOwned_target (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (source slot : Nat) (writable : Bool)
    (run : returnOwned caller callee ty source writable = some (out,slot))
    (scope : callee.scope = caller.scope+1) :
    ∃ view header destination,
      Proofs.CppMoveViews.resolve callee.objects source = some (view,header) ∧
      destination = callee.objects.heap.headers.length ∧
      Proofs.CppMoveViews.resolve out.objects slot =
        some (⟨destination,writable⟩,⟨header.allocation,caller.scope,writable,header.limit⟩) := by
  unfold returnOwned at run
  obtain ⟨pair,moveRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  rcases pair with ⟨objects,movedSlot⟩
  dsimp only at rest
  obtain ⟨actual,finishRun,returned⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have pairEq := Prod.mk.inj (Option.some.inj returned)
  rcases pairEq with ⟨rfl,rfl⟩
  obtain ⟨view,header,destination,resolved,_,core,views,slotEq⟩ :=
    Proofs.CppMoveViews.construct_success callee.objects objects ty.valid source caller.scope movedSlot writable moveRun
  obtain ⟨original,originalFound,dest,heapEq⟩ := move_construct_success callee.objects.heap objects.heap
    ty.valid view.header caller.scope destination writable core
  have parts := Proofs.CppMoveViews.resolve_parts callee.objects source view header resolved
  have headerEq := Option.some.inj (parts.2.1.symm.trans originalFound)
  subst original
  have target : objects.heap.header destination = some ⟨header.allocation,caller.scope,writable,header.limit⟩ := by
    rw [heapEq,dest]
    exact constructed_target _ _ _ _ _
  have survives := finishScope_keeps caller (observe {callee with objects := objects}) actual ty destination
    ⟨header.allocation,caller.scope,writable,header.limit⟩ finishRun target (by change caller.scope ≠ callee.scope; omega)
  have finalViews := finishScope_views caller (observe {callee with objects := objects}) actual ty finishRun
  refine ⟨view,header,destination,resolved,dest,?_⟩
  apply Proofs.CppMoveViews.resolve_runs
  · rw [finalViews]
    change objects.views[movedSlot]? = some ⟨destination,writable⟩
    rw [views,slotEq]
    simp
  · exact survives
  · intro permission; exact permission


-- Success follows from the source's current permissions and the existing finish guards.
-- No completed returnOwned execution is assumed.
theorem returnOwned_ready (caller callee : Context) (ty : Proofs.CppScalar.Ty)
    (source : Nat) (writable : Bool) (view : Proofs.CppMoveViews.View) (header : Header)
    (found : Proofs.CppMoveViews.resolve callee.objects source = some (view,header))
    (permission : view.writable = true)
    (scope : callee.scope = caller.scope+1)
    (views : callee.objects.views.take caller.objects.views.length = caller.objects.views)
    (grants : callee.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (unique : Unique callee.objects.heap) (valid : ReadableHeaders callee.objects.heap ty.valid) :
    ∃ out slot, returnOwned caller callee ty source writable = some (out,slot) := by
  have parts := Proofs.CppMoveViews.resolve_parts callee.objects source view header found
  have moveRun := Proofs.CppMoveViews.construct_ready callee.objects ty.valid source caller.scope writable
    view header found permission (valid view.header header parts.2.1)
  let objects : Proofs.CppMoveViews.State Int :=
    ⟨constructed callee.objects.heap view.header header caller.scope writable,
      callee.objects.views++[⟨callee.objects.heap.headers.length,writable⟩]⟩
  let next := observe {callee with objects := objects}
  have prefixLength : caller.objects.views.length ≤ callee.objects.views.length := by
    have lengths := congrArg List.length views
    simp only [List.length_take] at lengths
    omega
  have nextViews : next.objects.views.take caller.objects.views.length = caller.objects.views := by
    change (callee.objects.views++_).take caller.objects.views.length = _
    rw [List.take_append_of_le_length prefixLength]
    exact views
  have nextGrants : next.objects.heap.grants.take caller.objects.heap.grants.length = caller.objects.heap.grants := grants
  have nextUnique : Unique next.objects.heap := constructed_unique _ _ _ _ _ unique parts.2.1
  have nextValid : ReadableHeaders next.objects.heap ty.valid := constructed_readable _ _ _ _ _ _ parts.2.1 valid
  obtain ⟨out,finish⟩ := finishScope_ready caller next ty scope nextViews nextGrants fits types nextUnique nextValid
  refine ⟨out,callee.objects.views.length,?_⟩
  simp [returnOwned,moveRun,objects,next,finish]


theorem returnOwned_success (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (source slot : Nat) (writable : Bool)
    (run : returnOwned caller callee ty source writable = some (out,slot)) :
    ∃ objects, Proofs.CppMoveViews.construct callee.objects ty.valid source caller.scope writable = some (objects,slot) ∧
      finishScope caller (observe {callee with objects := objects}) ty = some out := by
  unfold returnOwned at run
  obtain ⟨pair,moveRun,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  rcases pair with ⟨objects,movedSlot⟩
  dsimp only at rest
  obtain ⟨actual,finishRun,returned⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have eq := Prod.mk.inj (Option.some.inj returned)
  rcases eq with ⟨rfl,rfl⟩
  exact ⟨objects,moveRun,finishRun⟩

theorem finishScope_invariants (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (run : finishScope caller callee ty = some out)
    (unique : Unique callee.objects.heap) (readable : ReadableHeaders callee.objects.heap ty.valid)
    (covered : OwnsAll callee.objects.heap) (valid : Proofs.CppMoveFrame.AllocationsValid callee.objects.heap ty)
    (bounds : Proofs.CppMoveWrite.GrantBounds callee.objects.heap) :
    Unique out.objects.heap ∧ ReadableHeaders out.objects.heap ty.valid ∧ OwnsAll out.objects.heap ∧
      Proofs.CppMoveFrame.AllocationsValid out.objects.heap ty ∧ Proofs.CppMoveWrite.GrantBounds out.objects.heap ∧
      Proofs.CppMoveSpace.HeadersLive out.objects.heap := by
  unfold finishScope at run
  obtain ⟨heap,destroyRun,finishRun⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have metadata := finishBorrowed_metadata caller
    (observe {callee with objects := {callee.objects with heap := heap}}) out finishRun
  rw [metadata.1]
  exact destroyScope_invariants callee.objects.heap heap ty callee.scope destroyRun unique readable covered valid bounds

theorem returnOwned_invariants (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (source slot : Nat) (writable : Bool)
    (run : returnOwned caller callee ty source writable = some (out,slot))
    (unique : Unique callee.objects.heap) (readable : ReadableHeaders callee.objects.heap ty.valid)
    (covered : OwnsAll callee.objects.heap) (valid : Proofs.CppMoveFrame.AllocationsValid callee.objects.heap ty)
    (bounds : Proofs.CppMoveWrite.GrantBounds callee.objects.heap) :
    Unique out.objects.heap ∧ ReadableHeaders out.objects.heap ty.valid ∧ OwnsAll out.objects.heap ∧
      Proofs.CppMoveFrame.AllocationsValid out.objects.heap ty ∧ Proofs.CppMoveWrite.GrantBounds out.objects.heap ∧
      Proofs.CppMoveSpace.HeadersLive out.objects.heap := by
  obtain ⟨objects,moveRun,finishRun⟩ := returnOwned_success caller callee out ty source slot writable run
  obtain ⟨view,header,destination,_,_,core,_,_⟩ :=
    Proofs.CppMoveViews.construct_success callee.objects objects ty.valid source caller.scope slot writable moveRun
  obtain ⟨original,found,_,heapEq⟩ := move_construct_success callee.objects.heap objects.heap
    ty.valid view.header caller.scope destination writable core
  have nextReadable : ReadableHeaders objects.heap ty.valid := by
    rw [heapEq]
    exact constructed_readable _ _ _ _ _ _ found readable
  exact finishScope_invariants caller (observe {callee with objects := objects}) out ty finishRun
    (Proofs.CppMoveViews.construct_unique _ _ _ _ _ _ _ moveRun unique) nextReadable
    (Proofs.CppMoveViews.construct_ownsAll _ _ _ _ _ _ _ moveRun covered)
    (Proofs.CppMoveFrame.construct_allocationsValid _ _ _ _ _ _ _ _ moveRun valid)
    (Proofs.CppMoveWrite.construct_grantBounds _ _ _ _ _ _ _ moveRun bounds)

theorem finishBorrowed_resources (caller callee out : Context)
    (run : finishBorrowed caller callee = some out) :
    work out = work callee+1 ∧ out.objects.heap = callee.objects.heap ∧
      out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) ∧
      out.peak = max (max caller.peak callee.peak) (out.scalars.peak+out.objects.heap.peak) := by
  unfold finishBorrowed at run
  split at run
  next guard =>
    have eq := Option.some.inj run
    subst out
    have fits := guard.2.2.2.1
    simp [work,observe,Proofs.CppState.State.observe,scalarLive,Nat.min_eq_left fits,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  next => simp at run



theorem scopeCost_constructed_old (s : Heap α) (source : Nat) (header : Header)
    (scope target id : Nat) (writable : Bool) (found : s.header source = some header)
    (inside : id < s.headers.length) :
    scopeCost (constructed s source header scope writable) target id ≤ scopeCost s target id := by
  by_cases same : source = id
  · subst id
    rw [show scopeCost (constructed s source header scope writable) target source =
      (if header.scope = target then 1 else 0) by
        simp [scopeCost,constructed_source s source header scope writable found,oldLength]]
    simp only [scopeCost,found]
    split <;> omega
  · have other := constructed_other s source id header scope writable inside same
    unfold scopeCost
    rw [other]
    cases previous : s.header id with
    | none => exact le_refl _
    | some actual =>
      have lengths : oldLength (constructed s source header scope writable) actual = oldLength s actual := rfl
      dsimp only
      rw [lengths]

theorem scopeBudget_mono (s out : Heap α) (scope : Nat) (ids : List Nat)
    (cost : ∀ id ∈ ids, scopeCost out scope id ≤ scopeCost s scope id) :
    scopeBudget out scope ids ≤ scopeBudget s scope ids := by
  induction ids with
  | nil => exact le_refl _
  | cons id tail ih =>
    have head := cost id (by simp)
    have rest := ih (fun i member => cost i (List.mem_cons_of_mem id member))
    simp only [scopeBudget]
    omega

-- Moving storage out of the closing scope cannot increase its destructor budget.
theorem scopeBudget_constructed (s : Heap α) (source : Nat) (header : Header)
    (scope target : Nat) (writable : Bool) (found : s.header source = some header)
    (outside : scope ≠ target) :
    scopeBudget (constructed s source header scope writable) target
      (scopeOrder (constructed s source header scope writable)) ≤ scopeBudget s target (scopeOrder s) := by
  have order : scopeOrder (constructed s source header scope writable) = s.headers.length :: scopeOrder s := by
    simp [scopeOrder,constructed,List.range_succ]
  rw [order]
  have head : scopeCost (constructed s source header scope writable) target s.headers.length = 0 := by
    simp [scopeCost,constructed_target,outside]
  simp only [scopeBudget,head,Nat.zero_add]
  apply scopeBudget_mono
  intro id member
  exact scopeCost_constructed_old s source header scope target id writable found ((scopeOrder_mem s id).mp member)

theorem finishScope_resources (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (run : finishScope caller callee ty = some out) :
    work out ≤ work callee+scopeBudget callee.objects.heap callee.scope (scopeOrder callee.objects.heap)+1 ∧
      out.objects.heap.liveSpace ≤ callee.objects.heap.liveSpace ∧
      out.objects.heap.baseSpace = callee.objects.heap.baseSpace ∧
      out.objects.heap.peak ≤ max callee.objects.heap.peak (callee.objects.heap.liveSpace-callee.objects.heap.baseSpace) ∧
      out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) ∧
      out.peak ≤ max (max caller.peak callee.peak)
        (max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) +
          max callee.objects.heap.peak (callee.objects.heap.liveSpace-callee.objects.heap.baseSpace)) := by
  unfold finishScope at run
  obtain ⟨heap,destroyRun,finishRun⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  let next := observe {callee with objects := {callee.objects with heap := heap}}
  have finish := finishBorrowed_resources caller next out finishRun
  have destroy := destroyList_resources callee.objects.heap heap ty.valid callee.scope
    (scopeOrder callee.objects.heap) destroyRun
  have budget := destroyScope_work callee.objects.heap heap ty.valid callee.scope destroyRun
  have workEq : work out = callee.scalars.work+heap.work+1 := finish.1
  have heapEq : out.objects.heap = heap := finish.2.1
  have scalarEq : out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) := finish.2.2.1
  have peakEq : out.peak = max (max caller.peak (max callee.peak (callee.scalars.peak+heap.peak)))
      (out.scalars.peak+heap.peak) := by
    simpa only [next,observe,heapEq] using finish.2.2.2
  refine ⟨?_,?_,?_,?_,scalarEq,?_⟩
  · have calleeWork : work callee = callee.scalars.work+callee.objects.heap.work := rfl
    omega
  · rw [heapEq]; exact destroy.1
  · rw [heapEq]; exact destroy.2.1
  · rw [heapEq]; exact destroy.2.2.2.2
  · have scalar : callee.scalars.peak ≤ out.scalars.peak := by rw [scalarEq]; omega
    omega



theorem returnOwned_resources (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (source slot : Nat) (writable : Bool)
    (run : returnOwned caller callee ty source writable = some (out,slot))
    (scope : callee.scope = caller.scope+1) :
    work out ≤ work callee+scopeBudget callee.objects.heap callee.scope (scopeOrder callee.objects.heap)+2 ∧
      out.objects.heap.liveSpace ≤ callee.objects.heap.liveSpace+1 ∧
      out.objects.heap.baseSpace = callee.objects.heap.baseSpace ∧
      out.objects.heap.peak ≤ max callee.objects.heap.peak (callee.objects.heap.liveSpace+1-callee.objects.heap.baseSpace) ∧
      out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) ∧
      out.peak ≤ max (max caller.peak callee.peak)
        (max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) +
          max callee.objects.heap.peak (callee.objects.heap.liveSpace+1-callee.objects.heap.baseSpace)) := by
  obtain ⟨objects,moveRun,finishRun⟩ := returnOwned_success caller callee out ty source slot writable run
  let next := observe {callee with objects := objects}
  obtain ⟨workBound,liveBound,baseEq,heapPeak,scalarEq,peakBound⟩ := finishScope_resources caller next out ty finishRun
  obtain ⟨moveWork,moveLive,movePeak,moveBase⟩ :=
    Proofs.CppMoveViews.construct_resources callee.objects objects ty.valid source caller.scope slot writable moveRun
  obtain ⟨view,_,destination,_,_,core,_,_⟩ :=
    Proofs.CppMoveViews.construct_success callee.objects objects ty.valid source caller.scope slot writable moveRun
  obtain ⟨header,found,_,heapEq⟩ := move_construct_success callee.objects.heap objects.heap
    ty.valid view.header caller.scope destination writable core
  have budget : scopeBudget objects.heap callee.scope (scopeOrder objects.heap) ≤
      scopeBudget callee.objects.heap callee.scope (scopeOrder callee.objects.heap) := by
    rw [heapEq]
    exact scopeBudget_constructed _ _ _ _ _ _ found (by clear * - scope; omega)
  have oldWork : work callee = callee.scalars.work+callee.objects.heap.work := rfl
  have nextWork : work next = work callee+1 := by
    change callee.scalars.work+objects.heap.work = work callee+1
    clear * - oldWork moveWork
    omega
  change work out ≤ work next+scopeBudget objects.heap callee.scope (scopeOrder objects.heap)+1 at workBound
  change out.objects.heap.liveSpace ≤ objects.heap.liveSpace at liveBound
  change out.objects.heap.baseSpace = objects.heap.baseSpace at baseEq
  change out.objects.heap.peak ≤ max objects.heap.peak (objects.heap.liveSpace-objects.heap.baseSpace) at heapPeak
  change out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) at scalarEq
  change out.peak ≤ max (max caller.peak (max callee.peak (callee.scalars.peak+objects.heap.peak)))
    (max (max caller.scalars.peak callee.scalars.peak) (scalarLive caller) +
      max objects.heap.peak (objects.heap.liveSpace-objects.heap.baseSpace)) at peakBound
  refine ⟨?_,?_,baseEq.trans moveBase,?_,scalarEq,?_⟩
  · clear * - workBound nextWork budget
    omega
  · exact liveBound.trans (Nat.le_of_eq moveLive)
  · clear * - heapPeak movePeak moveLive moveBase
    omega
  · clear * - peakBound movePeak moveLive moveBase
    omega

theorem finishScope_no_resurrection (caller callee out : Context) (ty : Proofs.CppScalar.Ty) (reference : Nat)
    (run : finishScope caller callee ty = some out)
    (old : Proofs.CppMoveHeaders.read callee.objects.heap ty.valid reference = none) :
    Proofs.CppMoveHeaders.read out.objects.heap ty.valid reference = none := by
  unfold finishScope at run
  obtain ⟨heap,destroyRun,finishRun⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  have metadata := finishBorrowed_metadata caller
    (observe {callee with objects := {callee.objects with heap := heap}}) out finishRun
  rw [metadata.1]
  exact destroyScope_no_resurrection callee.objects.heap heap ty.valid callee.scope reference destroyRun old

theorem returnOwned_no_resurrection (caller callee out : Context) (ty : Proofs.CppScalar.Ty)
    (source slot reference : Nat) (writable : Bool)
    (run : returnOwned caller callee ty source writable = some (out,slot))
    (old : Proofs.CppMoveHeaders.read callee.objects.heap ty.valid reference = none) :
    Proofs.CppMoveHeaders.read out.objects.heap ty.valid reference = none := by
  obtain ⟨objects,moveRun,finishRun⟩ := returnOwned_success caller callee out ty source slot writable run
  obtain ⟨view,_,destination,_,_,core,_,_⟩ :=
    Proofs.CppMoveViews.construct_success callee.objects objects ty.valid source caller.scope slot writable moveRun
  have moved := move_construct_read callee.objects.heap objects.heap ty.valid view.header caller.scope destination writable core reference
  exact finishScope_no_resurrection caller (observe {callee with objects := objects}) out ty reference finishRun (moved.trans old)


end Proofs.CppMoveReturn
