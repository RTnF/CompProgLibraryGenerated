import Proofs.CppMoveAssign

namespace Proofs.CppMoveViews
open Proofs.CppMoveHeaders

-- Object aliases name headers; element grants in heap retain allocation identity.
-- This is ghost interpreter metadata, not an additional C++ object allocation.
structure View where
  header : Nat
  writable : Bool
  deriving DecidableEq, Repr

structure State (α : Type) where
  heap : Heap α
  views : List View

-- A readonly view can be obtained from a mutable object without lowering the
-- header's maximum permission or changing existing mutable element grants.
def bind (s : State α) (header : Nat) (writable : Bool) : Option (State α × Nat) := do
  let object ← s.heap.header header
  if writable = true → object.writable = true then
    some (⟨s.heap,s.views++[⟨header,writable⟩]⟩,s.views.length)
  else none

def resolve (s : State α) (slot : Nat) : Option (View × Header) := do
  let view ← s.views[slot]?
  let object ← s.heap.header view.header
  if view.writable = true → object.writable = true then some (view,object) else none

def capture (s : State α) (accept : α → Bool) (slot : Nat) (index : Int) (writable : Bool) :
    Option (State α × Nat) := do
  let (view,_) ← resolve s slot
  if writable = true → view.writable = true then
    let (heap,reference) ← Proofs.CppMoveHeaders.capture s.heap accept view.header index writable
    some (⟨heap,s.views⟩,reference)
  else none

def assign (s : State α) (accept : α → Bool) (target source : Nat) : Option (State α) := do
  let (tv,_) ← resolve s target
  let (sv,_) ← resolve s source
  if tv.writable ∧ sv.writable then
    let heap ← Proofs.CppMoveAssign.moveAssign s.heap accept tv.header sv.header
    some ⟨heap,s.views⟩
  else none

def construct (s : State α) (accept : α → Bool) (source scope : Nat) (writable : Bool) :
    Option (State α × Nat) := do
  let (view,_) ← resolve s source
  if view.writable then
    let (heap,header) ← moveConstruct s.heap accept view.header scope writable
    some (⟨heap,s.views++[⟨header,writable⟩]⟩,s.views.length)
  else none

-- No requirement that source/target view slots differ: self move is determined
-- by equal HeaderIds inside moveAssign, including two distinct aliases.
theorem assign_runs (s : State α) (accept : α → Bool) (target source : Nat)
    (tv sv : View) (th sh : Header) (out : Heap α)
    (targetFound : resolve s target = some (tv,th))
    (sourceFound : resolve s source = some (sv,sh))
    (targetWrite : tv.writable = true) (sourceWrite : sv.writable = true)
    (run : Proofs.CppMoveAssign.moveAssign s.heap accept tv.header sv.header = some out) :
    assign s accept target source = some ⟨out,s.views⟩ := by
  simp [assign,targetFound,sourceFound,targetWrite,sourceWrite,run]

theorem readonly_assign_target (s : State α) (accept : α → Bool) (target source : Nat)
    (tv : View) (th : Header) (found : resolve s target = some (tv,th))
    (readonly : tv.writable = false) : assign s accept target source = none := by
  simp only [assign,found]
  cases sourceFound : resolve s source with
  | none => simp
  | some pair => rcases pair with ⟨sv,sh⟩; simp [readonly]

theorem readonly_construct (s : State α) (accept : α → Bool) (source scope : Nat)
    (writable : Bool) (view : View) (header : Header)
    (found : resolve s source = some (view,header)) (readonly : view.writable = false) :
    construct s accept source scope writable = none := by
  simp [construct,found,readonly]

theorem readonly_capture (s : State α) (accept : α → Bool) (slot : Nat) (index : Int)
    (view : View) (header : Header) (found : resolve s slot = some (view,header))
    (readonly : view.writable = false) : capture s accept slot index true = none := by
  simp [capture,found,readonly]

-- Element access deliberately ignores object-view constness after capture.
def read (s : State α) (accept : α → Bool) (reference : Nat) : Option α :=
  Proofs.CppMoveHeaders.read s.heap accept reference

-- Still needs typed Frame/NState materialization, scalar order and resource
-- correspondence. This draft is not a complete caller adapter.

theorem readonly_assign_source (s : State α) (accept : α → Bool) (target source : Nat)
    (sv : View) (sh : Header) (found : resolve s source = some (sv,sh))
    (readonly : sv.writable = false) : assign s accept target source = none := by
  unfold assign
  cases targetFound : resolve s target with
  | none => simp
  | some pair => rcases pair with ⟨tv,th⟩; simp [found,readonly]

theorem assign_success (s out : State α) (accept : α → Bool) (target source : Nat)
    (run : assign s accept target source = some out) :
    ∃ tv th sv sh, resolve s target = some (tv,th) ∧ resolve s source = some (sv,sh) ∧
      tv.writable = true ∧ sv.writable = true ∧
      Proofs.CppMoveAssign.moveAssign s.heap accept tv.header sv.header = some out.heap ∧
      out.views = s.views := by
  unfold assign at run
  cases tf : resolve s target with
  | none => simp [tf] at run
  | some pair =>
    rcases pair with ⟨tv,th⟩
    cases sf : resolve s source with
    | none => simp [tf,sf] at run
    | some pair =>
      rcases pair with ⟨sv,sh⟩
      simp only [tf,sf,Bind.bind,Option.bind] at run
      split at run
      next allowed =>
        cases core : Proofs.CppMoveAssign.moveAssign s.heap accept tv.header sv.header with
        | none => simp [core] at run
        | some heap =>
          simp only [core] at run
          have eq := Option.some.inj run
          subst out
          exact ⟨tv,th,sv,sh,rfl,rfl,allowed.1,allowed.2,core,rfl⟩
      next => simp at run

theorem assign_unique (s out : State α) (accept : α → Bool) (target source : Nat)
    (run : assign s accept target source = some out) (unique : Unique s.heap) : Unique out.heap := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ := assign_success s out accept target source run
  exact Proofs.CppMoveAssign.move_assign_unique s.heap out.heap accept tv.header sv.header unique core

theorem assign_no_resurrection (s out : State α) (accept : α → Bool) (target source reference : Nat)
    (run : assign s accept target source = some out) (dead : read s accept reference = none) :
    read out accept reference = none := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ := assign_success s out accept target source run
  exact Proofs.CppMoveAssign.move_assign_no_resurrection s.heap out.heap accept tv.header sv.header core reference dead


theorem resolve_parts (s : State α) (slot : Nat) (view : View) (header : Header)
    (found : resolve s slot = some (view,header)) :
    s.views[slot]? = some view ∧ s.heap.header view.header = some header ∧
      (view.writable = true → header.writable = true) := by
  unfold resolve at found
  cases vf : s.views[slot]? with
  | none => simp [vf] at found
  | some v =>
    cases hf : s.heap.header v.header with
    | none => simp [vf,hf] at found
    | some h =>
      simp only [vf,hf,Bind.bind,Option.bind] at found
      split at found
      next permission =>
        have eq := Option.some.inj found
        cases eq
        exact ⟨rfl,hf,permission⟩
      next => simp at found

theorem assign_ready (s : State α) (accept : α → Bool) (target source : Nat)
    (tv sv : View) (th sh : Header)
    (tf : resolve s target = some (tv,th)) (sf : resolve s source = some (sv,sh))
    (tw : tv.writable = true) (sw : sv.writable = true)
    (tr : readable s.heap th accept = true) (sr : readable s.heap sh accept = true)
    (limit : th.limit = sh.limit) (unique : Unique s.heap) :
    assign s accept target source =
      some ⟨Proofs.CppMoveAssign.assigned s.heap tv.header sv.header th sh,s.views⟩ := by
  have tp := resolve_parts s target tv th tf
  have sp := resolve_parts s source sv sh sf
  exact assign_runs s accept target source tv sv th sh _ tf sf tw sw
    (Proofs.CppMoveAssign.move_assign_runs s.heap accept tv.header sv.header th sh
      tp.2.1 sp.2.1 (tp.2.2 tw) (sp.2.2 sw) tr sr limit unique)

theorem assign_ownsAll (s out : State α) (accept : α → Bool) (target source : Nat)
    (run : assign s accept target source = some out) (covered : OwnsAll s.heap) : OwnsAll out.heap := by
  obtain ⟨tv,th,sv,sh,_,_,_,_,core,_⟩ := assign_success s out accept target source run
  exact Proofs.CppMoveAssign.move_assign_ownsAll s.heap out.heap accept tv.header sv.header covered core

theorem assign_resources (s out : State α) (accept : α → Bool) (target source : Nat)
    (run : assign s accept target source = some out) :
    ∃ tv th, resolve s target = some (tv,th) ∧
      out.heap.work = s.heap.work + Proofs.CppMoveAssign.oldLength s.heap th + 1 ∧
      out.heap.liveSpace + Proofs.CppMoveAssign.oldCapacity s.heap th = s.heap.liveSpace ∧
      out.heap.peak = max s.heap.peak (s.heap.liveSpace+1-s.heap.baseSpace) ∧
      out.heap.baseSpace = s.heap.baseSpace ∧ out.views = s.views := by
  obtain ⟨tv,th,sv,sh,tf,sf,_,_,core,views⟩ := assign_success s out accept target source run
  obtain ⟨old,hf,work,space,peak,base⟩ :=
    Proofs.CppMoveAssign.move_assign_resources s.heap out.heap accept tv.header sv.header core
  have hp := (resolve_parts s target tv th tf).2.1
  have eq := Option.some.inj (hf.symm.trans hp)
  subst old
  exact ⟨tv,th,tf,work,space,peak,base,views⟩

theorem bind_runs (s : State α) (id : Nat) (header : Header) (writable : Bool)
    (found : s.heap.header id = some header)
    (permission : writable = true → header.writable = true) :
    bind s id writable = some (⟨s.heap,s.views++[⟨id,writable⟩]⟩,s.views.length) := by
  simp [bind,found]
  exact permission

theorem bind_old_view (s : State α) (id : Nat) (writable : Bool) (slot : Nat) (view : View)
    (found : s.views[slot]? = some view) :
    (s.views++[⟨id,writable⟩])[slot]? = some view := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

-- Re-resolving a view reads the current header, rather than a saved allocation.
theorem resolve_runs (s : State α) (slot : Nat) (view : View) (header : Header)
    (vf : s.views[slot]? = some view) (hf : s.heap.header view.header = some header)
    (permission : view.writable = true → header.writable = true) :
    resolve s slot = some (view,header) := by
  simp [resolve,vf,hf]
  exact permission


theorem construct_ready (s : State α) (accept : α → Bool) (source scope : Nat) (writable : Bool)
    (view : View) (header : Header) (found : resolve s source = some (view,header))
    (permission : view.writable = true) (valid : readable s.heap header accept = true) :
    construct s accept source scope writable =
      some (⟨constructed s.heap view.header header scope writable,
        s.views++[⟨s.heap.headers.length,writable⟩]⟩,s.views.length) := by
  have hp := resolve_parts s source view header found
  have core := move_construct_runs s.heap accept view.header scope header writable hp.2.1 (hp.2.2 permission) valid
  simp [construct,found,permission,core]

theorem construct_success (s out : State α) (accept : α → Bool) (source scope slot : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) :
    ∃ view header destination, resolve s source = some (view,header) ∧ view.writable = true ∧
      moveConstruct s.heap accept view.header scope writable = some (out.heap,destination) ∧
      out.views = s.views++[⟨destination,writable⟩] ∧ slot = s.views.length := by
  unfold construct at run
  cases vf : resolve s source with
  | none => simp [vf] at run
  | some pair =>
    rcases pair with ⟨view,header⟩
    simp only [vf,Bind.bind,Option.bind] at run
    split at run
    next permission =>
      cases core : moveConstruct s.heap accept view.header scope writable with
      | none => simp [core] at run
      | some pair =>
        rcases pair with ⟨heap,destination⟩
        simp only [core] at run
        have eq := Prod.mk.inj (Option.some.inj run)
        rcases eq with ⟨stateEq,slotEq⟩
        subst out
        subst slot
        exact ⟨view,header,destination,rfl,permission,core,rfl,rfl⟩
    next => simp at run

theorem construct_resources (s out : State α) (accept : α → Bool) (source scope slot : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) :
    out.heap.work = s.heap.work+1 ∧ out.heap.liveSpace = s.heap.liveSpace+1 ∧
      out.heap.peak = max s.heap.peak (out.heap.liveSpace-s.heap.baseSpace) ∧
      out.heap.baseSpace = s.heap.baseSpace := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := construct_success s out accept source scope slot writable run
  exact move_construct_resources s.heap out.heap accept view.header scope destination writable core

theorem construct_read (s out : State α) (accept : α → Bool) (source scope slot reference : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) :
    read out accept reference = read s accept reference := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := construct_success s out accept source scope slot writable run
  exact move_construct_read s.heap out.heap accept view.header scope destination writable core reference


-- Capturing only appends a grant. It neither copies nor moves vector storage.
theorem capture_core_success (s out : Heap α) (accept : α → Bool) (headerId : Nat)
    (index : Int) (writable : Bool) (reference : Nat)
    (run : Proofs.CppMoveHeaders.capture s accept headerId index writable = some (out,reference)) :
    ∃ grant : Grant, out = {s with grants := s.grants++[grant]} ∧ reference = s.grants.length := by
  unfold Proofs.CppMoveHeaders.capture at run
  cases hf : s.header headerId with
  | none => simp [hf] at run
  | some header =>
    simp only [hf,Bind.bind,Option.bind] at run
    split at run
    next permission =>
      cases ownerFound : header.allocation with
      | none => simp [ownerFound] at run
      | some owner =>
        cases trackedFound : s.allocation owner with
        | none => simp [ownerFound,trackedFound] at run
        | some tracked =>
          simp only [ownerFound,trackedFound] at run
          split at run
          next compatible =>
            cases refFound : Proofs.CppVectorCopyAssign.reference tracked accept index with
            | none => simp [refFound] at run
            | some ref =>
              simp only [refFound] at run
              have eq := Prod.mk.inj (Option.some.inj run)
              exact ⟨⟨ref,writable⟩,eq.1.symm,eq.2.symm⟩
          next => simp at run
    next => simp at run

theorem capture_success (s out : State α) (accept : α → Bool) (slot : Nat) (index : Int)
    (writable : Bool) (reference : Nat)
    (run : capture s accept slot index writable = some (out,reference)) :
    ∃ view header, resolve s slot = some (view,header) ∧
      (writable = true → view.writable = true) ∧
      Proofs.CppMoveHeaders.capture s.heap accept view.header index writable = some (out.heap,reference) ∧
      out.views = s.views := by
  unfold capture at run
  cases vf : resolve s slot with
  | none => simp [vf] at run
  | some pair =>
    rcases pair with ⟨view,header⟩
    simp only [vf,Bind.bind,Option.bind] at run
    split at run
    next permission =>
      cases core : Proofs.CppMoveHeaders.capture s.heap accept view.header index writable with
      | none => simp [core] at run
      | some pair =>
        rcases pair with ⟨heap,id⟩
        simp only [core] at run
        have eq := Prod.mk.inj (Option.some.inj run)
        rcases eq with ⟨stateEq,refEq⟩
        subst out
        subst reference
        exact ⟨view,header,rfl,permission,core,rfl⟩
    next => simp at run

theorem capture_metadata (s out : State α) (accept : α → Bool) (slot : Nat) (index : Int)
    (writable : Bool) (reference : Nat)
    (run : capture s accept slot index writable = some (out,reference)) :
    out.heap.headers = s.heap.headers ∧ out.heap.allocations = s.heap.allocations ∧
      out.heap.work = s.heap.work ∧ out.heap.peak = s.heap.peak ∧
      out.heap.baseSpace = s.heap.baseSpace ∧ out.views = s.views := by
  obtain ⟨view,header,_,_,core,views⟩ := capture_success s out accept slot index writable reference run
  obtain ⟨grant,heapEq,_⟩ := capture_core_success s.heap out.heap accept view.header index writable reference core
  rw [heapEq]
  exact ⟨rfl,rfl,rfl,rfl,rfl,views⟩

theorem capture_read_old (s out : State α) (accept : α → Bool) (slot : Nat) (index : Int)
    (writable : Bool) (reference old : Nat) (grant : Grant)
    (run : capture s accept slot index writable = some (out,reference))
    (found : s.heap.grants[old]? = some grant) : read out accept old = read s accept old := by
  obtain ⟨view,header,_,_,core,_⟩ := capture_success s out accept slot index writable reference run
  obtain ⟨new,heapEq,_⟩ := capture_core_success s.heap out.heap accept view.header index writable reference core
  unfold read Proofs.CppMoveHeaders.read
  rw [heapEq]
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.getElem?_append_left inside]
  rfl


theorem capture_resolve (s out : State α) (accept : α → Bool) (slot : Nat) (index : Int)
    (writable : Bool) (reference other : Nat)
    (run : capture s accept slot index writable = some (out,reference)) :
    resolve out other = resolve s other := by
  obtain ⟨headers,_,_,_,_,views⟩ := capture_metadata s out accept slot index writable reference run
  simp only [resolve,Heap.header,headers,views]

theorem construct_unique (s out : State α) (accept : α → Bool) (source scope slot : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) (unique : Unique s.heap) :
    Unique out.heap := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := construct_success s out accept source scope slot writable run
  exact move_construct_unique s.heap out.heap accept view.header scope destination writable unique core

theorem construct_ownsAll (s out : State α) (accept : α → Bool) (source scope slot : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) (covered : OwnsAll s.heap) :
    OwnsAll out.heap := by
  obtain ⟨view,header,destination,_,_,core,_,_⟩ := construct_success s out accept source scope slot writable run
  exact move_construct_ownsAll s.heap out.heap accept view.header scope destination writable covered core


theorem construct_destination (s out : State α) (accept : α → Bool) (source scope slot : Nat) (writable : Bool)
    (run : construct s accept source scope writable = some (out,slot)) :
    ∃ header : Header, resolve out slot = some (⟨s.heap.headers.length,writable⟩,
      ⟨header.allocation,scope,writable,header.limit⟩) := by
  obtain ⟨view,header,destination,_,_,core,views,slotEq⟩ :=
    construct_success s out accept source scope slot writable run
  obtain ⟨old,_,destinationEq,heapEq⟩ :=
    move_construct_success s.heap out.heap accept view.header scope destination writable core
  refine ⟨old,?_⟩
  apply resolve_runs
  · rw [views,slotEq,destinationEq]
    simp
  · rw [heapEq]
    exact constructed_target s.heap view.header old scope writable
  · intro permission
    exact permission

end Proofs.CppMoveViews
