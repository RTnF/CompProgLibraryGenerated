import Proofs.DynamicPrepareExists
import Proofs.DynamicScopeAuto

namespace Proofs.DynamicFinish
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedScope
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.MultiVecDynamicScope
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes

-- Contents may change while each existing root retains its type and scope.
def shape : Contents → Proofs.CppVectorOwnership.Element × Nat
  | .flat ty sc _ => (.integer ty,sc)
  | .rows ty sc _ => (.vector (.integer ty),sc)

def SameShape (before after : ContentsHeap) : Prop :=
  ∀ owner, (after owner).map shape = (before owner).map shape

theorem SameShape.refl (h : ContentsHeap) : SameShape h h := fun _ => rfl

theorem SameShape.trans {a b c : ContentsHeap} (ab : SameShape a b) (bc : SameShape b c) : SameShape a c :=
  fun owner => (bc owner).trans (ab owner)

theorem same_put (h : ContentsHeap) (root : Nat) (old new : Contents)
    (found : h root = some old) (equal : shape new = shape old) : SameShape h (putContents h root new) := by
  intro owner
  by_cases same : owner = root
  · subst owner; simp [putContents,found,equal]
  · simp [putContents,same]

theorem appendRoot_shape (h next : ContentsHeap) (root : Nat) (ty : Ty)
    (run : DynamicContents.appendRoot h root ty = some next) : SameShape h next := by
  cases found : h root with
  | none => simp [DynamicContents.appendRoot,found] at run
  | some c =>
    cases c with
    | flat _ _ _ => simp [DynamicContents.appendRoot,found] at run
    | rows t sc vs =>
      by_cases equal : t = ty
      · simp only [DynamicContents.appendRoot,found,Bind.bind,Option.bind,equal,ite_true,Option.some.injEq] at run
        subst next; exact same_put h root _ _ found (by simp [shape,equal])
      · simp [DynamicContents.appendRoot,found,equal] at run

theorem appendChild_shape (h next : ContentsHeap) (root : Nat) (ty : Ty) (k : Nat) (x : Int)
    (run : DynamicContents.appendChild h root ty k x = some next) : SameShape h next := by
  cases found : h root with
  | none => simp [DynamicContents.appendChild,found] at run
  | some c =>
    cases c with
    | flat _ _ _ => simp [DynamicContents.appendChild,found] at run
    | rows t sc vs =>
      cases row : vs[k]? with
      | none => simp [DynamicContents.appendChild,found,row] at run
      | some old =>
        simp only [DynamicContents.appendChild,found,row,Bind.bind,Option.bind] at run
        split at run
        · have same := Option.some.inj run
          subst next; exact same_put h root _ _ found rfl
        · contradiction

theorem erase_shape (v : View) : shape (erase v) = (v.element,v.scope) := by cases v <;> rfl

theorem views_of_shape {params : List Parameter} {old new : Heap} {f : Proofs.CppNestedVectorBindings.Frame} {m : Resources}
    (family : Family params old f m) (same : SameShape (eraseHeap old) (eraseHeap new)) :
    ∀ p ∈ params, ∃ v, new p.owner = some v ∧ v.element = p.element ∧ v.scope = p.scope := by
  intro p member
  obtain ⟨v,found,element,scope⟩ := family.views p member
  have shaped := same p.owner
  cases next : new p.owner with
  | none => simp [eraseHeap,next,found] at shaped
  | some w =>
    have equal : (w.element,w.scope) = (v.element,v.scope) := by
      simpa [eraseHeap,next,found,erase_shape] using shaped
    exact ⟨w,rfl,(Prod.mk.inj equal).1.trans element,(Prod.mk.inj equal).2.trans scope⟩

def resultValue : ResultKind → Option Int → Option Ret
  | .scalar ty,some value => if ty.valid value then some (.scalar value) else none
  | .unit,none => some .unit
  | _,_ => none

def finish (outer inner : DynamicStmt.State) (kind : ResultKind) (returned : Option Int) : Option (DynamicStmt.State × Ret) := do
  let restored ← DynamicControl.leave outer inner
  let value ← resultValue kind returned
  some (restored,value)

-- Unlike lexical leave, the caller's vector bindings replace the callee list.
def restored (caller callee : NState) : NState :=
  let scalars : Proofs.CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length,
    work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
  let frame := {noopRetired callee.frame with bindings := caller.frame.bindings}
  (⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak callee.peak⟩ : NState).observe

theorem restored_peak (caller callee : NState)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length) :
    (restored caller callee).peak = max (max caller.peak callee.peak)
      (max (max caller.scalars.peak callee.scalars.peak) (Proofs.CppNestedEval.liveS caller)+
        max callee.frame.state.storage.peak (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace)) := by
  have length : (callee.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
    simp [List.length_take,Nat.min_eq_left fits]
  change max (max caller.peak callee.peak)
    (max (max caller.scalars.peak callee.scalars.peak)
      ((callee.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+caller.scalars.bindings.length+0)+_) = _
  rw [length]
  rfl

theorem finish_eq (caller callee : NState) (kind : ResultKind) (returned : Option Int) (value : Ret)
    (accepted : resultValue kind returned = some value)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type = caller.scalars.memory.map Proofs.CppState.Cell.type)
    (valid : callee.frame.state.wellFormed = true)
    (fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope) :
    CppNestedCall.finish caller callee kind (returned.map Ret.scalar) = some (restored caller callee,value) := by
  have retire := retireScope_fresh callee.frame callee.scope valid fresh
  cases kind with
  | vector _ => simp [resultValue] at accepted
  | unit =>
    cases returned with
    | some _ => simp [resultValue] at accepted
    | none =>
      have same : Ret.unit = value := Option.some.inj accepted
      subst value
      simp [CppNestedCall.finish,fits,types,retire,restored]
  | scalar ty =>
    cases returned with
    | none => simp [resultValue] at accepted
    | some x =>
      by_cases good : ty.valid x = true
      · have same : Ret.scalar x = value := by simpa [resultValue,good] using accepted
        subst value
        simp [CppNestedCall.finish,fits,types,good,retire,restored]
      · simp [resultValue,good] at accepted

theorem rebound_family {params calleeParams : List Parameter} {old new : Heap} {caller callee : NState} {m0 m : Resources}
    (before : Family params old caller.frame m0) (after : Family calleeParams new callee.frame m)
    (same : SameShape (eraseHeap old) (eraseHeap new))
    (flags : ∃ extra, callee.frame.rootWritable = caller.frame.rootWritable ++ extra) :
    Family params new {callee.frame with bindings := caller.frame.bindings} m := by
  obtain ⟨extra,rights⟩ := flags
  refine ⟨after.valid,after.models,after.lengths,before.bindings,?_,before.permissions,views_of_shape before same,?_⟩
  · intro p member
    have found := before.flags p member
    rw [rights,List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · exact ⟨after.measured.live,after.measured.work,after.measured.peak,after.measured.count,after.measured.base⟩

theorem sound (params calleeParams : List Parameter) (outer inner final : DynamicStmt.State) (caller callee : NState)
    (before : Realizes params outer.locals outer.contents caller)
    (after : Realizes calleeParams inner.locals inner.contents callee)
    (kind : ResultKind) (returned : Option Int) (value : Ret)
    (pure : finish outer inner kind returned = some (final,value))
    (same : SameShape outer.contents inner.contents)
    (flags : ∃ extra, callee.frame.rootWritable = caller.frame.rootWritable ++ extra)
    (fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope) :
    CppNestedCall.finish caller callee kind (returned.map Ret.scalar) = some (restored caller callee,value) ∧
      Realizes params final.locals final.contents (restored caller callee) ∧
      (restored caller callee).work = callee.work+1 := by
  obtain ⟨left,leftRun,rest⟩ := DynamicResultValid.bind_some _ _ _ pure
  obtain ⟨ret,retRun,result⟩ := DynamicResultValid.bind_some _ _ _ rest
  have pairs := Prod.mk.inj (Option.some.inj result)
  obtain ⟨rfl,rfl⟩ := pairs
  obtain ⟨fits,types,fields⟩ := DynamicScopeAuto.leave_fields outer inner left leftRun
  have sm := congrArg Locals.memory before.locals
  have tm := congrArg Locals.memory after.locals
  change caller.scalars.memory = outer.locals.memory at sm
  change callee.scalars.memory = inner.locals.memory at tm
  have fits' : caller.scalars.memory.length ≤ callee.scalars.memory.length := by rw [sm,tm]; exact fits
  have types' : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type = caller.scalars.memory.map Proofs.CppState.Cell.type := by rw [sm,tm]; exact types
  obtain ⟨old,m0,oldFamily,oldErase⟩ := before.heap
  obtain ⟨new,m,newFamily,newErase⟩ := after.heap
  have shaped : SameShape (eraseHeap old) (eraseHeap new) := by rw [oldErase,newErase]; exact same
  have family := rebound_family oldFamily newFamily shaped flags
  have retired := Family.noopRetired family
  refine ⟨finish_eq caller callee kind returned ret retRun fits' types' newFamily.valid fresh,?_,?_⟩
  · subst left
    refine ⟨?_,new,observed m,retired,newErase⟩
    have sb := congrArg Locals.bindings before.locals
    have ss := congrArg Locals.slots before.locals
    change caller.scalars.bindings = outer.locals.bindings at sb
    change caller.slots = outer.locals.slots at ss
    change (⟨callee.scalars.memory.take caller.scalars.memory.length,caller.scalars.bindings,caller.slots⟩ : Locals) = _
    rw [sm,tm,sb,ss]
  · change callee.scalars.work+1+callee.frame.state.storage.work = callee.scalars.work+callee.frame.state.storage.work+1
    omega

end Proofs.DynamicFinish
