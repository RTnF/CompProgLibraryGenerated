import Proofs.DynamicOwnedLayout

namespace Proofs.CppConstructionFootprint
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppVectorStore
open Proofs.CppNestedConstruct Proofs.CppNestedStmt Proofs.CppNestedEval
open Proofs.DynamicResultValid

def installed (f : Frame) (next : State) (ty : Ty) (wr : Bool) (scope : Nat) : Frame :=
  ⟨next,f.rootWritable++[wr],f.bindings++[⟨f.state.storage.objects.length,.integer ty,wr,.root scope⟩]⟩

def emptyState (s : State) (ty : Ty) (scope : Nat) : State :=
  ⟨s.forest.declareRoot ty scope,{s.storage with
    objects := s.storage.objects++[some (flatBuffer ty s.storage.objects.length)],
    work := s.storage.work+1,
    peak := max s.storage.peak (s.liveSpace+1-s.storage.baseSpace)}⟩

def filledState (s : State) (ty : Ty) (scope count : Nat) (x : Int) : State :=
  ⟨s.forest.declareRoot ty scope,{s.storage with
    objects := s.storage.objects++[some ⟨s.storage.objects.length,List.replicate count (.integer x),count,
      Proofs.CppVectorBindings.sizeLimit ty,0⟩],
    work := s.storage.work+(count+1),
    peak := max s.storage.peak (s.liveSpace+(count+2)-s.storage.baseSpace)}⟩

theorem bind_exact (f frame : Frame) (owner : Nat) (element : Element) (scope : Nat)
    (wr : Bool) (index : Nat) (run : f.bindRoot owner element scope wr = some (frame,index)) :
    frame = {f with bindings := f.bindings++[⟨owner,element,wr,.root scope⟩]} ∧ index = f.bindings.length := by
  unfold Frame.bindRoot at run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨buffer,tag⟩ := pair
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  split at rest
  · have same := Prod.mk.inj (Option.some.inj rest)
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨rfl,rfl⟩
  · contradiction

theorem empty_layout (s : NState) (ty : Ty) (wr : Bool) (out : NStep)
    (actual : (NStmt.declareVector ty wr).run s = some out) :
    out.state.frame = installed s.frame (emptyState s.frame.state ty s.scope) ty wr s.scope := by
  unfold NStmt.run at actual
  obtain ⟨next,allocated,rest⟩ := bind_some _ _ _ actual
  obtain ⟨pair,bound,same⟩ := bind_some _ _ _ rest
  obtain ⟨frame,index⟩ := pair
  have equal := Option.some.inj same
  subst out
  obtain ⟨_,_,nextEq⟩ := declareVector_inv s.frame.state ty s.scope next allocated
  obtain ⟨frameEq,_⟩ := bind_exact _ frame s.frame.state.storage.objects.length (.integer ty) s.scope wr index bound
  change frame = _
  rw [frameEq,nextEq]
  rfl

theorem fill_layout (s : NState) (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (scalarCount : count.scalarOnly = true) (scalarValue : value.scalarOnly = true)
    (countValue : count.denote (envOf s) = some n) (valueValue : value.denote (envOf s) = some x)
    (out : NStep) (actual : (NStmt.fillVector ty wr count value).run s = some out) :
    out.state.frame = installed s.frame (filledState s.frame.state ty s.scope n.toNat x) ty wr s.scope := by
  obtain ⟨t1,ev1,good1⟩ := scalar_eval count s n scalarCount countValue
  have env1 : envOf t1 = envOf s := envOf_core good1.1
  obtain ⟨t2,ev2,good2⟩ := scalar_eval value t1 x scalarValue (by rw [env1]; exact valueValue)
  have core : Core s t2 := good1.1.trans good2.1
  have frameEq : (t2.release s).frame = s.frame := by
    change (⟨t2.frame.state,t2.frame.rootWritable,t2.frame.bindings.take s.frame.bindings.length⟩ : Frame) = s.frame
    rw [core.1]
    simp
  have scopeEq : (t2.release s).scope = s.scope := core.2.2.1
  simp only [NStmt.run,ev1,ev2,Bind.bind,Option.bind] at actual
  split at actual
  · obtain ⟨next,allocated,rest⟩ := bind_some _ _ _ actual
    obtain ⟨pair,bound,same⟩ := bind_some _ _ _ rest
    obtain ⟨frame,index⟩ := pair
    have equal := Option.some.inj same
    subst out
    rw [frameEq,scopeEq] at allocated bound
    obtain ⟨_,_,_,_,nextEq⟩ := fillVector_inv s.frame.state ty s.scope n.toNat x next allocated
    obtain ⟨installedEq,_⟩ := bind_exact _ frame s.frame.state.storage.objects.length (.integer ty) s.scope wr index bound
    change frame = _
    rw [installedEq,nextEq]
    rfl
  · simp at actual

-- Exact buffer equality preserves capacity, limit, epoch and outstanding element references.
theorem filled_old (s : State) (ty : Ty) (scope count : Nat) (x : Int) (owner : Nat)
    (inside : owner < s.storage.objects.length) :
    (filledState s ty scope count x).storage.lookup owner = s.storage.lookup owner := by
  simp [filledState,Store.lookup,List.getElem?_append_left inside]

theorem filled_new (s : State) (ty : Ty) (scope count : Nat) (x : Int) :
    (filledState s ty scope count x).storage.lookup s.storage.objects.length =
      some ⟨s.storage.objects.length,List.replicate count (.integer x),count,
        Proofs.CppVectorBindings.sizeLimit ty,0⟩ := by
  simp [filledState,Store.lookup]

theorem filled_old_tag (s : State) (ty : Ty) (scope count : Nat) (x : Int) (owner : Nat)
    (inside : owner < s.forest.objects.length) :
    (filledState s ty scope count x).forest.lookup owner = s.forest.lookup owner :=
  declareRoot_old s.forest ty scope owner inside

theorem empty_old (s : State) (ty : Ty) (scope owner : Nat)
    (inside : owner < s.storage.objects.length) :
    (emptyState s ty scope).storage.lookup owner = s.storage.lookup owner := by
  simp [emptyState,Store.lookup,List.getElem?_append_left inside]

theorem empty_new (s : State) (ty : Ty) (scope : Nat) :
    (emptyState s ty scope).storage.lookup s.storage.objects.length =
      some (flatBuffer ty s.storage.objects.length) := by
  simp [emptyState,Store.lookup]

end Proofs.CppConstructionFootprint
