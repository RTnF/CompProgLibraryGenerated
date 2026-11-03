import Proofs.CppConstructionFootprint
import Proofs.CppConstructorFinish

namespace Proofs.CppConstructionRetire
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppConstructionFootprint

-- Descendants only follow earlier owners, so equal prefixes have equal contexts.
theorem context_prefix (f g : Forest) (bound : Nat)
    (same : ∀ i, i < bound → g.lookup i = f.lookup i) (owner : Nat) (inside : owner < bound) :
    g.context owner = f.context owner := by
  induction owner using Nat.strongRecOn with
  | ind owner ih =>
    have lookup := same owner inside
    cases found : f.lookup owner with
    | none =>
      have missing : g.lookup owner = none := lookup.trans found
      have rf : f.rootOwner owner = none := by rw [Forest.rootOwner]; simp [found]
      have rg : g.rootOwner owner = none := by rw [Forest.rootOwner]; simp [missing]
      simp [Forest.context,rf,rg]
    | some tag =>
      have updated : g.lookup owner = some tag := lookup.trans found
      cases hp : tag.parent with
      | none =>
        simp [Forest.context,root_runs f owner tag found hp,root_runs g owner tag updated hp,found,updated]
      | some parent =>
        by_cases earlier : parent < owner
        · rw [context_child g owner parent tag updated hp earlier,context_child f owner parent tag found hp earlier]
          exact ih parent earlier (by omega)
        · have wrong : owner ≤ parent := by omega
          simp [Forest.context,invalid_parent_fails g owner parent tag updated hp wrong,
            invalid_parent_fails f owner parent tag found hp wrong]

def settled (s : State) (ty : Ty) (scope count : Nat) (x : Int) : State :=
  let grown := filledState s ty (scope+1) count x
  ({grown with forest := (grown.forest.transferred s.storage.objects.length scope
    (Proofs.DynamicTransfer.tagOf (.flat ty (scope+1) (List.replicate count x))))} : State).retired (scope+1)

theorem settled_old (s : State) (ty : Ty) (scope count : Nat) (x : Int)
    (lengths : s.forest.objects.length = s.storage.objects.length)
    (owner : Nat) (inside : owner < s.storage.objects.length)
    (kept : s.forest.context owner ≠ some (scope+1)) :
    (settled s ty scope count x).storage.lookup owner = s.storage.lookup owner ∧
    (settled s ty scope count x).forest.lookup owner = s.forest.lookup owner := by
  let grown := filledState s ty (scope+1) count x
  let moved : State := {grown with forest := (grown.forest.transferred s.storage.objects.length scope
    (Proofs.DynamicTransfer.tagOf (.flat ty (scope+1) (List.replicate count x))))}
  have oldTag (i : Nat) (bound : i < s.storage.objects.length) : moved.forest.lookup i = s.forest.lookup i := by
    change (grown.forest.transferred s.storage.objects.length scope _).lookup i = _
    rw [transferred_lookup_other grown.forest s.storage.objects.length i scope _ (by omega)]
    exact filled_old_tag s ty (scope+1) count x i (by omega)
  have contextEq := context_prefix s.forest moved.forest s.storage.objects.length oldTag owner inside
  have keepMoved : moved.forest.context owner ≠ some (scope+1) := by rw [contextEq]; exact kept
  refine ⟨?_,?_⟩
  · change (moved.retired (scope+1)).storage.lookup owner = _
    rw [retired_kept moved (scope+1) owner keepMoved]
    exact filled_old s ty (scope+1) count x owner inside
  · change (moved.forest.retired (scope+1)).lookup owner = _
    rw [retired_other_context moved.forest (scope+1) owner keepMoved]
    exact oldTag owner inside

theorem settled_new (s : State) (ty : Ty) (scope count : Nat) (x : Int)
    (lengths : s.forest.objects.length = s.storage.objects.length) :
    (settled s ty scope count x).storage.lookup s.storage.objects.length =
      some ⟨s.storage.objects.length,List.replicate count (Proofs.CppNestedVectorStore.Value.integer x),count,
        Proofs.CppVectorBindings.sizeLimit ty,0⟩ := by
  let grown := filledState s ty (scope+1) count x
  let tag := Proofs.DynamicTransfer.tagOf (.flat ty (scope+1) (List.replicate count x))
  let moved : State := {grown with forest := grown.forest.transferred s.storage.objects.length scope tag}
  have found : grown.forest.lookup s.storage.objects.length = some tag := by
    change (s.forest.declareRoot ty (scope+1)).lookup s.storage.objects.length = _
    rw [← lengths,Proofs.CppNestedConstruct.declareRoot_new]
    rfl
  have nextTag : moved.forest.lookup s.storage.objects.length = some {tag with scope := some scope} :=
    transferred_lookup_root grown.forest s.storage.objects.length scope tag found
  have rootRun := root_runs moved.forest s.storage.objects.length {tag with scope := some scope} nextTag rfl
  have contextEq : moved.forest.context s.storage.objects.length = some scope := by
    simp [Forest.context,rootRun,nextTag]
  change (moved.retired (scope+1)).storage.lookup s.storage.objects.length = _
  rw [retired_kept moved (scope+1) s.storage.objects.length (by rw [contextEq]; simp)]
  exact filled_new s ty (scope+1) count x

-- Recover the concrete frame of any successful constructor finish.
theorem finish_frame (caller callee out : Proofs.CppNestedProgram.NState)
    (vectorSlot index : Nat) (element : Element)
    (fields : List Proofs.CppConstructorFinish.ScalarField)
    (reference : Proofs.CppConstructorFinish.ObjectRef)
    (binding : Proofs.CppNestedVectorBindings.Binding) (view : Proofs.CppRootModel.View)
    (slot : callee.vectorSlot vectorSlot = some index) (found : callee.frame.bindings[index]? = some binding)
    (model : Proofs.CppRootModel.Models callee.frame.state binding.owner view)
    (viewElement : view.element = element) (viewScope : view.scope = callee.scope)
    (actual : Proofs.CppConstructorFinish.finish caller callee vectorSlot element fields = some (out,reference)) :
    out.frame.state = (Proofs.DynamicTransfer.movedFrame callee.frame binding.owner caller.scope view).state.retired callee.scope ∧
      out.frame.rootWritable = callee.frame.rootWritable ∧
      out.frame.bindings = caller.frame.bindings ++ [⟨binding.owner,binding.element,binding.writable,.root caller.scope⟩] := by
  have moved := Proofs.DynamicTransfer.frame_runs callee.frame binding.owner caller.scope view model
  rw [viewElement,viewScope] at moved
  have retired := Proofs.DynamicRetire.frame_runs
    (Proofs.DynamicTransfer.movedFrame callee.frame binding.owner caller.scope view) callee.scope
    (Proofs.DynamicTransfer.Models.moved model caller.scope).valid
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · simp only [slot,found,Bind.bind,Option.bind] at actual
    split at actual
    · obtain ⟨values,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
      simp only [moved,retired,Option.bind_some] at rest
      have same := (Prod.mk.inj (Option.some.inj rest)).1
      subst out
      exact ⟨rfl,rfl,rfl⟩
    · simp at actual
  · simp at actual

end Proofs.CppConstructionRetire
