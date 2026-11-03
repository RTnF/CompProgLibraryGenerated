import Proofs.DynamicDeclareOwned

namespace Proofs.DynamicConstructCore
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedStmt Proofs.CppNestedEval Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicAllocateFamily Proofs.DynamicContents

def parameter (s : NState) (element : Element) (wr : Bool) : Parameter :=
  ⟨s.frame.bindings.length,s.frame.state.storage.objects.length,element,s.scope,wr,wr⟩

def appended (l : Locals) (binding : Nat) : Locals := {l with slots := l.slots ++ [.vector binding]}

theorem release_family {params : List Parameter} {h : Heap} {m : Resources} {s t : NState} {w p : Nat}
    (family : Family params h s.frame m) (good : GoodF s t w p) (extra : List Binding)
    (bindings : t.frame.bindings = s.frame.bindings ++ extra) : Family params h (t.release s).frame m := by
  apply family.transport (t.release s).frame (by exact good.1) (by exact good.2.1)
  intro q member
  have found := family.bindings q member
  change (t.frame.bindings.take s.frame.bindings.length)[q.slot]? = _
  rw [List.getElem?_take_of_lt (List.getElem?_eq_some_iff.mp found).1,bindings,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem release_bindings (s t : NState) (extra : List Binding)
    (bindings : t.frame.bindings = s.frame.bindings ++ extra) : (t.release s).frame.bindings = s.frame.bindings := by
  change t.frame.bindings.take s.frame.bindings.length = _
  rw [bindings,List.take_append_length]

-- The common allocation/binding tail of count and fill constructors.
theorem install_full (params : List Parameter) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (next : State) (view : View) (wr : Bool) (children : Nat)
    (scopedView : view.scope = s.scope)
    (allocated : Family params (put h s.frame.state.storage.objects.length view) (grown s.frame next wr children)
      (resources (grown s.frame next wr children))) :
    ∃ frame out, (grown s.frame next wr children).bindRoot s.frame.state.storage.objects.length view.element s.scope wr = some (frame,s.frame.bindings.length) ∧
      out = ({s with frame := frame,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).charge 3 0 ∧
      Family (params ++ [parameter s view.element wr]) (put h s.frame.state.storage.objects.length view) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s view.element wr]) (snapshot out) (eraseHeap (put h s.frame.state.storage.objects.length view)) out ∧
      snapshot out = appended (snapshot s) s.frame.bindings.length ∧ out.scope = s.scope ∧
      out.work = s.scalars.work+3+next.storage.work ∧
      out.peak = max s.peak (max s.scalars.peak (liveS s)+next.storage.peak) ∧
      out.frame.state = next ∧ out.frame.bindings.length = s.frame.bindings.length+1 := by
  obtain ⟨frame,bound,post⟩ := register allocated s.frame.state.storage.objects.length view (by simp [put]) wr (new_flag family next wr children)
  obtain ⟨_,_,_,frameEq,_⟩ := DynamicFamilyInit.bind_root (s := (⟨s.scalars,grown s.frame next wr children,s.slots,s.scope,s.peak⟩ : NState)) allocated _ view.scope view.element wr view (by simp [put]) rfl rfl frame s.frame.bindings.length bound
  have frameState : frame.state = next := by rw [frameEq]; rfl
  rw [scopedView] at bound post
  let out := ({s with frame := frame,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).charge 3 0
  have finalFamily : Family (params ++ [parameter s view.element wr]) (put h s.frame.state.storage.objects.length view) out.frame (resources out.frame) := Family.remeasured post
  refine ⟨frame,out,bound,rfl,finalFamily,of_family _ _ _ out finalFamily,rfl,rfl,?_,?_,frameState,?_⟩
  · change s.scalars.work+3+frame.state.storage.work = _
    rw [frameState]
  · change max s.peak (max s.scalars.peak (liveS s+0)+frame.state.storage.peak) = _
    rw [frameState,Nat.add_zero]
  · change frame.bindings.length = s.frame.bindings.length+1
    rw [frameEq]
    simp [Frame.addBinding,grown]

theorem install (params : List Parameter) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (next : State) (view : View) (wr : Bool) (children : Nat)
    (scopedView : view.scope = s.scope)
    (allocated : Family params (put h s.frame.state.storage.objects.length view) (grown s.frame next wr children)
      (resources (grown s.frame next wr children))) :
    ∃ frame out, (grown s.frame next wr children).bindRoot s.frame.state.storage.objects.length view.element s.scope wr = some (frame,s.frame.bindings.length) ∧
      out = ({s with frame := frame,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).charge 3 0 ∧
      Family (params ++ [parameter s view.element wr]) (put h s.frame.state.storage.objects.length view) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s view.element wr]) (snapshot out) (eraseHeap (put h s.frame.state.storage.objects.length view)) out ∧
      snapshot out = appended (snapshot s) s.frame.bindings.length ∧ out.scope = s.scope ∧
      out.work = s.scalars.work+3+next.storage.work ∧
      out.peak = max s.peak (max s.scalars.peak (liveS s)+next.storage.peak) := by
  obtain ⟨frame,out,ran,defined,post,real,snap,scope,work,peak,_⟩ := install_full params h m s family next view wr children scopedView allocated
  exact ⟨frame,out,ran,defined,post,real,snap,scope,work,peak⟩

end Proofs.DynamicConstructCore
