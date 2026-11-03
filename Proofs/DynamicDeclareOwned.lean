import Proofs.DynamicAllocateFamily

namespace Proofs.DynamicDeclareOwned
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVectorStore Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedConstruct Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicRealizes Proofs.DynamicAllocateFamily

def parameter (s : NState) (ty : Ty) (wr : Bool) : Parameter :=
  ⟨s.frame.bindings.length,s.frame.state.storage.objects.length,.integer ty,s.scope,wr,wr⟩

theorem sound (params : List Parameter) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (ty : Ty) (wr : Bool) (supported : Proofs.CppVectorBindings.supported ty) :
    ∃ out, (NStmt.declareVector ty wr).run s = some ⟨out,none,false⟩ ∧
      Family (params ++ [parameter s ty wr]) (put h s.frame.state.storage.objects.length (.flat ty s.scope [])) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s ty wr]) (snapshot out)
        (putContents (eraseHeap h) s.frame.state.storage.objects.length (.flat ty s.scope [])) out ∧
      out.scope = s.scope ∧ out.work = s.work+2 := by
  let next : State := ⟨s.frame.state.forest.declareRoot ty s.scope,
    {s.frame.state.storage with
      objects := s.frame.state.storage.objects ++ [some (flatBuffer ty s.frame.state.storage.objects.length)],
      work := s.frame.state.storage.work+1,
      peak := max s.frame.state.storage.peak (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)}⟩
  have allocated : s.frame.state.declareVector ty s.scope = some next := by
    simp [State.declareVector,family.valid,supported,next]
  have base := DynamicAllocateFamily.empty family next ty s.scope wr allocated
  have flag := new_flag family next wr 0
  obtain ⟨frame,bound,post⟩ := register base s.frame.state.storage.objects.length (.flat ty s.scope []) (by simp [put]) wr flag
  have frameState : frame.state = next := by
    obtain ⟨_,_,_,frameEq,_⟩ := DynamicFamilyInit.bind_root (s := (⟨s.scalars,grown s.frame next wr 0,s.slots,s.scope,s.peak⟩ : NState)) base s.frame.state.storage.objects.length s.scope (.integer ty) wr (.flat ty s.scope []) (by simp [put]) rfl rfl frame s.frame.bindings.length bound
    rw [frameEq]; rfl
  let out := ({s with frame := frame,slots := s.slots ++ [.vector s.frame.bindings.length]} : NState).charge 1 0
  have post' : Family (params ++ [parameter s ty wr]) (put h s.frame.state.storage.objects.length (.flat ty s.scope [])) out.frame (resources out.frame) := by
    exact Family.remeasured post
  have bound' : ({s.frame with state := next,rootWritable := s.frame.rootWritable ++ [wr]} : Frame).bindRoot s.frame.state.storage.objects.length (.integer ty) s.scope wr = some (frame,s.frame.bindings.length) := by
    simpa only [grown,List.replicate_zero,List.append_nil,View.element,View.scope] using bound
  refine ⟨out,?_,post',?_,rfl,?_⟩
  · simp [NStmt.run,allocated,bound',out]
  · refine ⟨rfl,_,_,post',?_⟩
    rw [erase_put]; rfl
  · change s.scalars.work+1+frame.state.storage.work = s.scalars.work+s.frame.state.storage.work+2
    rw [frameState]
    change s.scalars.work+1+(s.frame.state.storage.work+1) = _
    omega

end Proofs.DynamicDeclareOwned
