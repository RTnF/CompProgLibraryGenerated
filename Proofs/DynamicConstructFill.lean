import Proofs.DynamicConstructRows

namespace Proofs.DynamicConstructFill
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVectorStore Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedConstruct Proofs.CppNestedStmt Proofs.CppNestedEval Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicContents
open Proofs.DynamicConstructCore Proofs.DynamicAllocateFamily

theorem sound_full (params : List Parameter) (h : Heap) (m : Resources) (l : Locals) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params l (eraseHeap h) s)
    (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (countPure : denote params l (eraseHeap h) count = some n)
    (valuePure : denote params l (eraseHeap h) value = some x)
    (nonnegative : 0 ≤ n) (supported : Proofs.CppVectorBindings.supported ty)
    (limit : n.toNat ≤ Proofs.CppVectorBindings.sizeLimit ty) (accepted : ty.valid x = true) :
    ∃ out, (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩ ∧
      Family (params ++ [parameter s (.integer ty) wr])
        (put h s.frame.state.storage.objects.length (.flat ty s.scope (List.replicate n.toNat x))) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s (.integer ty) wr]) (appended l s.frame.bindings.length)
        (putContents (eraseHeap h) s.frame.state.storage.objects.length (.flat ty s.scope (List.replicate n.toNat x))) out ∧
      out.scope = s.scope ∧ out.work ≤ s.work+2*count.nodes+2*value.nodes+n.toNat+4 ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes+2*value.nodes)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)) ∧
      out.frame.bindings.length = s.frame.bindings.length+1 ∧
      out.frame.state.storage.objects.length = s.frame.state.storage.objects.length+1 := by
  obtain ⟨_,t1,extra1,ev1⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) n countPure) s real
  have real1 := DynamicExprCompose.in_extension params l (eraseHeap h) s t1 real (Ext.of_goodF ev1.2.1 ev1.2.2)
  obtain ⟨_,t2,extra2,ev2⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) x valuePure) t1 real1
  have good : GoodF s t2 (2*count.nodes+2*value.nodes) (2*count.nodes+2*value.nodes) :=
    (ev1.2.1.trans ev2.2.1).mono (by omega) (by omega)
  have allBindings : t2.frame.bindings = s.frame.bindings ++ (extra1 ++ extra2) := by
    rw [ev2.2.2,ev1.2.2,List.append_assoc]
  let released := t2.release s
  have before : Family params h released.frame m := release_family family good _ allBindings
  have rb : released.frame.bindings = s.frame.bindings := DynamicConstructCore.release_bindings s t2 _ allBindings
  have rs : released.frame.state = s.frame.state := good.1
  have sc : released.scope = s.scope := good.2.2.2.1
  have snap : snapshot released = l := (ev_preserves params l (eraseHeap h) t1 t2 real1 value x extra2 _ _ ev2).1.locals
  let next : State := ⟨s.frame.state.forest.declareRoot ty s.scope,
    {s.frame.state.storage with
      objects := s.frame.state.storage.objects ++ [some ⟨s.frame.state.storage.objects.length,List.replicate n.toNat (Value.integer x),n.toNat,Proofs.CppVectorBindings.sizeLimit ty,0⟩],
      work := s.frame.state.storage.work+(n.toNat+1),
      peak := max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)}⟩
  have allocated : released.frame.state.fillVector ty released.scope n.toNat x = some next := by
    rw [rs,sc]; simp [State.fillVector,family.valid,supported,limit,accepted,next]
  have base := DynamicAllocateFamily.filled before next ty released.scope n.toNat x wr allocated
  obtain ⟨frame,out,bound,defined,post,matched,snapOut,scopeOut,workOut,peakOut,outState,bindingCount⟩ := install_full params h m released before next _ wr 0 rfl base
  have bound' : ({released.frame with state := next,rootWritable := released.frame.rootWritable ++ [wr]} : Frame).bindRoot released.frame.state.storage.objects.length (.integer ty) released.scope wr = some (frame,released.frame.bindings.length) := by
    simpa only [grown,List.replicate_zero,List.append_nil,View.element] using bound
  have ran : (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩ := by
    simp only [NStmt.run,ev1.1,Bind.bind,Option.bind,ev2.1,if_pos nonnegative]
    change (released.frame.state.fillVector ty released.scope n.toNat x).bind _ = _
    rw [allocated,Option.bind_some]
    change (({released.frame with state := next,rootWritable := released.frame.rootWritable ++ [wr]} : Frame).bindRoot released.frame.state.storage.objects.length (.integer ty) released.scope wr).bind _ = _
    rw [bound',Option.bind_some,defined]
  have descriptor : parameter released (.integer ty) wr = parameter s (.integer ty) wr := by simp only [parameter,rs,sc,rb]
  simp only [View.element] at post matched
  rw [descriptor] at post matched
  simp only [rs,sc] at post matched
  rw [snap,rb] at snapOut
  rw [snapOut,erase_put] at matched
  refine ⟨out,ran,post,matched,scopeOut.trans sc,?_,?_,?_,?_⟩
  · have upper := good.2.2.2.2.2.2.2.2.1
    rw [workOut]
    change t2.scalars.work+3+(s.frame.state.storage.work+(n.toNat+1)) ≤ s.scalars.work+s.frame.state.storage.work+2*count.nodes+2*value.nodes+n.toNat+4
    omega
  · obtain ⟨state,_,_,_,memory,bindings,baseline,_,_,_,scalarPeak,_,peak⟩ := good
    have live := liveS_of_memory memory bindings baseline
    have store : t2.frame.state.storage.peak = s.frame.state.storage.peak := by rw [state]
    rw [store] at peak
    have scalarBound : max t2.scalars.peak (liveS t2) ≤ max s.scalars.peak (liveS s+2*count.nodes+2*value.nodes) := by rw [live]; omega
    have growing : s.frame.state.storage.peak ≤ next.storage.peak := Nat.le_max_left _ _
    rw [peakOut]
    change max t2.peak (max t2.scalars.peak (liveS t2)+next.storage.peak) ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes+2*value.nodes)+next.storage.peak)
    omega
  · rw [bindingCount,rb]
  · rw [outState]
    simp [next]

theorem sound (params : List Parameter) (h : Heap) (m : Resources) (l : Locals) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params l (eraseHeap h) s)
    (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (countPure : denote params l (eraseHeap h) count = some n)
    (valuePure : denote params l (eraseHeap h) value = some x)
    (nonnegative : 0 ≤ n) (supported : Proofs.CppVectorBindings.supported ty)
    (limit : n.toNat ≤ Proofs.CppVectorBindings.sizeLimit ty) (accepted : ty.valid x = true) :
    ∃ out, (NStmt.fillVector ty wr count value).run s = some ⟨out,none,false⟩ ∧
      Family (params ++ [parameter s (.integer ty) wr])
        (put h s.frame.state.storage.objects.length (.flat ty s.scope (List.replicate n.toNat x))) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s (.integer ty) wr]) (appended l s.frame.bindings.length)
        (putContents (eraseHeap h) s.frame.state.storage.objects.length (.flat ty s.scope (List.replicate n.toNat x))) out ∧
      out.scope = s.scope ∧ out.work ≤ s.work+2*count.nodes+2*value.nodes+n.toNat+4 ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes+2*value.nodes)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)) := by
  obtain ⟨out,ran,post,real,scope,work,peak,_⟩ := sound_full params h m l s family real ty wr count value n x countPure valuePure nonnegative supported limit accepted
  exact ⟨out,ran,post,real,scope,work,peak⟩

end Proofs.DynamicConstructFill
