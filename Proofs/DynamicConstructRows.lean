import Proofs.DynamicConstructCore

namespace Proofs.DynamicConstructRows
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVectorStore Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedConstruct Proofs.CppNestedStmt Proofs.CppNestedEval Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicContents
open Proofs.DynamicConstructCore Proofs.DynamicAllocateFamily

theorem sound_full (params : List Parameter) (h : Heap) (m : Resources) (l : Locals) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params l (eraseHeap h) s)
    (ty : Ty) (wr : Bool) (count : NExpr) (n : Int)
    (pure : denote params l (eraseHeap h) count = some n) (nonnegative : 0 ≤ n)
    (supported : Proofs.CppVectorBindings.supported ty) (limit : n.toNat ≤ rowLimit) :
    ∃ out, (NStmt.constructRows ty wr count).run s = some ⟨out,none,false⟩ ∧
      Family (params ++ [parameter s (.vector (.integer ty)) wr])
        (put h s.frame.state.storage.objects.length (.rows ty s.scope (rowIds s.frame.state.storage.objects.length n.toNat) 0 (List.replicate n.toNat []))) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s (.vector (.integer ty)) wr]) (appended l s.frame.bindings.length)
        (putContents (eraseHeap h) s.frame.state.storage.objects.length (.rows ty s.scope (List.replicate n.toNat []))) out ∧
      out.scope = s.scope ∧ out.work ≤ s.work+2*count.nodes+n.toNat+4 ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)) ∧
      out.frame.bindings.length = s.frame.bindings.length+1 ∧
      out.frame.state.storage.objects.length = s.frame.state.storage.objects.length+1+n.toNat := by
  obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) n pure) s real
  let released := t.release s
  have before : Family params h released.frame m := release_family family ev.2.1 extra ev.2.2
  have rb : released.frame.bindings = s.frame.bindings := DynamicConstructCore.release_bindings s t extra ev.2.2
  have rs : released.frame.state = s.frame.state := ev.2.1.1
  have sc : released.scope = s.scope := ev.2.1.2.2.2.1
  have snap : snapshot released = l := (ev_preserves params l (eraseHeap h) s t real count n extra _ _ ev).1.locals
  let next : State := ⟨s.frame.state.forest.constructRows ty s.scope n.toNat,
    {s.frame.state.storage with
      objects := s.frame.state.storage.objects ++ some (rootBuffer s.frame.state.storage.objects.length n.toNat) ::
        (List.range n.toNat).map fun j => some (rowBuffer ty (s.frame.state.storage.objects.length+1+j)),
      work := s.frame.state.storage.work+n.toNat+1,
      peak := max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)}⟩
  have allocated : released.frame.state.constructRows ty released.scope n.toNat = some next := by
    rw [rs,sc]; simp [State.constructRows,family.valid,supported,limit,next]
  have base := DynamicAllocateFamily.rows before next ty released.scope n.toNat wr allocated
  obtain ⟨frame,out,bound,defined,post,matched,snapOut,scopeOut,workOut,peakOut,outState,bindingCount⟩ := install_full params h m released before next _ wr n.toNat rfl base
  have bound' : ({released.frame with state := next,rootWritable := released.frame.rootWritable ++ [wr] ++ List.replicate n.toNat false} : Frame).bindRoot released.frame.state.storage.objects.length (.vector (.integer ty)) released.scope wr = some (frame,released.frame.bindings.length) := by
    simpa only [grown,View.element] using bound
  have ran : (NStmt.constructRows ty wr count).run s = some ⟨out,none,false⟩ := by
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind,if_pos nonnegative]
    change (released.frame.state.constructRows ty released.scope n.toNat).bind _ = _
    rw [allocated,Option.bind_some]
    change (({released.frame with state := next,rootWritable := released.frame.rootWritable ++ [wr] ++ List.replicate n.toNat false} : Frame).bindRoot released.frame.state.storage.objects.length (.vector (.integer ty)) released.scope wr).bind _ = _
    rw [bound',Option.bind_some]
    rw [defined]
  have descriptor : parameter released (.vector (.integer ty)) wr = parameter s (.vector (.integer ty)) wr := by
    simp only [parameter,rs,sc,rb]
  simp only [View.element] at post matched
  rw [descriptor] at post matched
  simp only [rs,sc] at post matched
  rw [snap,rb] at snapOut
  rw [snapOut,erase_put] at matched
  refine ⟨out,ran,post,matched,scopeOut.trans sc,?_,?_,?_,?_⟩
  · have upper := ev.2.1.2.2.2.2.2.2.2.2.1
    change t.scalars.work ≤ s.scalars.work+2*count.nodes at upper
    rw [workOut]
    change t.scalars.work+3+(s.frame.state.storage.work+n.toNat+1) ≤ s.scalars.work+s.frame.state.storage.work+2*count.nodes+n.toNat+4
    omega
  · obtain ⟨_,_,_,_,memory,bindings,baseline,_,_,_,scalarPeak,_,peak⟩ := ev.2.1
    have live := liveS_of_memory memory bindings baseline
    have store : t.frame.state.storage.peak = s.frame.state.storage.peak := by rw [ev.2.1.1]
    rw [store] at peak
    have scalarBound : max t.scalars.peak (liveS t) ≤ max s.scalars.peak (liveS s+2*count.nodes) := by rw [live]; omega
    have growing : s.frame.state.storage.peak ≤ next.storage.peak := Nat.le_max_left _ _
    rw [peakOut]
    change max t.peak (max t.scalars.peak (liveS t)+next.storage.peak) ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes)+next.storage.peak)
    omega
  · rw [bindingCount,rb]
  · rw [outState]
    simp only [next,List.length_append,List.length_cons,List.length_map,List.length_range]
    omega

theorem sound (params : List Parameter) (h : Heap) (m : Resources) (l : Locals) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params l (eraseHeap h) s)
    (ty : Ty) (wr : Bool) (count : NExpr) (n : Int)
    (pure : denote params l (eraseHeap h) count = some n) (nonnegative : 0 ≤ n)
    (supported : Proofs.CppVectorBindings.supported ty) (limit : n.toNat ≤ rowLimit) :
    ∃ out, (NStmt.constructRows ty wr count).run s = some ⟨out,none,false⟩ ∧
      Family (params ++ [parameter s (.vector (.integer ty)) wr])
        (put h s.frame.state.storage.objects.length (.rows ty s.scope (rowIds s.frame.state.storage.objects.length n.toNat) 0 (List.replicate n.toNat []))) out.frame (resources out.frame) ∧
      Realizes (params ++ [parameter s (.vector (.integer ty)) wr]) (appended l s.frame.bindings.length)
        (putContents (eraseHeap h) s.frame.state.storage.objects.length (.rows ty s.scope (List.replicate n.toNat []))) out ∧
      out.scope = s.scope ∧ out.work ≤ s.work+2*count.nodes+n.toNat+4 ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*count.nodes)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)) := by
  obtain ⟨out,ran,post,real,scope,work,peak,_⟩ := sound_full params h m l s family real ty wr count n pure nonnegative supported limit
  exact ⟨out,ran,post,real,scope,work,peak⟩

end Proofs.DynamicConstructRows
