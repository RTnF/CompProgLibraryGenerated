import Proofs.CppNestedOps

namespace Proofs.CppBufferHeaders
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings

structure Signature where
  owner : Nat
  capacity : Nat
  limit : Nat
  epoch : Nat
  size : Nat
deriving DecidableEq, Repr

def signature (b : Buffer Value) : Signature := ⟨b.owner,b.capacity,b.limit,b.epoch,b.items.length⟩

-- Values may change, while allocation headers and lengths stay unchanged.
structure SameHeaders (s t : State) : Prop where
  forest : t.forest = s.forest
  count : t.storage.objects.length = s.storage.objects.length
  base : t.storage.baseSpace = s.storage.baseSpace
  buffers : ∀ owner, (t.storage.lookup owner).map signature = (s.storage.lookup owner).map signature

theorem SameHeaders.refl (s : State) : SameHeaders s s := ⟨rfl,rfl,rfl,fun _ => rfl⟩

theorem SameHeaders.trans {s t u : State} (a : SameHeaders s t) (b : SameHeaders t u) : SameHeaders s u :=
  ⟨b.forest.trans a.forest,b.count.trans a.count,b.base.trans a.base,fun owner => (b.buffers owner).trans (a.buffers owner)⟩

theorem updated_headers (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit)
    (bound : owner < f.state.storage.objects.length) (found : f.state.storage.lookup owner = some old)
    (same : signature result.buffer = signature old) :
    SameHeaders f.state (f.updated owner old result).state := by
  refine ⟨rfl,by simp [Frame.updated],rfl,?_⟩
  intro other
  by_cases eq : other = owner
  · subst other
    rw [Proofs.CppNestedOps.updated_lookup_self f owner old result bound,found]
    exact congrArg some same
  · rw [Proofs.CppNestedOps.updated_lookup_other f owner other old result (Ne.symm eq)]

theorem write_headers (f : Frame) (owner index : Nat) (old : Buffer Value) (value : Value)
    (bound : owner < f.state.storage.objects.length) (found : f.state.storage.lookup owner = some old) :
    SameHeaders f.state
      (f.updated owner old ⟨{old with items := old.items.set index value},(),1,old.capacity+2⟩).state := by
  apply updated_headers f owner old _ bound found
  simp [signature]

theorem SameHeaders.live {s t : State} (same : SameHeaders s t) : t.liveSpace = s.liveSpace := by
  have nodes (owner : Nat) : t.nodeSpace owner = s.nodeSpace owner := by
    have header := same.buffers owner
    simp only [State.nodeSpace,same.forest]
    cases before : s.storage.lookup owner <;> cases after : t.storage.lookup owner <;>
      simp [before,after,signature] at header ⊢
    obtain ⟨_,capacity,_,_,_⟩ := header
    cases s.forest.lookup owner <;> simp [capacity]
  simp only [State.liveSpace,same.count]
  congr 1
  exact List.map_congr_left (fun owner _ => nodes owner)

end Proofs.CppBufferHeaders
