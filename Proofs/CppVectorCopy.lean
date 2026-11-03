import Proofs.CppVectorStore

namespace Proofs.CppVectorCopy
open Proofs.CppVector

-- A store must supply a globally fresh owner. This local operation checks
-- separation from its source. Cost units apply to fixed-width scalar elements.
def copied (source : Buffer α) (owner : Nat) : Buffer α :=
  ⟨owner,source.items,source.items.length,source.limit,0⟩

def copyConstruct (source : Buffer α) (owner : Nat) (accept : α → Bool) : Option (Result α Unit) :=
  if source.Valid accept ∧ owner ≠ source.owner then
    some ⟨copied source owner,(),source.items.length+1,source.items.length+2⟩
  else none

theorem copied_valid (source : Buffer α) (owner : Nat) (accept : α → Bool)
    (valid : source.Valid accept) : (copied source owner).Valid accept :=
  ⟨Nat.le_refl _,Nat.le_trans valid.1 valid.2.1,valid.2.2⟩

theorem copy_runs (source : Buffer α) (owner : Nat) (accept : α → Bool)
    (valid : source.Valid accept) (fresh : owner ≠ source.owner) :
    copyConstruct source owner accept = some ⟨copied source owner,(),source.items.length+1,source.items.length+2⟩ := by
  simp [copyConstruct,valid,fresh]

theorem copy_same_owner (source : Buffer α) (accept : α → Bool) :
    copyConstruct source source.owner accept = none := by simp [copyConstruct]

theorem copy_invalid (source : Buffer α) (owner : Nat) (accept : α → Bool)
    (invalid : ¬ source.Valid accept) : copyConstruct source owner accept = none := by simp [copyConstruct,invalid]

theorem copy_read (source : Buffer α) (owner index : Nat) (accept : α → Bool) (value : α)
    (valid : source.Valid accept) (found : source.items[index]? = some value) :
    readRef (copied source owner) accept ⟨owner,0,index⟩ =
      some ⟨copied source owner,value,1,source.items.length+2⟩ :=
  readRef_runs _ _ _ _ (copied_valid source owner accept valid) found

theorem source_ref_separate (source : Buffer α) (owner : Nat) (accept : α → Bool) (reference : ElementRef)
    (fresh : owner ≠ source.owner) (origin : reference.owner = source.owner) :
    readRef (copied source owner) accept reference = none := by
  simp [readRef,copied,origin,Ne.symm fresh]

theorem copied_write (source : Buffer α) (owner index : Nat) (accept : α → Bool) (value : α)
    (valid : source.Valid accept) (inside : index < source.items.length) (accepted : accept value = true) :
    writeRef (copied source owner) accept true ⟨owner,0,index⟩ value =
      some ⟨{copied source owner with items := source.items.set index value},(),1,source.items.length+2⟩ :=
  writeRef_runs _ _ _ _ (copied_valid source owner accept valid) inside accepted

open Proofs.CppVectorStore

-- Allocate through the store so the new owner is fresh among all lifetimes,
-- including tombstones. The source and every existing object remain resident.
def copyStore (s : Store α) (sourceOwner : Nat) (accept : α → Bool) :
    Option (Store α × Nat) := do
  let source ← s.lookup sourceOwner
  let result ← copyConstruct source s.objects.length accept
  some (s.allocate result.buffer result.work result.peak,s.objects.length)

def extended (s : Store α) (source : Buffer α) : Store α :=
  s.allocate (copied source s.objects.length) (source.items.length+1) (source.items.length+2)

theorem copy_store_runs (s : Store α) (sourceOwner : Nat) (source : Buffer α)
    (accept : α → Bool) (valid : s.Valid accept) (found : s.lookup sourceOwner = some source) :
    copyStore s sourceOwner accept = some (extended s source,s.objects.length) := by
  have properties := valid sourceOwner source found
  have bound := lookup_bound s sourceOwner source found
  have fresh : s.objects.length ≠ source.owner := by rw [properties.1]; omega
  simp [copyStore,found,copy_runs source s.objects.length accept properties.2 fresh,extended]

theorem copy_store_valid (s : Store α) (sourceOwner : Nat) (source : Buffer α)
    (accept : α → Bool) (valid : s.Valid accept) (found : s.lookup sourceOwner = some source) :
    (extended s source).Valid accept :=
  allocate_valid s _ accept _ _ valid (copied_valid source _ accept (valid _ _ found).2)

theorem copy_store_new (s : Store α) (source : Buffer α) :
    (extended s source).lookup s.objects.length = some (copied source s.objects.length) := by
  simpa [extended,copied] using lookup_allocate_new s (copied source s.objects.length)
    (source.items.length+1) (source.items.length+2)

theorem copy_store_old (s : Store α) (source : Buffer α) (owner : Nat)
    (old : owner < s.objects.length) :
    (extended s source).lookup owner = s.lookup owner :=
  lookup_allocate_old s _ _ _ owner old

theorem copy_store_reference (s : Store α) (source : Buffer α) (accept : α → Bool)
    (reference : ElementRef) (old : reference.owner < s.objects.length) :
    (extended s source).readReference accept reference = s.readReference accept reference := by
  simp only [Store.readReference,copy_store_old s source reference.owner old]

theorem copy_store_cost (s : Store α) (source : Buffer α) :
    (extended s source).work = s.work+source.items.length+1 ∧
    (extended s source).liveSpace = s.liveSpace+source.items.length+1 ∧
    (extended s source).peak = max s.peak (s.liveSpace+source.items.length+2-s.baseSpace) := by
  have resident := allocate_space s (copied source s.objects.length)
    (source.items.length+1) (source.items.length+2)
  refine ⟨by simp [extended,Store.allocate,Nat.add_assoc], ?_,
    by simp [extended,Store.allocate,Nat.add_assoc]⟩
  simpa [extended,copied] using resident

end Proofs.CppVectorCopy
