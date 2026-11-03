import Proofs.CppVectorGrowth
import Proofs.CppVectorStore

namespace Proofs.CppVectorStoreGrowth
open Proofs.CppVector Proofs.CppVectorStore

def append (s : Store α) (accept : α → Bool) (writable : Bool)
    (owner : Nat) (value : α) : Option (Store α × Unit) := do
  let buffer ← s.lookup owner
  let result ← CppVectorGrowth.append buffer accept writable value
  s.commit owner accept result

theorem append_peak (b : Buffer α) (accept : α → Bool) (value : α) (r : Result α Unit)
    (run : CppVectorGrowth.append b accept true value = some r) :
    b.capacity + 1 ≤ r.peak ∧ r.buffer.capacity + 1 ≤ r.peak := by
  unfold CppVectorGrowth.append at run
  split at run
  · split at run <;> cases run <;> dsimp <;> omega
  · contradiction

theorem append_spec (s : Store α) (accept : α → Bool) (owner : Nat) (value : α)
    (b : Buffer α) (valid : s.Valid accept) (lookup : s.lookup owner = some b)
    (accepted : accept value = true) (room : b.items.length < b.limit) :
    ∃ final r, append s accept true owner value = some (final, ()) ∧
      CppVectorGrowth.append b accept true value = some r ∧
      final.Valid accept ∧ final.lookup owner = some r.buffer ∧
      r.buffer.items = b.items ++ [value] ∧
      final.objects.length = s.objects.length ∧
      final.work = s.work + r.work ∧
      final.liveSpace + b.capacity + 1 = s.liveSpace + r.buffer.capacity + 1 ∧
      final.liveSpace - s.baseSpace ≤ final.peak ∧
      (∀ other, owner ≠ other → final.lookup other = s.lookup other) := by
  have bv := (valid owner b lookup).2
  have owns := (valid owner b lookup).1
  obtain ⟨r, run, rv, ri, ro, _, _, _, _⟩ := CppVectorGrowth.append_spec b accept value bv accepted room
  have peaks := append_peak b accept value r run
  have bounded := lookup_bound s owner b lookup
  have same : r.buffer.owner = owner := ro.trans owns
  have commit := commit_runs s owner accept b r lookup owns same rv peaks.1 peaks.2
  let final : Store α := {s with objects := s.objects.set owner (some r.buffer), work := s.work + r.work, peak := max s.peak (s.liveSpace + (r.peak - (b.capacity+1)) - s.baseSpace)}
  have raw : s.objects[owner]? = some (some b) := by
    unfold Store.lookup at lookup
    cases h : s.objects[owner]? <;> simp [h] at lookup
    rename_i x
    cases x <;> simp_all
  refine ⟨final, r, ?_, run, commit_valid s owner accept r valid bounded same rv,
    lookup_set_same s owner (some r.buffer) bounded, ri, by simp [final], rfl,
    update_space s owner b r.buffer raw, ?_, ?_⟩
  · simp [append, lookup, run, commit, final]
  · exact update_peak_bound s owner b r raw peaks.1 peaks.2
  · intro other different
    exact lookup_set_other s owner other (some r.buffer) different

theorem append_dead (s : Store α) (accept : α → Bool) (writable : Bool)
    (owner : Nat) (value : α) (dead : s.lookup owner = none) :
    append s accept writable owner value = none := by simp [append, dead]

theorem append_readonly (s : Store α) (accept : α → Bool) (owner : Nat) (value : α) :
    append s accept false owner value = none := by
  unfold append
  cases s.lookup owner <;> simp [CppVectorGrowth.append_readonly]

end Proofs.CppVectorStoreGrowth
