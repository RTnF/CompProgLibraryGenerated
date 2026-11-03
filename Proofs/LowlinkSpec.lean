import Proofs.LowlinkFinal

namespace Proofs.LowlinkSpec
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv Proofs.LowlinkGraph Proofs.LowlinkFinal

/-- The meaning of the output arrays of `lowlink`, for the final state of the machine. -/
theorem lowlink_spec {n : Nat} {hd tg : Nat → Nat} {st : St} (G : GH n hd tg) (I : MInv n hd tg st) (hsp : st.sp = 0)
    (hall : ∀ v, v < n → v ∈ st.Vis) :
    (∀ v, v < n → 0 ≤ st.O v ∧ st.O v < (n : Int)) ∧
    (∀ u v, u < n → v < n → st.O u = st.O v → u = v) ∧
    (∀ v, v < n → st.P v = -1 ∨ ∃ p : Nat, p < n ∧ st.P v = (p : Int) ∧ AdjH hd tg p v ∧ st.O p < st.O v) ∧
    (∀ v p : Nat, v < n → st.P v = (p : Int) →
      (st.L v = st.O v ↔ ¬ Rtc (LlFinal.EB (AdjH hd tg) p v) p v)) ∧
    (∀ v, v < n → (((st.P v < 0 ∧ 2 ≤ st.Sp v) ∨ (0 ≤ st.P v ∧ 1 ≤ st.Sp v)) ↔
      ∃ a b, AdjH hd tg v a ∧ AdjH hd tg v b ∧ ¬ Rtc (LlFinal.EV (AdjH hd tg) v) a b)) := by
  have L := final_of_inv G I hsp hall
  have hVl := I.vis_len_le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvV := hall v hv
    have := I.ord_lt_len hvV
    exact ⟨this.1, by omega⟩
  · intro u v hu hv h
    exact I.ord_inj (hall u hu) (hall v hv) h
  · intro v hv
    by_cases h : 0 ≤ st.P v
    · right
      obtain ⟨p, hp⟩ : ∃ p : Nat, st.P v = (p : Int) := ⟨(st.P v).toNat, by omega⟩
      obtain ⟨h1, h2, h3⟩ := I.par_ok p v hp
      exact ⟨p, I.vis_lt p h1, hp, h2, h3⟩
    · left
      exact I.par_neg v (by omega)
  · intro v p hv hp
    have hvV := hall v hv
    have hpar : parO st.P v = some p := parO_some.mpr hp
    have key := L.bridge_iff v p hpar
    have h1 := I.low_le v hvV
    have h2 := (I.ord_lt_len hvV).1
    have e : ((st.L v).toNat = (st.O v).toNat) ↔ st.L v = st.O v := by omega
    exact e.symm.trans key
  · intro v hv
    have hvV := hall v hv
    have key := L.art_iff hv
    have hs : 0 ≤ st.Sp v := by
      rw [I.sep_cnt v hvV]; exact Int.natCast_nonneg _
    have hnone : parO st.P v = none ↔ st.P v < 0 := by
      unfold parO
      split <;> simp <;> omega
    have hsome : parO st.P v ≠ none ↔ 0 ≤ st.P v := by
      rw [Ne, hnone]; omega
    unfold Art at key
    rw [hnone, hsome] at key
    have e1 : (2 ≤ (st.Sp v).toNat) ↔ 2 ≤ st.Sp v := by omega
    have e2 : (1 ≤ (st.Sp v).toNat) ↔ 1 ≤ st.Sp v := by omega
    show _ ↔ _
    rw [← key]
    simp only [e1, e2]

end Proofs.LowlinkSpec
