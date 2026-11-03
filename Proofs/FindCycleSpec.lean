import Proofs.FindCycleStep

namespace Proofs.FindCycleSpec
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv (upd upd_same upd_ne AdjH)
open Proofs.FindCycleInv Proofs.FindCycleStep

section
variable {n : Nat} {hd tg : Nat → Nat} {st : FS}

/-- If everything is finished, the graph has no directed cycle. -/
theorem acyclic_of_done (G : FGH n hd tg) (I : FInv n hd tg st) (hsp : st.sp = 0)
    (hall : ∀ a, a < n → st.C a ≠ 0) :
    ∀ u w, AdjH hd tg u w → ¬ Rtc (AdjH hd tg) w u := by
  have hblack : ∀ a, a < n → st.C a = 2 := by
    intro a ha
    have := hall a ha
    rcases I.c_rng a with h | h | h
    · exact absurd h this
    · obtain ⟨i, hi, _⟩ := I.gray_sk a h; omega
    · exact h
  intro u w huw hpath
  have hun := (G.adj_lt u w huw).1
  -- along an arc the finishing time strictly decreases
  have step : ∀ a b, AdjH hd tg a b → st.Fi b < st.Fi a := by
    intro a b ⟨q, hq1, hq2, hq3⟩
    have ha := (G.adj_lt a b ⟨q, hq1, hq2, hq3⟩).1
    have := (I.bl_done a (hblack a ha)).2 q hq1 hq2
    rw [hq3] at this
    exact this.2
  have key : ∀ x, Rtc (AdjH hd tg) w x → st.Fi x ≤ st.Fi w := by
    intro x hx
    induction hx with
    | refl => exact Int.le_refl _
    | tail _ hbc ih =>
      have := step _ _ hbc
      omega
  have h1 := key u hpath
  have h2 := step u w huw
  omega


/-- The stack at the moment a back arc is found. -/
structure Found (n : Nat) (hd tg : Nat → Nat) (Sk : Nat → Nat) (fsp fw : Nat) : Prop where
  pos : 0 < fsp
  lt : ∀ i, i < fsp → Sk i < n
  inj : ∀ i j, i < fsp → j < fsp → Sk i = Sk j → i = j
  arc : ∀ i, i + 1 < fsp → AdjH hd tg (Sk i) (Sk (i + 1))
  mem : ∃ j, j < fsp ∧ Sk j = fw
  back : AdjH hd tg (Sk (fsp - 1)) fw

theorem Found.fsp_le {Sk : Nat → Nat} {fsp fw : Nat} (F : Found n hd tg Sk fsp fw) : fsp ≤ n := by
  have hnd : ((List.range fsp).map Sk).Nodup := by
    apply Proofs.PrimMath.nodup_map_inj List.nodup_range
    intro x hx y hy h
    exact F.inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) h
  have hsub : (List.range fsp).map Sk ⊆ List.range n := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr (F.lt i (List.mem_range.mp hi))
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

theorem found_of_inv (I : FInv n hd tg st) {v w q : Nat} (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v)
    (hq : (q : Int) = st.It v) (hit : q < hd (v + 1)) (hw : tg q = w) (hwg : st.C w = 1) :
    Found n hd tg st.Sk st.sp w := by
  have hvg := top_gray I hsp hv
  have hrng := I.it_rng v (by omega)
  refine ⟨hsp, ?_, I.sk_inj, I.sk_arc, ?_, ?_⟩
  · intro i hi
    have := I.sk_gray i hi
    exact I.c_lt _ (by omega)
  · obtain ⟨i, hi, hik⟩ := I.gray_sk w hwg
    exact ⟨i, hi, hik⟩
  · rw [hv]; exact ⟨q, by omega, hit, hw⟩

/-- The meaning of the output of `find_cycle` when it reports a cycle. -/
def CycOut (n : Nat) (hd tg : Nat → Nat) (cyc : List Int) (k : Nat) : Prop :=
  0 < k ∧ k ≤ n ∧ (∀ i, i < k → 0 ≤ cyc.getD i 0 ∧ cyc.getD i 0 < (n : Int)) ∧
  (∀ i j, i < k → j < k → cyc.getD i 0 = cyc.getD j 0 → i = j) ∧
  (∀ i, i < k → ∃ a b : Nat, (a : Int) = cyc.getD i 0 ∧ (b : Int) = cyc.getD ((i + 1) % k) 0 ∧ AdjH hd tg a b)

theorem cycout_of_found {Sk : Nat → Nat} {fsp fw : Nat} (F : Found n hd tg Sk fsp fw) {j : Nat} (hj : j < fsp)
    (hjw : Sk j = fw) (cyc : List Int) (hcyc : ∀ t, t < fsp - j → cyc.getD t 0 = ((Sk (j + t) : Nat) : Int)) :
    CycOut n hd tg cyc (fsp - j) := by
  have hnd : ((List.range fsp).map Sk).Nodup := by
    apply Proofs.PrimMath.nodup_map_inj List.nodup_range
    intro x hx y hy h
    exact F.inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) h
  have hsub : (List.range fsp).map Sk ⊆ List.range n := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr (F.lt i (List.mem_range.mp hi))
  have hfn : fsp ≤ n := by
    have := List.Nodup.length_le_of_subset hnd hsub
    simpa using this
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro i hi
    rw [hcyc i hi]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast F.lt (j + i) (by omega)⟩
  · intro a b ha hb hab
    rw [hcyc a ha, hcyc b hb] at hab
    have := F.inj (j + a) (j + b) (by omega) (by omega) (by exact_mod_cast hab)
    omega
  · intro i hi
    by_cases hlast : i + 1 < fsp - j
    · refine ⟨Sk (j + i), Sk (j + i + 1), (hcyc i hi).symm, ?_, ?_⟩
      · have : (i + 1) % (fsp - j) = i + 1 := Nat.mod_eq_of_lt hlast
        rw [this, hcyc (i + 1) hlast, Nat.add_assoc]
      · exact F.arc (j + i) (by omega)
    · have hi' : i = fsp - j - 1 := by omega
      have hmod : (i + 1) % (fsp - j) = 0 := by
        have : i + 1 = fsp - j := by omega
        rw [this]; exact Nat.mod_self _
      refine ⟨Sk (j + i), fw, (hcyc i hi).symm, ?_, ?_⟩
      · rw [hmod, hcyc 0 (by omega)]; simp [hjw]
      · have : j + i = fsp - 1 := by omega
        rw [this]; exact F.back

end

end Proofs.FindCycleSpec
