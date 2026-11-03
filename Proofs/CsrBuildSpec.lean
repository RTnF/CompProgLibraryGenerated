import Proofs.CsrBuildMath
import Proofs.TopoSortMath
import Proofs.LowlinkInv

namespace Proofs.CsrBuildSpec
open Proofs.CsrBuildMath Proofs.LowlinkInv

/-- The head array: `H[v]` is the number of edges whose source is smaller than `v`. -/
def headOf (F : List Nat) (m n : Nat) : List Nat := (List.range (n + 1)).map (ocnt (fun j => F.getD j 0) m)

theorem headOf_len (F : List Nat) (m n : Nat) : (headOf F m n).length = n + 1 := by simp [headOf]

theorem headOf_get (F : List Nat) (m n v : Nat) (hv : v ≤ n) :
    (headOf F m n).getD v 0 = ocnt (fun j => F.getD j 0) m v := by
  unfold headOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem headOf_big (F : List Nat) (m n v : Nat) (hv : n < v) : (headOf F m n).getD v 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [headOf_len]; omega)]; rfl

/-- The result of `csr_build`: a valid head array, the adjacency of the CSR graph equals the edge relation, and the
edges are placed stably (the `k`-th edge out of `u` goes to slot `head[u] + k`). -/
structure CSROut (n : Nat) (F T : List Nat) (H T' : List Nat) : Prop where
  head : Proofs.TopoSortMath.HeadOK H T' n
  adj : ∀ u w, AdjH (fun a => H.getD a 0) (fun a => T'.getD a 0) u w ↔
    ∃ i, i < F.length ∧ F.getD i 0 = u ∧ T.getD i 0 = w
  stable : ∀ j, j < F.length →
    T'.getD (H.getD (F.getD j 0) 0 + cnt (fun j => F.getD j 0) (F.getD j 0) j) 0 = T.getD j 0

theorem csr_spec (F T : List Nat) (n m : Nat) (hFl : F.length = m) (hF : ∀ j, j < m → F.getD j 0 < n)
    (T' : List Nat) (hT'l : T'.length = m)
    (hT' : ∀ j, j < m → T'.getD (ocnt (fun j => F.getD j 0) m (F.getD j 0) + cnt (fun j => F.getD j 0) (F.getD j 0) j) 0
      = T.getD j 0) : CSROut n F T (headOf F m n) T' := by
  have htot := ocnt_total (fun j => F.getD j 0) n m hF
  refine ⟨⟨headOf_len F m n, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [headOf_get F m n 0 (by omega)]; rfl
  · intro i hi
    rw [headOf_get F m n i (by omega), headOf_get F m n (i + 1) (by omega)]
    exact ocnt_mono _ _ (by omega)
  · rw [headOf_get F m n n (Nat.le_refl _), htot, hT'l]
  · intro u w
    constructor
    · rintro ⟨q, hq1, hq2, hq3⟩
      dsimp only at hq1 hq2 hq3
      have hun : u < n := by
        apply Classical.byContradiction
        intro h
        rw [headOf_big F m n (u + 1) (by omega)] at hq2
        omega
      rw [headOf_get F m n u (by omega)] at hq1
      rw [headOf_get F m n (u + 1) (by omega)] at hq2
      have hq2' : q < ocnt (fun j => F.getD j 0) m u + cnt (fun j => F.getD j 0) u m := hq2
      obtain ⟨j, hj, hju, hcj⟩ := kth (fun j => F.getD j 0) u m (q - ocnt (fun j => F.getD j 0) m u) (by omega)
      have hju' : F.getD j 0 = u := hju
      refine ⟨j, by omega, hju', ?_⟩
      rw [← hT' j hj, hju', hcj]
      have : ocnt (fun j => F.getD j 0) m u + (q - ocnt (fun j => F.getD j 0) m u) = q := by omega
      rw [this, hq3]
    · rintro ⟨i, hi, hiu, hiw⟩
      have him : i < m := by omega
      have hu := hF i him
      subst hiu
      have hlt := cnt_lt (fun j => F.getD j 0) him
      refine ⟨ocnt (fun j => F.getD j 0) m (F.getD i 0) + cnt (fun j => F.getD j 0) (F.getD i 0) i, ?_, ?_, ?_⟩
      · dsimp only; rw [headOf_get F m n _ (by omega)]; omega
      · dsimp only; rw [headOf_get F m n _ (by omega)]
        show _ < ocnt (fun j => F.getD j 0) m (F.getD i 0) + cnt (fun j => F.getD j 0) (F.getD i 0) m
        omega
      · dsimp only; rw [hT' i him, hiw]
  · intro j hj
    have him : j < m := by omega
    rw [headOf_get F m n _ (by have := hF j him; omega)]
    exact hT' j him

theorem ocnt_find (F : Nat → Nat) (i : Nat) : ∀ n q, q < ocnt F i n → ∃ u, u < n ∧ ocnt F i u ≤ q ∧ q < ocnt F i (u + 1) := by
  intro n
  induction n with
  | zero => intro q h; simp [ocnt] at h
  | succ n ih =>
    intro q h
    by_cases hq : q < ocnt F i n
    · obtain ⟨u, hu, h1, h2⟩ := ih q hq
      exact ⟨u, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, h⟩

theorem tg_nonneg (F T : List Nat) (n m : Nat) (hF : ∀ j, j < m → F.getD j 0 < n) (Tg : List Int)
    (hT : ∀ j, j < m → Tg.getD (ocnt (fun j => F.getD j 0) m (F.getD j 0) + cnt (fun j => F.getD j 0) (F.getD j 0) j) 0
      = ((T.getD j 0 : Nat) : Int)) : ∀ q, q < m → 0 ≤ Tg.getD q 0 := by
  intro q hq
  have htot := ocnt_total (fun j => F.getD j 0) n m hF
  obtain ⟨u, hu, h1, h2⟩ := ocnt_find (fun j => F.getD j 0) m n q (by omega)
  have h2' : q < ocnt (fun j => F.getD j 0) m u + cnt (fun j => F.getD j 0) u m := h2
  obtain ⟨j, hj, hju, hcj⟩ := kth (fun j => F.getD j 0) u m (q - ocnt (fun j => F.getD j 0) m u) (by omega)
  have hju' : F.getD j 0 = u := hju
  have := hT j hj
  rw [hju', hcj] at this
  have e : ocnt (fun j => F.getD j 0) m u + (q - ocnt (fun j => F.getD j 0) m u) = q := by omega
  rw [e] at this
  rw [this]
  exact Int.natCast_nonneg _

theorem map_toNat_cast (L : List Int) (h : ∀ q, q < L.length → 0 ≤ L.getD q 0) :
    L = (L.map Int.toNat).map (fun a : Nat => (a : Int)) := by
  apply List.ext_getElem
  · simp
  · intro q h1 h2
    have := h q h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp only [List.getElem_map]
    exact (Int.toNat_of_nonneg this).symm

theorem head_cast (F : List Nat) (n m : Nat) (Hd : List Int) (hl : Hd.length = n + 1)
    (hf : ∀ v, Hd.getD v 0 = if v ≤ n then ((ocnt (fun j => F.getD j 0) m v : Nat) : Int) else 0) :
    Hd = (headOf F m n).map (fun a : Nat => (a : Int)) := by
  apply List.ext_getElem
  · simp [headOf_len, hl]
  · intro q h1 h2
    have h3 : q ≤ n := by omega
    have := hf q
    rw [if_pos h3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp only [List.getElem_map]
    have e := headOf_get F m n q h3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [headOf_len]; omega)] at e
    simp at this e
    rw [this, e]

/-- From the final vectors of the loops to the specification. -/
theorem csr_glue (F T : List Nat) (n m : Nat) (hFl : F.length = m) (hF : ∀ j, j < m → F.getD j 0 < n)
    (Hd Tg : List Int) (hHdl : Hd.length = n + 1)
    (hHdf : ∀ v, Hd.getD v 0 = if v ≤ n then ((ocnt (fun j => F.getD j 0) m v : Nat) : Int) else 0)
    (hTgl : Tg.length = m)
    (hTg : ∀ j, j < m → Tg.getD (ocnt (fun j => F.getD j 0) m (F.getD j 0) + cnt (fun j => F.getD j 0) (F.getD j 0) j) 0
      = ((T.getD j 0 : Nat) : Int)) :
    ∃ H' T' : List Nat, CSROut n F T H' T' ∧ Hd = H'.map (fun a : Nat => (a : Int)) ∧
      Tg = T'.map (fun a : Nat => (a : Int)) := by
  have hnn := tg_nonneg F T n m hF Tg hTg
  have hTe := map_toNat_cast Tg (fun q hq => hnn q (by omega))
  have hT'l : (Tg.map Int.toNat).length = m := by simp [hTgl]
  refine ⟨headOf F m n, Tg.map Int.toNat, ?_, head_cast F n m Hd hHdl hHdf, hTe⟩
  apply csr_spec F T n m hFl hF _ hT'l
  intro j hj
  have htot := ocnt_total (fun j => F.getD j 0) n m hF
  have hp : ocnt (fun j => F.getD j 0) m (F.getD j 0) + cnt (fun j => F.getD j 0) (F.getD j 0) j < m := by
    have h1 := cnt_lt (fun j => F.getD j 0) hj
    have h2 := ocnt_mono (fun j => F.getD j 0) m (show F.getD j 0 + 1 ≤ n by have := hF j hj; omega)
    have h3 : ocnt (fun j => F.getD j 0) m (F.getD j 0 + 1) =
      ocnt (fun j => F.getD j 0) m (F.getD j 0) + cnt (fun j => F.getD j 0) (F.getD j 0) m := rfl
    omega
  have := hTg j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
  simp at this ⊢
  omega

end Proofs.CsrBuildSpec
