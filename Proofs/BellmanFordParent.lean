import Proofs.BellmanFordPExec
import Proofs.BellmanFordBridge

namespace Proofs.BellmanFordParent
open Proofs.BellmanFordExec Proofs.BellmanFordPExec

theorem getD_set_same (l : List Int) (i : Nat) (x : Int) (h : i < l.length) : (l.set i x).getD i 0 = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (l : List Int) (i j : Nat) (x : Int) (h : j ≠ i) : (l.set i x).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

/-- Every parent is `-1` or comes from an edge `p -> v` whose relaxation the distance respects: `D[v] ≥ D[p] + cost`. -/
def ParInvE (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D P : List Int) : Prop :=
  ∀ v, v < P.length → P.getD v 0 = -1 ∨
    ∃ e, e < m ∧ ((F.getD e 0 : Nat) : Int) = P.getD v 0 ∧ T.getD e 0 = v ∧ D.getD (F.getD e 0) 0 < inf ∧
      D.getD (F.getD e 0) 0 + Cc.getD e 0 ≤ D.getD v 0

theorem relax_par (inf : Int) (F T : List Nat) (Cc : List Int) (m e0 : Nat) (D P : List Int) (he0 : e0 < m)
    (hDP : D.length = P.length) (ht : T.getD e0 0 < D.length) (hup : F.getD e0 0 < D.length) (hle : ∀ x ∈ D, x ≤ inf)
    (h : ParInvE inf F T Cc m D P) :
    ParInvE inf F T Cc m (relaxL inf F T Cc e0 D) (relaxPL inf F T Cc e0 D P) ∧
      (∀ x ∈ relaxL inf F T Cc e0 D, x ≤ inf) := by
  unfold relaxL relaxPL
  by_cases hc : D.getD (F.getD e0 0) 0 ≠ inf ∧ D.getD (F.getD e0 0) 0 + Cc.getD e0 0 < D.getD (T.getD e0 0) 0
  · rw [if_pos hc, if_pos hc]
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨u, hu⟩ : ∃ u, F.getD e0 0 = u := ⟨_, rfl⟩
    obtain ⟨t, htt⟩ : ∃ t, T.getD e0 0 = t := ⟨_, rfl⟩
    obtain ⟨c, hcc⟩ : ∃ c, Cc.getD e0 0 = c := ⟨_, rfl⟩
    rw [hu] at hc1 hc2 ⊢
    rw [htt] at hc2 ht ⊢
    rw [hcc] at hc2 ⊢
    rw [hu] at hup
    have hDu : D.getD u 0 ≤ inf := hle _ (Proofs.BellmanFordExec.getD_mem D u hup)
    have hDt : D.getD t 0 ≤ inf := hle _ (Proofs.BellmanFordExec.getD_mem D t ht)
    refine ⟨?_, ?_⟩
    · intro v hv
      have hv' : v < P.length := by simpa using hv
      by_cases hvt : v = t
      · subst hvt
        right
        refine ⟨e0, he0, ?_, htt, ?_, ?_⟩
        · rw [hu, getD_set_same P v _ (by omega)]
        · rw [hu]
          by_cases hut : u = v
          · subst hut
            rw [getD_set_same D u _ ht]
            omega
          · rw [getD_set_ne D v u _ hut]
            omega
        · rw [hu, hcc]
          by_cases hut : u = v
          · subst hut
            rw [getD_set_same D u _ ht]
            omega
          · rw [getD_set_ne D v u _ hut, getD_set_same D v _ ht]
            try omega
      · rw [getD_set_ne P t v _ hvt]
        rcases h v hv' with h1 | ⟨e, he, hF, hT, hlt, hle'⟩
        · exact Or.inl h1
        · right
          refine ⟨e, he, ?_, hT, ?_, ?_⟩
          · rw [hF]
          · by_cases hFe : F.getD e 0 = t
            · rw [hFe, getD_set_same D t _ ht]
              rw [hFe] at hlt
              omega
            · rw [getD_set_ne D t _ _ hFe]; exact hlt
          · rw [getD_set_ne D t v _ hvt]
            by_cases hFe : F.getD e 0 = t
            · rw [hFe, getD_set_same D t _ ht]
              rw [hFe] at hlt hle'
              omega
            · rw [getD_set_ne D t _ _ hFe]; exact hle'
    · intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact hle x hx
      · rw [hx]; omega
  · rw [if_neg hc, if_neg hc]
    exact ⟨h, hle⟩

theorem passPrefix_par (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D0 P0 : List Int)
    (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n) (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n)
    (hDl : D0.length = n) (hPl : P0.length = n)
    (hle : ∀ x ∈ D0, x ≤ inf) (h : ParInvE inf F T Cc m D0 P0) :
    ∀ t, t ≤ m → ParInvE inf F T Cc m (passPrefix inf F T Cc t D0) (passPrefixP inf F T Cc t D0 P0) ∧
      (∀ x ∈ passPrefix inf F T Cc t D0, x ≤ inf) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨h, hle⟩
  | succ t ih =>
    intro ht
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have htn : T.getD t 0 < n := by
      have : T.getD t 0 = T[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, show t < m by omega]
      rw [this]; exact hTn _ (List.getElem_mem _)
    have hun : F.getD t 0 < n := by
      have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, show t < m by omega]
      rw [this]; exact hFn _ (List.getElem_mem _)
    rw [passPrefix_succ, passPrefixP_succ]
    exact relax_par inf F T Cc m t _ _ (by omega) (by rw [passPrefix_length, passPrefixP_length, hDl, hPl])
      (by rw [passPrefix_length, hDl]; exact htn) (by rw [passPrefix_length, hDl]; exact hun) ih2 ih1

theorem rounds_par (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D0 P0 : List Int)
    (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n) (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n)
    (hDl : D0.length = n) (hPl : P0.length = n)
    (hle : ∀ x ∈ D0, x ≤ inf) (h : ParInvE inf F T Cc m D0 P0) :
    ∀ r, ParInvE inf F T Cc m (roundsL inf F T Cc m r D0) (roundsPL inf F T Cc m r D0 P0) ∧
      (∀ x ∈ roundsL inf F T Cc m r D0, x ≤ inf) := by
  intro r
  induction r with
  | zero => exact ⟨h, hle⟩
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [roundsL, roundsPL, passL]
    exact passPrefix_par inf F T Cc m n _ _ hTl hTn hFl hFn (by rw [roundsL_length, hDl]) (by rw [roundsPL_length, hPl]) ih2 ih1 m (Nat.le_refl _)

theorem parInv_init (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D P : List Int) (hP : ∀ x ∈ P, x = -1) :
    ParInvE inf F T Cc m D P := by
  intro v hv
  left
  exact hP _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
    exact List.getElem_mem hv)

/-- A distance list is stable when no edge from a reached vertex can still relax. -/
def Stable (inf : Int) (F T : List Nat) (Cc : List Int) (m : Nat) (D : List Int) : Prop :=
  ∀ e, e < m → D.getD (F.getD e 0) 0 ≠ inf → D.getD (T.getD e 0) 0 ≤ D.getD (F.getD e 0) 0 + Cc.getD e 0

theorem markEdge_id (inf : Int) (F T : List Nat) (Cc : List Int) (m e : Nat) (D P : List Int) (he : e < m)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) (hu : F.getD e 0 < D.length) :
    markEdge inf F T Cc e (D, P) = (D, P) := by
  have h1 : D.getD (F.getD e 0) 0 ≠ -inf := hneg _ (Proofs.BellmanFordExec.getD_mem D _ hu)
  show (if D.getD (F.getD e 0) 0 ≠ inf then markIn inf F T Cc e (D, P) else (D, P)) = (D, P)
  by_cases h0 : D.getD (F.getD e 0) 0 = inf
  · rw [if_neg (fun h => h h0)]
  · have h2 := hst e he h0
    rw [if_pos h0]
    show (if D.getD (F.getD e 0) 0 = -inf then (D.set (T.getD e 0) (-inf), P.set (T.getD e 0) (-1))
      else if D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0 then (D.set (T.getD e 0) (-inf), P.set (T.getD e 0) (-1))
      else (D, P)) = (D, P)
    rw [if_neg h1, if_neg (not_lt.mpr h2)]

theorem markPrefix_id (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D P : List Int)
    (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n) (hDl : D.length = n)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) :
    ∀ t, t ≤ m → markPrefix inf F T Cc t (D, P) = (D, P) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hu : F.getD t 0 < D.length := by
      have : F.getD t 0 = F[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hFl, show t < m by omega]
      rw [this, hDl]; exact hFn _ (List.getElem_mem _)
    rw [markPrefix_succ, ih (by omega)]
    exact markEdge_id inf F T Cc m t D P (by omega) hst hneg hu

theorem markRounds_id (inf : Int) (F T : List Nat) (Cc : List Int) (m n : Nat) (D P : List Int)
    (hFl : F.length = m) (hFn : ∀ x ∈ F, x < n) (hDl : D.length = n)
    (hst : Stable inf F T Cc m D) (hneg : ∀ x ∈ D, x ≠ -inf) :
    ∀ r, markRounds inf F T Cc m r (D, P) = (D, P) := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [markRounds]
    rw [ih]
    exact markPrefix_id inf F T Cc m n D P hFl hFn hDl hst hneg m (Nat.le_refl _)

end Proofs.BellmanFordParent
