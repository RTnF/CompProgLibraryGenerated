import Proofs.Cpp.Gen.FloydWarshall
import Proofs.Cpp.Lib.Basic
import Proofs.FloydWarshallCall

/-! # `floyd_warshall` (library/graph/floyd_warshall.hpp)

Warshall-Floyd in place, on a flat row-major matrix and on a vector of rows. The loops keep the matrix equal to
`Em W k i j` of `Proofs.FloydWarshallCall` (round `k`, rows `< i` and the first `j` entries of row `i` updated); after
the last round it is `Dm W n`, the shortest walk lengths (`Walk_ge`, `Walk_exists`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.FloydWarshallCall

namespace Proofs.Cpp.FloydWarshall

/-- The weights of the input matrix (row-major, `N × N`). -/
def Wf (d0 : Array Int) (N : Nat) : Nat → Nat → Nat := fun p q => (d0[p * N + q]!).toNat

/-- The flat matrix holds `Em W k i j` (round `k`, rows `< i` and the first `j` entries of row `i` done). -/
def FInv (W : Nat → Nat → Nat) (N k i j : Nat) (d : Array Int) : Prop :=
  d.size = N * N ∧ ∀ p q : Nat, p < N → q < N → d[p * N + q]! = (Em W k i j p q : Int)

theorem idx (N p q : Nat) : ((p : Int) * (N : Int) + (q : Int)).toNat = p * N + q := by
  rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]

theorem fstep (W : Nat → Nat → Nat) (N K I J : Nat) (hK : K < N) (hI : I < N) (hJ : J < N) (d : Array Int)
    (h : FInv W N K I J d) :
    (get d (I * N + K) + get d (K * N + J) < get d (I * N + J) →
      FInv W N K I (J + 1) (set d (I * N + J) (get d (I * N + K) + get d (K * N + J)))) ∧
    (¬get d (I * N + K) + get d (K * N + J) < get d (I * N + J) → FInv W N K I (J + 1) d) := by
  obtain ⟨hs, he⟩ := h
  have ga : get d (I * N + K) = (Dm W K I K : Int) := by rw [get_eq, idx, he I K hI hK, Em_col]
  have gb : get d (K * N + J) = (Dm W K K J : Int) := by rw [get_eq, idx, he K J hK hJ, Em_row]
  have gc : get d (I * N + J) = (Dm W K I J : Int) := by rw [get_eq, idx, he I J hI hJ, Em_here]
  have hD : Dm W (K + 1) I J = min (Dm W K I J) (Dm W K I K + Dm W K K J) := rfl
  have hlt : I * N + J < N * N := idx_lt N I J hI hJ
  rw [ga, gb, gc]
  refine ⟨fun hv => ⟨by simp [hs], fun p q hp hq => ?_⟩, fun hv => ⟨hs, fun p q hp hq => ?_⟩⟩
  · rw [getElem!_set _ _ _ _ (by rw [idx]; omega), idx]
    by_cases hpq : p = I ∧ q = J
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_pos rfl, Em_next, hD]; push_cast at hv ⊢; omega
    · have hne : p * N + q ≠ I * N + J := fun e => hpq (idx_inj N p q I J hq hJ e)
      rw [if_neg hne, Em_other _ _ _ _ _ _ hpq, he p q hp hq]
  · by_cases hpq : p = I ∧ q = J
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [Em_next, hD, he p q hp hq, Em_here]; push_cast at hv ⊢; omega
    · rw [Em_other _ _ _ _ _ _ hpq, he p q hp hq]

theorem cur_eq {N : Nat} {pref suff : List Int} {c : Int} (h : range 0 (N : Int) = pref ++ c :: suff) :
    c = (pref.length : Int) ∧ pref.length < N := by
  have e := range_cursor h
  have l := range_prefix_length h
  simp at e l; exact ⟨e, l⟩

theorem fstep' (W : Nat → Nat → Nat) (N : Nat) (pk pi pj sk si sj : List Int) (ck ci cj : Int)
    (hk : range 0 (N : Int) = pk ++ ck :: sk) (hi : range 0 (N : Int) = pi ++ ci :: si)
    (hj : range 0 (N : Int) = pj ++ cj :: sj) (d : Array Int) (h : FInv W N pk.length pi.length pj.length d) :
    (get d (ci * N + ck) + get d (ck * N + cj) < get d (ci * N + cj) →
      FInv W N pk.length pi.length (pj.length + 1) (set d (ci * N + cj) (get d (ci * N + ck) + get d (ck * N + cj)))) ∧
    (¬get d (ci * N + ck) + get d (ck * N + cj) < get d (ci * N + cj) →
      FInv W N pk.length pi.length (pj.length + 1) d) := by
  obtain ⟨rfl, hK⟩ := cur_eq hk
  obtain ⟨rfl, hI⟩ := cur_eq hi
  obtain ⟨rfl, hJ⟩ := cur_eq hj
  exact fstep W N _ _ _ hK hI hJ d h

theorem row_end (W : Nat → Nat → Nat) (N K I : Nat) (d : Array Int) (h : FInv W N K I N d) :
    FInv W N K (I + 1) 0 d :=
  ⟨h.1, fun p q hp hq => by rw [h.2 p q hp hq, Em_row_end _ _ _ _ _ _ hq]⟩

theorem round_end (W : Nat → Nat → Nat) (N K : Nat) (d : Array Int) (h : FInv W N K N 0 d) :
    FInv W N (K + 1) 0 0 d :=
  ⟨h.1, fun p q hp hq => by rw [h.2 p q hp hq, Em_end _ _ _ _ _ hp, Em_start]⟩

theorem finit (d : Array Int) (N : Nat) (hsz : d.size = N * N) (hnn : ∀ k : Nat, 0 ≤ d[k]!) :
    FInv (Wf d N) N 0 0 0 d :=
  ⟨hsz, fun p q hp hq => by rw [Em_start]; simp only [Dm, Wf]; have := hnn (p * N + q); omega⟩

/-- `floyd_warshall(d, n)` on a flat `n × n` matrix with nonnegative entries: `d[p * n + q]` becomes `Dm W n p q`;
`1 + n (1 + n (1 + n))` steps. -/
theorem floyd_warshall_vec_int_spec (d : Array Int) (N : Nat) (hsz : d.size = N * N)
    (hnn : ∀ k : Nat, 0 ≤ d[k]!) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.floyd_warshall_vec_int (T := Int) d N
    ⦃⇓ r c => ⌜r.size = N * N ∧ (∀ p q : Nat, p < N → q < N → r[p * N + q]! = (Dm (Wf d N) N p q : Int)) ∧
               c = t0 + 1 + N * (1 + N * (1 + N))⌝⦄ := by
  mvcgen [cp.floyd_warshall_vec_int]
  case inv1 => exact ⇓⟨xs, a⟩ c => ⌜FInv (Wf d N) N xs.prefix.length 0 0 a ∧
    c = t0 + 1 + xs.prefix.length * (1 + N * (1 + N))⌝
  case inv2 =>
    rename_i pk _ _ _ _ _ _
    exact ⇓⟨xs, a⟩ c => ⌜FInv (Wf d N) N pk.length xs.prefix.length 0 a ∧
      c = t0 + 1 + pk.length * (1 + N * (1 + N)) + 1 + xs.prefix.length * (1 + N)⌝
  case inv3 =>
    rename_i pk _ _ _ _ _ _ pi _ _ _ _ _ _
    exact ⇓⟨xs, a⟩ c => ⌜FInv (Wf d N) N pk.length pi.length xs.prefix.length a ∧
      c = t0 + 1 + pk.length * (1 + N * (1 + N)) + 1 + pi.length * (1 + N) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ _ _ _ ∧ _ = _ + 1 + _›
    exact ⟨(fstep' _ N _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) _ hI).1 ‹_›, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ _ _ _ ∧ _ = _ + 1 + _›
    exact ⟨(fstep' _ N _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) _ hI).2 (Int.not_lt.mpr ‹_›), by omega⟩
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ _ _ _ ∧ _›
    exact ⟨hI, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ _ N _ ∧ _›
    refine ⟨row_end _ _ _ _ _ hI, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ 0 0 _ ∧ _›
    exact ⟨hI, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹FInv _ N _ N 0 _ ∧ _›
    refine ⟨round_end _ _ _ _ hI, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · exact ⟨finit d N hsz hnn, ‹_›⟩
  · obtain ⟨hI, hc⟩ := ‹FInv _ N N 0 0 _ ∧ _›
    exact ⟨hI.1, fun p q hp hq => by rw [hI.2 p q hp hq, Em_start], hc⟩

/-! ## The matrix as a vector of rows -/

/-- The weights of the input matrix of rows. -/
def Wr (d0 : Array (Array Int)) : Nat → Nat → Nat := fun p q => ((d0[p]!)[q]!).toNat

/-- The matrix of rows holds `Em W k i j`. -/
def NInv (W : Nat → Nat → Nat) (N k i j : Nat) (d : Array (Array Int)) : Prop :=
  d.size = N ∧ (∀ p : Nat, p < N → (d[p]!).size = N) ∧
    ∀ p q : Nat, p < N → q < N → (d[p]!)[q]! = (Em W k i j p q : Int)

theorem nstep' (W : Nat → Nat → Nat) (N : Nat) (pk pi pj sk si sj : List Int) (ck ci cj : Int)
    (hk : range 0 (N : Int) = pk ++ ck :: sk) (hi : range 0 (N : Int) = pi ++ ci :: si)
    (hj : range 0 (N : Int) = pj ++ cj :: sj) (d : Array (Array Int)) (h : NInv W N pk.length pi.length pj.length d) :
    (get (get d ci) ck + get (get d ck) cj < get (get d ci) cj →
      NInv W N pk.length pi.length (pj.length + 1)
        (set d ci (set (get d ci) cj (get (get d ci) ck + get (get d ck) cj)))) ∧
    (¬get (get d ci) ck + get (get d ck) cj < get (get d ci) cj →
      NInv W N pk.length pi.length (pj.length + 1) d) := by
  obtain ⟨rfl, hK⟩ := cur_eq hk
  obtain ⟨rfl, hI⟩ := cur_eq hi
  obtain ⟨rfl, hJ⟩ := cur_eq hj
  set K := pk.length
  set I := pi.length
  set J := pj.length
  obtain ⟨hs, hr, he⟩ := h
  have ga : get (get d I) K = (Dm W K I K : Int) := by simp only [get_eq, Int.toNat_natCast]; rw [he I K hI hK, Em_col]
  have gb : get (get d K) J = (Dm W K K J : Int) := by simp only [get_eq, Int.toNat_natCast]; rw [he K J hK hJ, Em_row]
  have gc : get (get d I) J = (Dm W K I J : Int) := by simp only [get_eq, Int.toNat_natCast]; rw [he I J hI hJ, Em_here]
  have hD : Dm W (K + 1) I J = min (Dm W K I J) (Dm W K I K + Dm W K K J) := rfl
  rw [ga, gb, gc]
  refine ⟨fun hv => ⟨by simp [hs], fun p hp => ?_, fun p q hp hq => ?_⟩, fun hv => ⟨hs, hr, fun p q hp hq => ?_⟩⟩
  · rw [getElem!_set _ _ _ _ (by simp; omega)]
    by_cases hpi : p = I
    · simp only [Int.toNat_natCast, hpi, ite_true, size_set, get_eq]; exact hr I hI
    · simp only [Int.toNat_natCast, hpi, ite_false]; exact hr p hp
  · rw [getElem!_set _ _ _ _ (by simp; omega)]
    by_cases hpi : p = I
    · subst hpi
      simp only [Int.toNat_natCast, ite_true]
      rw [getElem!_set _ _ _ _ (by simp [get_eq]; rw [hr _ hp]; omega)]
      by_cases hqj : q = J
      · subst hqj; rw [if_pos (by simp), Em_next, hD]; push_cast at hv ⊢; omega
      · rw [if_neg (by simp; omega), Em_other _ _ _ _ _ _ (fun e => hqj e.2), get_eq, Int.toNat_natCast, he _ q hp hq]
    · simp only [Int.toNat_natCast, hpi, ite_false]
      rw [Em_other _ _ _ _ _ _ (fun e => hpi e.1), he p q hp hq]
  · by_cases hpq : p = I ∧ q = J
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [Em_next, hD, he _ _ hp hq, Em_here]; push_cast at hv ⊢; omega
    · rw [Em_other _ _ _ _ _ _ hpq, he p q hp hq]

theorem nrow_end (W : Nat → Nat → Nat) (N K I : Nat) (d : Array (Array Int)) (h : NInv W N K I N d) :
    NInv W N K (I + 1) 0 d :=
  ⟨h.1, h.2.1, fun p q hp hq => by rw [h.2.2 p q hp hq, Em_row_end _ _ _ _ _ _ hq]⟩

theorem nround_end (W : Nat → Nat → Nat) (N K : Nat) (d : Array (Array Int)) (h : NInv W N K N 0 d) :
    NInv W N (K + 1) 0 0 d :=
  ⟨h.1, h.2.1, fun p q hp hq => by rw [h.2.2 p q hp hq, Em_end _ _ _ _ _ hp, Em_start]⟩

/-- `floyd_warshall(d)` on a square matrix of rows with nonnegative entries: `d[p][q]` becomes `Dm W n p q`, the
shortest walk length from `p` to `q` (`Walk_ge`, `Walk_exists`); `1 + n (1 + n (1 + n))` steps. -/
theorem floyd_warshall_vec_spec (d : Array (Array Int)) (hr : ∀ p : Nat, p < d.size → (d[p]!).size = d.size)
    (hnn : ∀ p q : Nat, 0 ≤ (d[p]!)[q]!) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.floyd_warshall_vec (T := Int) d
    ⦃⇓ r c => ⌜r.size = d.size ∧ (∀ p : Nat, p < d.size → (r[p]!).size = d.size) ∧
               (∀ p q : Nat, p < d.size → q < d.size → (r[p]!)[q]! = (Dm (Wr d) d.size p q : Int)) ∧
               c = t0 + 1 + d.size * (1 + d.size * (1 + d.size))⌝⦄ := by
  mvcgen [cp.floyd_warshall_vec]
  case inv1 => exact ⇓⟨xs, a⟩ c => ⌜NInv (Wr d) d.size xs.prefix.length 0 0 a ∧
    c = t0 + 1 + xs.prefix.length * (1 + d.size * (1 + d.size))⌝
  case inv2 =>
    rename_i pk _ _ _ _ _ _
    exact ⇓⟨xs, a⟩ c => ⌜NInv (Wr d) d.size pk.length xs.prefix.length 0 a ∧
      c = t0 + 1 + pk.length * (1 + d.size * (1 + d.size)) + 1 + xs.prefix.length * (1 + d.size)⌝
  case inv3 =>
    rename_i pk _ _ _ _ _ _ pi _ _ _ _ _ _
    exact ⇓⟨xs, a⟩ c => ⌜NInv (Wr d) d.size pk.length pi.length xs.prefix.length a ∧
      c = t0 + 1 + pk.length * (1 + d.size * (1 + d.size)) + 1 + pi.length * (1 + d.size) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [size] at *
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ _ _ _ ∧ _ = _ + 1 + _›
    exact ⟨(nstep' _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) _ hI).1 ‹_›, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ _ _ _ ∧ _ = _ + 1 + _›
    exact ⟨(nstep' _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) _ hI).2
      (Int.not_lt.mpr ‹_›), by omega⟩
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ _ _ _ ∧ _›
    exact ⟨hI, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ _ d.size _ ∧ _›
    refine ⟨nrow_end _ _ _ _ _ hI, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ 0 0 _ ∧ _›
    exact ⟨hI, by omega⟩
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ _ d.size 0 _ ∧ _›
    refine ⟨nround_end _ _ _ _ hI, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]; omega
  · refine ⟨⟨rfl, fun p hp => hr p hp, fun p q hp hq => ?_⟩, ‹_›⟩
    rw [Em_start]; simp only [Dm, Wr]; have := hnn p q; omega
  · obtain ⟨hI, hc⟩ := ‹NInv _ _ d.size 0 0 _ ∧ _›
    exact ⟨hI.1, hI.2.1, fun p q hp hq => by rw [hI.2.2 p q hp hq, Em_start], hc⟩

end Proofs.Cpp.FloydWarshall
