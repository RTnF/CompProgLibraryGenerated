import Proofs.BellmanFordExec

namespace Proofs.BellmanFordBridge
open Proofs.BellmanFordMath Proofs.BellmanFordExec

/-- The distance list as a function on vertices. -/
def fnOf (D : List Int) : Nat → Int := fun j => D.getD j 0

/-- The edges `(from[e], to[e], cost[e])` for `e < m`. -/
def edgesOf (F T : List Nat) (Cc : List Int) (m : Nat) : List Edge :=
  (List.range m).map (fun e => (F.getD e 0, T.getD e 0, Cc.getD e 0))

theorem fnOf_set (D : List Int) (v : Nat) (x : Int) (hv : v < D.length) :
    fnOf (D.set v x) = BellmanFordMath.upd (fnOf D) v x := by
  funext j
  unfold fnOf BellmanFordMath.upd
  by_cases h : j = v
  · subst h; simp [List.getD_eq_getElem?_getD, hv]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set, h, Ne.symm h]

theorem fnOf_relaxL (inf : Int) (F T : List Nat) (Cc : List Int) (e : Nat) (D : List Int) (hv : T.getD e 0 < D.length) :
    fnOf (relaxL inf F T Cc e D) = relax inf (fnOf D) (F.getD e 0, T.getD e 0, Cc.getD e 0) := by
  unfold relaxL relax
  show fnOf (if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
      then D.set (T.getD e 0) (D.getD (F.getD e 0) 0 + Cc.getD e 0) else D) =
    (if D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
      then BellmanFordMath.upd (fnOf D) (T.getD e 0) (D.getD (F.getD e 0) 0 + Cc.getD e 0) else fnOf D)
  by_cases h : D.getD (F.getD e 0) 0 ≠ inf ∧ D.getD (F.getD e 0) 0 + Cc.getD e 0 < D.getD (T.getD e 0) 0
  · rw [if_pos h, if_pos h]
    exact fnOf_set D _ _ hv
  · rw [if_neg h, if_neg h]


theorem edgesOf_length (F T : List Nat) (Cc : List Int) (m : Nat) : (edgesOf F T Cc m).length = m := by
  simp [edgesOf]

theorem edgesOf_take (F T : List Nat) (Cc : List Int) (m t : Nat) (ht : t < m) :
    (edgesOf F T Cc m).take (t + 1) = (edgesOf F T Cc m).take t ++ [(F.getD t 0, T.getD t 0, Cc.getD t 0)] := by
  have h1 : (edgesOf F T Cc m)[t]? = some (F.getD t 0, T.getD t 0, Cc.getD t 0) := by
    simp [edgesOf, ht]
  rw [List.take_succ, h1]
  rfl

theorem passPrefix_fn (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) (n m : Nat)
    (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) :
    ∀ t, t ≤ m → fnOf (passPrefix inf F T Cc t D0) = ((edgesOf F T Cc m).take t).foldl (relax inf) (fnOf D0) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hv : T.getD t 0 < n := by
      have : T.getD t 0 = T[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hTl, show t < m by omega]
      rw [this]; exact hTn _ (List.getElem_mem _)
    rw [passPrefix_succ, edgesOf_take F T Cc m t (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
    exact fnOf_relaxL inf F T Cc t _ (by rw [passPrefix_length, hDl]; exact hv)

theorem passL_fn (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) (n m : Nat)
    (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) :
    fnOf (passL inf F T Cc m D0) = pass inf (edgesOf F T Cc m) (fnOf D0) := by
  unfold passL pass
  rw [passPrefix_fn inf F T Cc D0 n m hTl hTn hDl m (Nat.le_refl _), List.take_of_length_le (by rw [edgesOf_length])]

theorem rounds_succ_r (inf : Int) (E : List Edge) : ∀ (r : Nat) (d : Nat → Int),
    rounds inf E (r + 1) d = pass inf E (rounds inf E r d)
  | 0, d => rfl
  | r + 1, d => by
    show rounds inf E (r + 1) (pass inf E d) = _
    rw [rounds_succ_r inf E r (pass inf E d)]
    rfl

theorem roundsL_fn (inf : Int) (F T : List Nat) (Cc : List Int) (D0 : List Int) (n m : Nat)
    (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n) (hDl : D0.length = n) :
    ∀ r, fnOf (roundsL inf F T Cc m r D0) = rounds inf (edgesOf F T Cc m) r (fnOf D0) := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [rounds_succ_r]
    simp only [roundsL]
    rw [passL_fn inf F T Cc _ n m hTl hTn (by rw [roundsL_length, hDl]), ih]


/-- What `bellman_ford` computes: every known distance is the cost of a walk from a source, and (when `inf` exceeds the cost of
every walk of at most `n - 1` edges) every such walk bounds the distance. -/
theorem bf_spec (inf : Int) (F T : List Nat) (Cc D0 : List Int) (n m : Nat) (hTl : T.length = m) (hTn : ∀ x ∈ T, x < n)
    (hDl : D0.length = n) :
    (roundsL inf F T Cc m (n - 1) D0).length = n ∧
    (∀ v, (roundsL inf F T Cc m (n - 1) D0).getD v 0 ≠ inf → ∃ w c k, D0.getD w 0 ≠ inf ∧
      Walk (edgesOf F T Cc m) w v c k ∧ (roundsL inf F T Cc m (n - 1) D0).getD v 0 = D0.getD w 0 + c) ∧
    ((∀ w v c k, k ≤ n - 1 → Walk (edgesOf F T Cc m) w v c k → D0.getD w 0 < inf → D0.getD w 0 + c < inf) →
      ∀ w v c k, k ≤ n - 1 → D0.getD w 0 < inf → Walk (edgesOf F T Cc m) w v c k →
        (roundsL inf F T Cc m (n - 1) D0).getD v 0 ≤ D0.getD w 0 + c) := by
  have hf := roundsL_fn inf F T Cc D0 n m hTl hTn hDl (n - 1)
  refine ⟨by rw [roundsL_length, hDl], ?_, ?_⟩
  · intro v hv
    have hs := sound_rounds inf (edgesOf F T Cc m) (fnOf D0) (n - 1) (fnOf D0) (sound_init inf _ _)
    have hv' : rounds inf (edgesOf F T Cc m) (n - 1) (fnOf D0) v ≠ inf := by
      rw [← hf]; exact hv
    obtain ⟨w, c, k, h0, wk, hd⟩ := hs v hv'
    refine ⟨w, c, k, h0, wk, ?_⟩
    have : (roundsL inf F T Cc m (n - 1) D0).getD v 0 = rounds inf (edgesOf F T Cc m) (n - 1) (fnOf D0) v := by
      rw [← hf]; rfl
    rw [this]; exact hd
  · intro hS w v c k hk h0 wk
    have hc := comp_rounds inf (edgesOf F T Cc m) (fnOf D0) (n - 1) hS (n - 1) (Nat.le_refl _) w v c k hk h0 wk
    have : (roundsL inf F T Cc m (n - 1) D0).getD v 0 = rounds inf (edgesOf F T Cc m) (n - 1) (fnOf D0) v := by
      rw [← hf]; rfl
    rw [this]; exact hc

end Proofs.BellmanFordBridge
