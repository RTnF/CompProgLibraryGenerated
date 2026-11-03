import Proofs.DijkstraMath

/-! Dijkstra with the parent array: relaxing an edge that lowers `dist[w]` also sets `parent[w]` to the finalised vertex. -/
namespace Proofs.DijkstraPMath
open Proofs.BellmanFordMath Proofs.DijkstraMath

def updI (p : Nat → Int) (i : Nat) (x : Int) : Nat → Int := fun j => if j = i then x else p j

/-- Relax one edge on the pair `(dist, parent)`. -/
def relaxP (inf : Int) (s : (Nat → Int) × (Nat → Int)) (e : Edge) : (Nat → Int) × (Nat → Int) :=
  if s.1 e.1 ≠ inf ∧ s.1 e.1 + e.2.2 < s.1 e.2.1 then (upd s.1 e.2.1 (s.1 e.1 + e.2.2), updI s.2 e.2.1 (e.1 : Int)) else s

def relaxOutP (inf : Int) (outE : Nat → List Edge) (b : Nat) (s : (Nat → Int) × (Nat → Int)) : (Nat → Int) × (Nat → Int) :=
  (outE b).foldl (relaxP inf) s

theorem relaxP_fst (inf : Int) (s : (Nat → Int) × (Nat → Int)) (e : Edge) : (relaxP inf s e).1 = relax inf s.1 e := by
  unfold relaxP relax
  by_cases h : s.1 e.1 ≠ inf ∧ s.1 e.1 + e.2.2 < s.1 e.2.1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem foldP_fst (inf : Int) : ∀ (L : List Edge) (s : (Nat → Int) × (Nat → Int)),
    (L.foldl (relaxP inf) s).1 = L.foldl (relax inf) s.1
  | [], s => rfl
  | e :: L, s => by
    simp only [List.foldl_cons]
    rw [foldP_fst inf L (relaxP inf s e), relaxP_fst]

theorem relaxOutP_fst (inf : Int) (outE : Nat → List Edge) (b : Nat) (s : (Nat → Int) × (Nat → Int)) :
    (relaxOutP inf outE b s).1 = relaxOut inf outE b s.1 := foldP_fst inf _ s

/-- Every parent entry is its initial value or an edge from a finalised vertex that realises the distance. -/
def ParInv (outE : Nat → List Edge) (D : List Nat) (d p p0 : Nat → Int) : Prop :=
  ∀ v, p v = p0 v ∨ ∃ u : Nat, p v = (u : Int) ∧ u ∈ D ∧ ∃ e ∈ outE u, e.2.1 = v ∧ d v = d u + e.2.2

/-- The state of the loop over the edges leaving `b`: `d b` and the finalised distances stay, and the parent entries keep the
invariant with `b` counted as finalised. -/
def FoldInv (outE : Nat → List Edge) (D : List Nat) (b : Nat) (dS d p p0 : Nat → Int) : Prop :=
  d b = dS b ∧ (∀ u ∈ D, d u = dS u) ∧ ParInv outE (D ++ [b]) d p p0

theorem par_fold (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (dS : Nat → Int) (D : List Nat)
    (p0 : Nat → Int) (b : Nat) (hb : b < n) (hbf : dS b < inf)
    (hmin : ∀ v ∈ D, dS v ≤ dS b) :
    ∀ (L : List Edge), (∀ e ∈ L, e ∈ outE b) → ∀ (s : (Nat → Int) × (Nat → Int)),
      FoldInv outE D b dS s.1 s.2 p0 → FoldInv outE D b dS (L.foldl (relaxP inf) s).1 (L.foldl (relaxP inf) s).2 p0
  | [], _, s, h => h
  | e :: L, hL, s, h => by
    simp only [List.foldl_cons]
    apply par_fold n inf outE G dS D p0 b hb hbf hmin L (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
    have heb : e ∈ outE b := hL e List.mem_cons_self
    obtain ⟨he1, hw, hc⟩ := G.out b hb e heb
    obtain ⟨hdb, hD, hpar⟩ := h
    unfold relaxP
    by_cases hf : s.1 e.1 ≠ inf ∧ s.1 e.1 + e.2.2 < s.1 e.2.1
    · rw [if_pos hf]
      have hwb : e.2.1 ≠ b := by
        intro hwb
        have := hf.2
        rw [hwb, he1] at this
        omega
      have hwD : e.2.1 ∉ D := by
        intro hwD
        have h1 := hmin e.2.1 hwD
        have h2 := hD e.2.1 hwD
        have := hf.2
        rw [he1, hdb, h2] at this
        omega
      refine ⟨?_, ?_, ?_⟩
      · show upd s.1 e.2.1 _ b = dS b
        rw [upd_ne _ _ _ _ (fun h => hwb h.symm)]; exact hdb
      · intro u hu
        have : u ≠ e.2.1 := fun h => hwD (h ▸ hu)
        show upd s.1 e.2.1 _ u = dS u
        rw [upd_ne _ _ _ _ this]; exact hD u hu
      · intro v
        by_cases hv : v = e.2.1
        · right
          refine ⟨b, ?_, List.mem_append_right _ (List.mem_singleton_self b), e, heb, hv.symm, ?_⟩
          · show updI s.2 e.2.1 (e.1 : Int) v = b
            rw [hv]; simp [updI, he1]
          · show upd s.1 e.2.1 (s.1 e.1 + e.2.2) v = upd s.1 e.2.1 (s.1 e.1 + e.2.2) b + e.2.2
            rw [hv, upd_same, upd_ne _ _ _ _ (fun h => hwb h.symm), he1, hdb]
        · rcases hpar v with h1 | ⟨u, hu1, hu2, e', he', he'1, he'2⟩
          · left
            show updI s.2 e.2.1 (e.1 : Int) v = p0 v
            simp [updI, hv, h1]
          · right
            have hu : u ≠ e.2.1 := by
              intro huw
              rcases List.mem_append.mp hu2 with h3 | h3
              · exact hwD (huw ▸ h3)
              · exact hwb (huw ▸ List.mem_singleton.mp h3)
            refine ⟨u, ?_, hu2, e', he', he'1, ?_⟩
            · show updI s.2 e.2.1 (e.1 : Int) v = u
              simp [updI, hv, hu1]
            · show upd s.1 e.2.1 _ v = upd s.1 e.2.1 _ u + e'.2.2
              rw [upd_ne _ _ _ _ hv, upd_ne _ _ _ _ hu]; exact he'2
    · rw [if_neg hf]
      exact ⟨hdb, hD, hpar⟩

/-- One outer iteration on the parent array: the vertex picked is the one of `djStep`. -/
def pStep (inf : Int) (outE : Nat → List Edge) (n : Nat) (st : (Nat → Int) × List Nat) (p : Nat → Int) : Nat → Int :=
  match (scanRes inf n st.1 st.2).1 with
  | none => p
  | some b => (relaxOutP inf outE b (st.1, p)).2

/-- The parent array after `t` outer iterations (the vertex picked in each iteration is the one of `djIter`). -/
def pIter (inf : Int) (outE : Nat → List Edge) (n : Nat) (d0 : Nat → Int) (p0 : Nat → Int) : Nat → (Nat → Int)
  | 0 => p0
  | t + 1 =>
    match (scanRes inf n (djIter inf outE n d0 t).1 (djIter inf outE n d0 t).2).1 with
    | none => pIter inf outE n d0 p0 t
    | some b => (relaxOutP inf outE b ((djIter inf outE n d0 t).1, pIter inf outE n d0 p0 t)).2

theorem pIter_succ (inf : Int) (outE : Nat → List Edge) (n : Nat) (d0 p0 : Nat → Int) (t : Nat) :
    pIter inf outE n d0 p0 (t + 1) = pStep inf outE n (djIter inf outE n d0 t) (pIter inf outE n d0 p0 t) := rfl

theorem parInv_mono (outE : Nat → List Edge) (D : List Nat) (b : Nat) (d p p0 : Nat → Int)
    (h : ParInv outE D d p p0) : ParInv outE (D ++ [b]) d p p0 := by
  intro v
  rcases h v with h1 | ⟨u, hu, hD, e, he, he1, he2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨u, hu, List.mem_append_left _ hD, e, he, he1, he2⟩

theorem pIter_inv (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 : Nat → Int)
    (hd0 : ∀ w, d0 w < inf → w < n) (p0 : Nat → Int) :
    ∀ t, ParInv outE (djIter inf outE n d0 t).2 (djIter inf outE n d0 t).1 (pIter inf outE n d0 p0 t) p0 := by
  intro t
  induction t with
  | zero =>
    intro v
    exact Or.inl rfl
  | succ t ih =>
    have hI := (djIter_inv n inf outE G d0 hd0 t).1
    rw [djIter_succ]
    unfold pIter djStep
    generalize hst : djIter inf outE n d0 t = st at ih hI
    have P := scan_inv inf st.1 st.2 n
    unfold scanRes
    rcases hr : ((List.range n).foldl (scanStep inf st.1 st.2) (none, inf)).1 with _ | b
    · simp only [hst, scanRes, hr]
      exact ih
    · have hb := P.some b hr
      simp only [hst, scanRes, hr]
      have hbf : st.1 b < inf := by have := hb.2.2.1; have := hb.2.2.2.1; omega
      have hmin : ∀ v ∈ st.2, st.1 v ≤ st.1 b := fun v hv => hI.mono4 v hv b hb.1 hb.2.1
      have F := par_fold n inf outE G st.1 st.2 p0 b hb.1 hbf hmin (outE b) (fun e he => he)
        (st.1, pIter inf outE n d0 p0 t) ⟨rfl, fun u _ => rfl, parInv_mono outE st.2 b _ _ _ ih⟩
      have h1 := relaxOutP_fst inf outE b (st.1, pIter inf outE n d0 p0 t)
      have h2 : (relaxOutP inf outE b (st.1, pIter inf outE n d0 p0 t)).1 = relaxOut inf outE b st.1 := h1
      show ParInv outE (st.2 ++ [b]) (relaxOut inf outE b st.1) _ p0
      rw [← h2]
      exact F.2.2

/-- A parent function as a list of length `n`. -/
def ofFnI (n : Nat) (f : Nat → Int) : List Int := (List.range n).map f

theorem ofFnI_length (n : Nat) (f : Nat → Int) : (ofFnI n f).length = n := by simp [ofFnI]

theorem ofFnI_set (n : Nat) (f : Nat → Int) (w : Nat) (x : Int) (hw : w < n) :
    (ofFnI n f).set w x = ofFnI n (updI f w x) := by
  apply List.ext_getElem
  · simp [ofFnI]
  · intro j h1 h2
    rw [List.getElem_set]
    simp only [ofFnI, List.getElem_map, List.getElem_range]
    unfold updI
    by_cases h : w = j
    · subst h; simp
    · simp [h, Ne.symm h]

theorem ofFnI_relaxP (n : Nat) (inf : Int) (s : (Nat → Int) × (Nat → Int)) (e : Edge) (he : e.2.1 < n) (hf : s.1 e.1 ≠ inf) :
    ofFnI n (relaxP inf s e).2 =
      if s.1 e.1 + e.2.2 < s.1 e.2.1 then (ofFnI n s.2).set e.2.1 (e.1 : Int) else ofFnI n s.2 := by
  unfold relaxP
  by_cases h : s.1 e.1 + e.2.2 < s.1 e.2.1
  · rw [if_pos ⟨hf, h⟩, if_pos h, ofFnI_set n s.2 _ _ he]
  · rw [if_neg (fun hh => h hh.2), if_neg h]

/-- Relaxing the first `d` edges of `L` in order, on the pair `(dist, parent)`. -/
def foldRP (inf : Int) (L : List Edge) (s0 : (Nat → Int) × (Nat → Int)) (d : Nat) : (Nat → Int) × (Nat → Int) :=
  (L.take d).foldl (relaxP inf) s0

theorem foldRP_succ (inf : Int) (L : List Edge) (s0 : (Nat → Int) × (Nat → Int)) (d : Nat) (hd : d < L.length) :
    foldRP inf L s0 (d + 1) = relaxP inf (foldRP inf L s0 d) L[d] := by
  unfold foldRP
  have h : L.take (d + 1) = L.take d ++ [L[d]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hd]
    rfl
  rw [h, List.foldl_append]
  rfl

theorem foldRP_full (inf : Int) (L : List Edge) (s0 : (Nat → Int) × (Nat → Int)) :
    foldRP inf L s0 L.length = L.foldl (relaxP inf) s0 := by
  unfold foldRP; rw [List.take_length]

end Proofs.DijkstraPMath
