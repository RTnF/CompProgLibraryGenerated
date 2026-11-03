import Proofs.BellmanFordMath

namespace Proofs.DijkstraMath
open Proofs.BellmanFordMath

/-- Relaxing the edges leaving `b` (non-negative costs, `d b` stays) either keeps a value or sets it to `d b + cost`. -/
theorem relax_fold_cases (inf : Int) (b : Nat) :
    ∀ (L : List Edge) (d : Nat → Int), (∀ e ∈ L, e.1 = b ∧ 0 ≤ e.2.2) →
      (L.foldl (relax inf) d) b = d b ∧
      ∀ x, (L.foldl (relax inf) d) x = d x ∨ ∃ e ∈ L, e.2.1 = x ∧ (L.foldl (relax inf) d) x = d b + e.2.2
  | [], d, _ => ⟨rfl, fun x => Or.inl rfl⟩
  | e :: t, d, h => by
    simp only [List.foldl_cons]
    have he := h e (List.mem_cons_self ..)
    have ht : ∀ e' ∈ t, e'.1 = b ∧ 0 ≤ e'.2.2 := fun e' h' => h e' (List.mem_cons_of_mem _ h')
    -- one step
    have hb : relax inf d e b = d b := by
      unfold relax
      by_cases hf : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
      · rw [if_pos hf]
        by_cases hbe : b = e.2.1
        · exfalso
          have h1 := hf.2
          rw [he.1, ← hbe] at h1
          have := he.2
          omega
        · exact upd_ne _ _ _ _ hbe
      · rw [if_neg hf]
    have hx : ∀ x, relax inf d e x = d x ∨ (e.2.1 = x ∧ relax inf d e x = d b + e.2.2) := by
      intro x
      unfold relax
      by_cases hf : d e.1 ≠ inf ∧ d e.1 + e.2.2 < d e.2.1
      · rw [if_pos hf]
        by_cases hxe : x = e.2.1
        · right
          subst hxe
          refine ⟨rfl, ?_⟩
          rw [upd_same, he.1]
        · left; exact upd_ne _ _ _ _ hxe
      · rw [if_neg hf]; left; rfl
    obtain ⟨ih1, ih2⟩ := relax_fold_cases inf b t (relax inf d e) ht
    refine ⟨by rw [ih1, hb], ?_⟩
    intro x
    rcases ih2 x with h2 | ⟨e', he', hxe', hv⟩
    · rcases hx x with h3 | ⟨h3, h4⟩
      · left; rw [h2, h3]
      · right
        refine ⟨e, List.mem_cons_self .., h3, ?_⟩
        rw [h2, h4]
    · right
      refine ⟨e', List.mem_cons_of_mem _ he', hxe', ?_⟩
      rw [hv, hb]


/-- All edges of the graph given by the out-edge lists. -/
def Eall (n : Nat) (outE : Nat → List Edge) : List Edge := (List.range n).flatMap outE

/-- The out-edge lists describe a graph on `0 .. n-1` with non-negative costs. -/
structure Graph (n : Nat) (outE : Nat → List Edge) : Prop where
  out : ∀ u, u < n → ∀ e, e ∈ outE u → e.1 = u ∧ e.2.1 < n ∧ 0 ≤ e.2.2

theorem mem_Eall (n : Nat) (outE : Nat → List Edge) (u : Nat) (hu : u < n) (e : Edge) (he : e ∈ outE u) :
    e ∈ Eall n outE := by
  unfold Eall
  exact List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu, he⟩

theorem mem_Eall_inv (n : Nat) (outE : Nat → List Edge) (e : Edge) (he : e ∈ Eall n outE) :
    ∃ u, u < n ∧ e ∈ outE u := by
  unfold Eall at he
  obtain ⟨u, hu, hmem⟩ := List.mem_flatMap.mp he
  exact ⟨u, List.mem_range.mp hu, hmem⟩

/-- The invariant of Dijkstra's algorithm: `D` is the set of finalized vertices. -/
structure Dj (n : Nat) (inf : Int) (outE : Nat → List Edge) (d0 d : Nat → Int) (D : List Nat) : Prop where
  sound : Sound inf (Eall n outE) d0 d
  done2 : ∀ y ∈ D, ∀ w c k, d0 w < inf → Walk (Eall n outE) w y c k → d y ≤ d0 w + c
  init3 : ∀ v, v < n → v ∉ D → d v ≤ d0 v
  edge3 : ∀ u ∈ D, ∀ e ∈ outE u, e.2.1 ∉ D → d e.2.1 ≤ d u + e.2.2
  mono4 : ∀ v ∈ D, ∀ x, x < n → x ∉ D → d v ≤ d x
  nodup : D.Nodup
  lt : ∀ x ∈ D, x < n

theorem walk_lemma (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 d : Nat → Int) (D : List Nat)
    (hd0 : ∀ w, d0 w < inf → w < n) (I : Dj n inf outE d0 d D) :
    ∀ w y c k, d0 w < inf → Walk (Eall n outE) w y c k →
      (y ∈ D → d y ≤ d0 w + c) ∧ (y ∉ D → ∃ x, x < n ∧ x ∉ D ∧ d x ≤ d0 w + c) := by
  intro w y c k h0 wk
  induction wk with
  | nil =>
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have := I.done2 _ hy w 0 0 h0 (Walk.nil w)
      omega
    · exact ⟨w, hd0 w h0, hy, by have := I.init3 w (hd0 w h0) hy; omega⟩
  | @step c0 k0 e he wk ih =>
    obtain ⟨u, hu, heu⟩ := mem_Eall_inv n outE e he
    obtain ⟨hev, hel, hec⟩ := G.out u hu e heu
    refine ⟨fun hy => I.done2 _ hy w _ _ h0 (Walk.step e he wk), fun hy => ?_⟩
    by_cases hD : e.1 ∈ D
    · have h1 := ih.1 hD
      have h2 := I.edge3 e.1 hD e (by rw [hev]; exact heu) hy
      exact ⟨e.2.1, hel, hy, by omega⟩
    · obtain ⟨x, hx, hxD, hdx⟩ := ih.2 hD
      exact ⟨x, hx, hxD, by omega⟩


/-- Relaxing all edges leaving `b`. -/
def relaxOut (inf : Int) (outE : Nat → List Edge) (b : Nat) (d : Nat → Int) : Nat → Int := (outE b).foldl (relax inf) d

theorem dj_step (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 d : Nat → Int) (D : List Nat)
    (hd0 : ∀ w, d0 w < inf → w < n) (I : Dj n inf outE d0 d D) (b : Nat) (hb : b < n) (hbD : b ∉ D) (hbf : d b < inf)
    (hmin : ∀ x, x < n → x ∉ D → d b ≤ d x) :
    Dj n inf outE d0 (relaxOut inf outE b d) (D ++ [b]) := by
  have hcls : ∀ e ∈ outE b, e.1 = b ∧ 0 ≤ e.2.2 := fun e he => ⟨(G.out b hb e he).1, (G.out b hb e he).2.2⟩
  obtain ⟨hstab, hcases⟩ := relax_fold_cases inf b (outE b) d hcls
  have hle : ∀ x, relaxOut inf outE b d x ≤ d x := fun x => foldl_le inf (outE b) d x
  have hedge : ∀ e ∈ outE b, relaxOut inf outE b d e.2.1 ≤ d b + e.2.2 := by
    intro e he
    have h1 := pass_edge inf (outE b) d e he (by rw [(G.out b hb e he).1]; exact hbf)
    rw [(G.out b hb e he).1] at h1
    exact h1
  have hDeq : ∀ u ∈ D, relaxOut inf outE b d u = d u := by
    intro u hu
    have h1 := I.mono4 u hu b hb hbD
    have h2 := hle u
    rcases hcases u with h3 | ⟨e, he, _, h4⟩
    · exact h3
    · have := (G.out b hb e he).2.2
      have h5 : relaxOut inf outE b d u = d b + e.2.2 := h4
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sound_foldl inf (Eall n outE) d0 (outE b) d (fun e he => mem_Eall n outE b hb e he) I.sound
  · intro y hy w c k h0 wk
    rcases List.mem_append.mp hy with hy | hy
    · have := I.done2 y hy w c k h0 wk
      have := hle y
      omega
    · have hyb : y = b := by simpa using hy
      subst hyb
      have hL := (walk_lemma n inf outE G d0 d D hd0 I w y c k h0 wk).2 hbD
      obtain ⟨x, hx1, hx2, hx3⟩ := hL
      have := hmin x hx1 hx2
      have h5 : relaxOut inf outE y d y = d y := hstab
      omega
  · intro v hv hvD
    have hvD' : v ∉ D := fun h => hvD (List.mem_append.mpr (Or.inl h))
    have := I.init3 v hv hvD'
    have := hle v
    omega
  · intro u hu e he heD
    have heD' : e.2.1 ∉ D := fun h => heD (List.mem_append.mpr (Or.inl h))
    rcases List.mem_append.mp hu with hu | hu
    · have h1 := I.edge3 u hu e he heD'
      have h2 := hle e.2.1
      have h3 := hDeq u hu
      omega
    · have hub : u = b := by simpa using hu
      subst hub
      have h1 := hedge e he
      have h2 : relaxOut inf outE u d u = d u := hstab
      omega
  · intro v hv x hx hxD
    have hxD' : x ∉ D := fun h => hxD (List.mem_append.mpr (Or.inl h))
    have hxb : x ≠ b := fun h => hxD (List.mem_append.mpr (Or.inr (by simp [h])))
    have hbx := hmin x hx hxD'
    have hdx : d b ≤ relaxOut inf outE b d x := by
      rcases hcases x with h3 | ⟨e, he, _, h4⟩
      · have h5 : relaxOut inf outE b d x = d x := h3
        omega
      · have := (G.out b hb e he).2.2
        have h5 : relaxOut inf outE b d x = d b + e.2.2 := h4
        omega
    rcases List.mem_append.mp hv with hv | hv
    · have := I.mono4 v hv b hb hbD
      have := hDeq v hv
      omega
    · have hvb : v = b := by simpa using hv
      subst hvb
      have h2 : relaxOut inf outE v d v = d v := hstab
      omega
  · rw [List.nodup_append]
    exact ⟨I.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
      intro a ha c hc hac
      have : c = b := by simpa using hc
      subst this; subst hac; exact hbD ha⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact I.lt x hx
    · have : x = b := by simpa using hx
      omega


/-- One step of the minimum scan of the code: `if (v is not done && dist[v] < bd) { bd = dist[v]; best = v; }`. -/
def scanStep (inf : Int) (d : Nat → Int) (D : List Nat) (s : Option Nat × Int) (v : Nat) : Option Nat × Int :=
  if v ∉ D ∧ d v < s.2 then (some v, d v) else s

/-- The result of scanning the vertices `0 .. n-1`. -/
def scanRes (inf : Int) (n : Nat) (d : Nat → Int) (D : List Nat) : Option Nat × Int :=
  (List.range n).foldl (scanStep inf d D) (none, inf)

structure PickInv (inf : Int) (d : Nat → Int) (D : List Nat) (k : Nat) (s : Option Nat × Int) : Prop where
  le : s.2 ≤ inf
  none : s.1 = none → s.2 = inf ∧ ∀ x, x < k → x ∉ D → inf ≤ d x
  some : ∀ b, s.1 = some b → b < k ∧ b ∉ D ∧ d b = s.2 ∧ s.2 < inf ∧ ∀ x, x < k → x ∉ D → s.2 ≤ d x

theorem scan_inv (inf : Int) (d : Nat → Int) (D : List Nat) :
    ∀ k, PickInv inf d D k ((List.range k).foldl (scanStep inf d D) (none, inf)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨Int.le_refl _, fun _ => ⟨rfl, fun x hx => by omega⟩, fun b hb => by simp at hb⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize hs : (List.range k).foldl (scanStep inf d D) (none, inf) = s at ih ⊢
    unfold scanStep
    by_cases hg : k ∉ D ∧ d k < s.2
    · rw [if_pos hg]
      refine ⟨by have := ih.le; simp; omega, fun h => by simp at h, fun b hb => ?_⟩
      simp only [Option.some.injEq] at hb
      subst hb
      refine ⟨by omega, hg.1, rfl, by have := ih.le; simp; omega, fun x hx hxD => ?_⟩
      simp only
      by_cases hxk : x = k
      · subst hxk; exact Int.le_refl _
      · have hxl : x < k := by omega
        rcases hs1 : s.1 with _ | b0
        · have := (ih.none hs1).2 x hxl hxD
          have := ih.le
          omega
        · have := (ih.some b0 hs1).2.2.2.2 x hxl hxD
          omega
    · rw [if_neg hg]
      refine ⟨ih.le, fun h => ⟨(ih.none h).1, fun x hx hxD => ?_⟩, fun b hb => ?_⟩
      · by_cases hxk : x = k
        · subst hxk
          have h1 := (ih.none h).1
          have : ¬ d x < s.2 := fun hh => hg ⟨hxD, hh⟩
          omega
        · exact (ih.none h).2 x (by omega) hxD
      · have := ih.some b hb
        refine ⟨by omega, this.2.1, this.2.2.1, this.2.2.2.1, fun x hx hxD => ?_⟩
        by_cases hxk : x = k
        · subst hxk
          have : ¬ d x < s.2 := fun hh => hg ⟨hxD, hh⟩
          omega
        · exact this.2.2.2.2 x (by omega) hxD


/-- One outer iteration `for (it ...)`. -/
def djStep (inf : Int) (outE : Nat → List Edge) (n : Nat) (st : (Nat → Int) × List Nat) (_it : Nat) : (Nat → Int) × List Nat :=
  match (scanRes inf n st.1 st.2).1 with
  | none => st
  | some b => (relaxOut inf outE b st.1, st.2 ++ [b])

def djIter (inf : Int) (outE : Nat → List Edge) (n : Nat) (d0 : Nat → Int) (t : Nat) : (Nat → Int) × List Nat :=
  (List.range t).foldl (djStep inf outE n) (d0, [])

theorem djIter_succ (inf : Int) (outE : Nat → List Edge) (n : Nat) (d0 : Nat → Int) (t : Nat) :
    djIter inf outE n d0 (t + 1) = djStep inf outE n (djIter inf outE n d0 t) t := by
  unfold djIter
  rw [List.range_succ, List.foldl_append]
  rfl

theorem dj_init (n : Nat) (inf : Int) (outE : Nat → List Edge) (d0 : Nat → Int) : Dj n inf outE d0 d0 [] :=
  ⟨sound_init inf _ _, fun y hy => by simp at hy, fun v _ _ => Int.le_refl _, fun u hu => by simp at hu,
   fun v hv => by simp at hv, List.nodup_nil, fun x hx => by simp at hx⟩

theorem djIter_inv (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 : Nat → Int)
    (hd0 : ∀ w, d0 w < inf → w < n) :
    ∀ t, Dj n inf outE d0 (djIter inf outE n d0 t).1 (djIter inf outE n d0 t).2 ∧
      ((djIter inf outE n d0 t).2.length = t ∨
        ∀ x, x < n → x ∉ (djIter inf outE n d0 t).2 → inf ≤ (djIter inf outE n d0 t).1 x) := by
  intro t
  induction t with
  | zero => exact ⟨dj_init n inf outE d0, Or.inl rfl⟩
  | succ t ih =>
    rw [djIter_succ]
    generalize hst : djIter inf outE n d0 t = st at ih ⊢
    obtain ⟨hI, hc⟩ := ih
    unfold djStep
    have P := scan_inv inf st.1 st.2 n
    unfold scanRes
    rcases hr : ((List.range n).foldl (scanStep inf st.1 st.2) (none, inf)).1 with _ | b
    · have h0 : ((List.range n).foldl (scanStep inf st.1 st.2) (none, inf)).1 = none := hr
      simp only []
      refine ⟨hI, Or.inr ?_⟩
      exact (P.none h0).2
    · have hb := P.some b hr
      simp only []
      have hI' := dj_step n inf outE G d0 st.1 st.2 hd0 hI b hb.1 hb.2.1 (by have := hb.2.2.1; have := hb.2.2.2.1; omega)
        (fun x hx hxD => by have := hb.2.2.1; have := hb.2.2.2.2 x hx hxD; omega)
      refine ⟨hI', Or.inl ?_⟩
      rcases hc with hc | hc
      · simp [hc]
      · exfalso
        have := hc b hb.1 hb.2.1
        have := hb.2.2.1; have := hb.2.2.2.1
        omega

theorem walk_lt (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 : Nat → Int)
    (hd0 : ∀ w, d0 w < inf → w < n) : ∀ w y c k, d0 w < inf → Walk (Eall n outE) w y c k → y < n := by
  intro w y c k h0 wk
  induction wk with
  | nil => exact hd0 w h0
  | @step c0 k0 e he wk ih =>
    obtain ⟨u, hu, heu⟩ := mem_Eall_inv n outE e he
    exact (G.out u hu e heu).2.1

theorem all_done (n : Nat) (D : List Nat) (hnd : D.Nodup) (hlt : ∀ x ∈ D, x < n) (hl : D.length = n) :
    ∀ x, x < n → x ∈ D := by
  intro x hx
  by_cases hm : x ∈ D
  · exact hm
  · exfalso
    have hnd' : (x :: D).Nodup := List.nodup_cons.mpr ⟨hm, hnd⟩
    have hsub : (x :: D) ⊆ List.range n := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_range.mpr hx
      · exact List.mem_range.mpr (hlt y hy)
    have := List.Nodup.length_le_of_subset hnd' hsub
    simp at this
    omega

/-- The result of Dijkstra's algorithm. -/
theorem dijkstra_spec (n : Nat) (inf : Int) (outE : Nat → List Edge) (G : Graph n outE) (d0 : Nat → Int)
    (hd0 : ∀ w, d0 w < inf → w < n) :
    Sound inf (Eall n outE) d0 (djIter inf outE n d0 n).1 ∧
    ((∀ w y c k, d0 w < inf → Walk (Eall n outE) w y c k → d0 w + c < inf) →
      ∀ w y c k, d0 w < inf → Walk (Eall n outE) w y c k → (djIter inf outE n d0 n).1 y ≤ d0 w + c) := by
  obtain ⟨hI, hc⟩ := djIter_inv n inf outE G d0 hd0 n
  refine ⟨hI.sound, fun hS w y c k h0 wk => ?_⟩
  have hyn := walk_lt n inf outE G d0 hd0 w y c k h0 wk
  have hL := walk_lemma n inf outE G d0 _ _ hd0 hI w y c k h0 wk
  by_cases hy : y ∈ (djIter inf outE n d0 n).2
  · exact hL.1 hy
  · exfalso
    obtain ⟨x, hx, hxD, hdx⟩ := hL.2 hy
    rcases hc with hc | hc
    · exact hxD (all_done n _ hI.nodup hI.lt hc x hx)
    · have := hc x hx hxD
      have := hS w y c k h0 wk
      omega

end Proofs.DijkstraMath
