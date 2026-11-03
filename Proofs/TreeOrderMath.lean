import Proofs.TreeDpMath

namespace Proofs.TreeOrderMath
open Proofs.TreeDpAlg Proofs.TreeDpSpec Proofs.TreeDpMath

/-- What `tree_order` needs from the tree and the parent array. -/
structure TO (head target : List Nat) (parent : List Int) (n root : Nat) : Prop where
  rootlt : root < n
  palen : parent.length = n
  rootpar : parent.getD root 0 = (root : Int)
  parv : ∀ w, w < n → 0 ≤ parent.getD w 0 ∧ parent.getD w 0 < n
  tgtlt : ∀ v, v < n → ∀ p ∈ arcs head v, tgt target p < n
  noself : ∀ v, v < n → ∀ p ∈ arcs head v, tgt target p ≠ v
  nodup : ∀ v, v < n → (nbs head target v).Nodup
  chArc : ∀ w, w < n → w ≠ root → ∃ p ∈ arcs head (par parent w), tgt target p = w
  depEx : ∃ dep : Nat → Nat, ∀ w, w < n → w ≠ root → dep (par parent w) < dep w

/-- The queue after the step `i`: the children of the `i`-th vertex are appended. -/
def qstep (head target : List Nat) (parent : List Int) (q : List Nat) (i : Nat) : List Nat :=
  if i < q.length then q ++ kidT head target parent (q.getD i 0) else q

def qrun (head target : List Nat) (parent : List Int) (q0 : List Nat) : Nat → List Nat
  | 0 => q0
  | i + 1 => qstep head target parent (qrun head target parent q0 i) i

structure QI (head target : List Nat) (parent : List Int) (n root i : Nat) (q : List Nat) : Prop where
  nd : q.Nodup
  lt : ∀ x ∈ q, x < n
  hd : q.getD 0 0 = root ∧ q ≠ []
  D : ∀ j, 1 ≤ j → j < q.length → ∃ j', j' < j ∧ j' < i ∧ q.getD j' 0 = par parent (q.getD j 0)

theorem getD_mem_of_lt (q : List Nat) (i : Nat) (h : i < q.length) : q.getD i 0 ∈ q := by
  have : q.getD i 0 = q[i]'h := by simp [List.getD_eq_getElem?_getD, h]
  rw [this]; exact List.getElem_mem _

theorem getD_app_left (l l' : List Nat) (j : Nat) (h : j < l.length) : (l ++ l').getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (l l' : List Nat) (j : Nat) (h : l.length ≤ j) :
    (l ++ l').getD j 0 = l'.getD (j - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_inj (q : List Nat) (hq : q.Nodup) (i j : Nat) (hi : i < q.length) (hj : j < q.length)
    (h : q.getD i 0 = q.getD j 0) : i = j := by
  have e1 : q.getD i 0 = q[i]'hi := by simp [List.getD_eq_getElem?_getD, hi]
  have e2 : q.getD j 0 = q[j]'hj := by simp [List.getD_eq_getElem?_getD, hj]
  rw [e1, e2] at h
  have a := List.Nodup.idxOf_getElem hq i hi
  have b := List.Nodup.idxOf_getElem hq j hj
  rw [h] at a
  omega

theorem kid_facts (H : TO head target parent n root) (v : Nat) (hv : v < n) (x : Nat) (hx : x ∈ kidT head target parent v) :
    x < n ∧ parent.getD x 0 = (v : Int) ∧ x ≠ v := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hpa, hdec⟩ := List.mem_filter.mp hp
  exact ⟨H.tgtlt v hv p hpa, by simpa using hdec, H.noself v hv p hpa⟩

theorem qi_init (H : TO head target parent n root) : QI head target parent n root 0 [root] :=
  ⟨by simp, by intro x hx; simp at hx; subst hx; exact H.rootlt, ⟨rfl, by simp⟩,
    fun j h1 h2 => absurd h2 (by simp; omega)⟩

theorem qi_step (H : TO head target parent n root) (i : Nat) (q : List Nat) (I : QI head target parent n root i q) :
    QI head target parent n root (i + 1) (qstep head target parent q i) := by
  unfold qstep
  by_cases h : i < q.length
  · rw [if_pos h]
    have hvq := getD_mem_of_lt q i h
    have hvn := I.lt _ hvq
    have hK := kid_facts H _ hvn
    have hKnd : (kidT head target parent (q.getD i 0)).Nodup := by
      have hsub : (kidT head target parent (q.getD i 0)).Sublist (nbs head target (q.getD i 0)) := by
        unfold kidT kidArcs nbs
        exact (List.filter_sublist).map _
      exact hsub.nodup (H.nodup _ hvn)
    have hdis : ∀ x ∈ q, ∀ y ∈ kidT head target parent (q.getD i 0), x ≠ y := by
      intro x hx y hy hxy
      subst hxy
      obtain ⟨_, hpar, hne⟩ := hK x hy
      have hxr : x ≠ root := by
        intro hr
        rw [hr, H.rootpar] at hpar
        apply hne
        rw [hr]
        exact_mod_cast hpar
      obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
      have hjd : q.getD j 0 = x := by simp [List.getD_eq_getElem?_getD, hj, hjx]
      have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun hz => hxr (by subst hz; rw [← hjd]; exact I.hd.1))
      obtain ⟨j', hj'j, hj'i, hj'e⟩ := I.D j hj1 hj
      rw [hjd] at hj'e
      have hparx : par parent x = q.getD i 0 := by
        unfold par; rw [hpar]; simp
      rw [hparx] at hj'e
      have := getD_inj q I.nd j' i (by omega) h hj'e
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact List.nodup_append.mpr ⟨I.nd, hKnd, hdis⟩
    · intro x hx
      rcases List.mem_append.mp hx with h1 | h1
      · exact I.lt x h1
      · exact (hK x h1).1
    · refine ⟨?_, List.append_ne_nil_of_left_ne_nil I.hd.2 _⟩
      rw [getD_app_left _ _ _ (List.length_pos_iff.mpr I.hd.2)]
      exact I.hd.1
    · intro j hj1 hj
      by_cases hjq : j < q.length
      · obtain ⟨j', a1, a2, a3⟩ := I.D j hj1 hjq
        refine ⟨j', a1, by omega, ?_⟩
        rw [getD_app_left _ _ _ hjq, getD_app_left _ _ _ (by omega)]
        exact a3
      · refine ⟨i, by omega, by omega, ?_⟩
        have hjk : j - q.length < (kidT head target parent (q.getD i 0)).length := by
          rw [List.length_append] at hj; omega
        have hel : (q ++ kidT head target parent (q.getD i 0)).getD j 0 =
            (kidT head target parent (q.getD i 0)).getD (j - q.length) 0 := by
          rw [getD_app_right _ _ _ (by omega)]
        rw [hel, getD_app_left _ _ _ h]
        have hmem := getD_mem_of_lt _ _ hjk
        have hpar := (hK _ hmem).2.1
        unfold par; rw [hpar]; simp
  · rw [if_neg h]
    refine ⟨I.nd, I.lt, I.hd, ?_⟩
    intro j hj1 hj
    obtain ⟨j', a1, a2, a3⟩ := I.D j hj1 hj
    exact ⟨j', a1, by omega, a3⟩

theorem qstep_prefix (head target : List Nat) (parent : List Int) (q : List Nat) (i : Nat) :
    q <+: qstep head target parent q i := by
  unfold qstep
  by_cases h : i < q.length
  · rw [if_pos h]; exact List.prefix_append _ _
  · rw [if_neg h]; exact List.prefix_refl _

theorem qrun_prefix (head target : List Nat) (parent : List Int) (q0 : List Nat) (m : Nat) :
    ∀ k, qrun head target parent q0 m <+: qrun head target parent q0 (m + k) := by
  intro k
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (qstep_prefix head target parent _ _)

theorem qrun_stable (head target : List Nat) (parent : List Int) (q0 : List Nat) (j : Nat)
    (h : (qrun head target parent q0 j).length ≤ j) : ∀ k, qrun head target parent q0 (j + k) = qrun head target parent q0 j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show qstep head target parent (qrun head target parent q0 (j + k)) (j + k) = _
    rw [ih]
    unfold qstep
    rw [if_neg (by omega)]

theorem qrun_inv (H : TO head target parent n root) : ∀ i, QI head target parent n root i (qrun head target parent [root] i) := by
  intro i
  induction i with
  | zero => exact qi_init H
  | succ i ih => exact qi_step H i _ ih

theorem nodup_len_le : ∀ (q r : List Nat), q.Nodup → q ⊆ r → q.length ≤ r.length := by
  intro q
  induction q with
  | nil => intro r _ _; simp
  | cons a q ih =>
    intro r hnd hsub
    rw [List.nodup_cons] at hnd
    have har : a ∈ r := hsub (List.mem_cons_self ..)
    have h1 : q ⊆ r.erase a := by
      intro x hx
      have hxr : x ∈ r := hsub (List.mem_cons_of_mem _ hx)
      have hxa : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr hxr
    have := ih (r.erase a) hnd.2 h1
    rw [List.length_erase_of_mem har] at this
    have hpos : 0 < r.length := List.length_pos_of_mem har
    simp; omega

theorem len_le_n (q : List Nat) (hnd : q.Nodup) (hlt : ∀ x ∈ q, x < n) : q.length ≤ n := by
  have hsub : q ⊆ List.range n := fun x hx => List.mem_range.mpr (hlt x hx)
  have := nodup_len_le q _ hnd hsub
  simpa using this

theorem qrun_complete (H : TO head target parent n root) :
    ∀ w, w < n → w ∈ qrun head target parent [root] n := by
  obtain ⟨dep, hdep⟩ := H.depEx
  have hI := qrun_inv H n
  have key : ∀ m w, dep w = m → w < n → w ∈ qrun head target parent [root] n := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro w hdw hw
      by_cases hwr : w = root
      · subst hwr
        have hpos : 0 < (qrun head target parent [w] n).length := List.length_pos_iff.mpr hI.hd.2
        have := getD_mem_of_lt _ 0 hpos
        rwa [hI.hd.1] at this
      · have hpv := H.parv w hw
        have hu : par parent w < n := by unfold par; omega
        have hlt := hdep w hw hwr
        have hum := ih (dep (par parent w)) (by omega) (par parent w) rfl hu
        obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hum
        have hjn : j < n := Nat.lt_of_lt_of_le hj (len_le_n _ hI.nd hI.lt)
        have hjd : (qrun head target parent [root] n).getD j 0 = par parent w := by
          simp [List.getD_eq_getElem?_getD, hj, hjx]
        have hjq : j < (qrun head target parent [root] j).length := by
          rcases Nat.lt_or_ge j (qrun head target parent [root] j).length with hc | hc
          · exact hc
          · exfalso
            have hst := qrun_stable head target parent [root] j hc (n - j)
            rw [show j + (n - j) = n by omega] at hst
            rw [hst] at hj
            omega
        obtain ⟨t, ht⟩ := qrun_prefix head target parent [root] j (n - j)
        rw [show j + (n - j) = n by omega] at ht
        have hu0 : (qrun head target parent [root] j).getD j 0 = par parent w := by
          rw [← hjd, ← ht, getD_app_left _ _ _ hjq]
        obtain ⟨t2, ht2⟩ := qrun_prefix head target parent [root] (j + 1) (n - (j + 1))
        rw [show j + 1 + (n - (j + 1)) = n by omega] at ht2
        have hstep : qrun head target parent [root] (j + 1) =
            qrun head target parent [root] j ++ kidT head target parent (par parent w) := by
          show qstep head target parent (qrun head target parent [root] j) j = _
          unfold qstep
          rw [if_pos hjq, hu0]
        obtain ⟨p, hp, hpt⟩ := H.chArc w hw hwr
        have hwk : w ∈ kidT head target parent (par parent w) := by
          refine List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, hpt⟩
          have : tgt target p = w := hpt
          rw [this]
          have : parent.getD w 0 = ((par parent w : Nat) : Int) := by
            unfold par; omega
          simpa using this
        rw [← ht2, hstep]
        simp [List.mem_append, hwk]
  exact fun w hw => key _ w rfl hw

/-- The final queue is a permutation of the vertices in which the parent comes before the child. -/
theorem order_spec (H : TO head target parent n root) :
    (qrun head target parent [root] n).length = n ∧ (qrun head target parent [root] n).Nodup ∧
    (∀ x ∈ qrun head target parent [root] n, x < n) ∧ (qrun head target parent [root] n).getD 0 0 = root ∧
    ∀ j, 1 ≤ j → j < n → ∃ j', j' < j ∧ (qrun head target parent [root] n).getD j' 0 =
      par parent ((qrun head target parent [root] n).getD j 0) := by
  have hI := qrun_inv H n
  have hle := len_le_n _ hI.nd hI.lt
  have hge : n ≤ (qrun head target parent [root] n).length := by
    have hsub : List.range n ⊆ qrun head target parent [root] n := fun x hx =>
      qrun_complete H x (List.mem_range.mp hx)
    have := nodup_len_le _ _ (List.nodup_range) hsub
    simpa using this
  have hlen : (qrun head target parent [root] n).length = n := by omega
  refine ⟨hlen, hI.nd, hI.lt, hI.hd.1, ?_⟩
  intro j hj1 hjn
  obtain ⟨j', a1, _, a3⟩ := hI.D j hj1 (by omega)
  exact ⟨j', a1, a3⟩

end Proofs.TreeOrderMath
