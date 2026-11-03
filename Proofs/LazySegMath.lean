import Proofs.SegTreeMath

namespace Proofs.LazySegMath
open Proofs.SegTreeMath

/-- A monoid `M` with an action `F`: `mp f x` is the value `x` after the action `f`, `comp f g` is "`g` first, then `f`". -/
structure LMon extends Mon where
  Fv : Int → Prop
  fid : Int
  comp : Int → Int → Int
  mp : Int → Int → Int
  fid_v : Fv fid
  comp_v : ∀ f g, Fv f → Fv g → Fv (comp f g)
  mp_v : ∀ f x, Fv f → V x → V (mp f x)
  mp_op : ∀ f a b, Fv f → V a → V b → mp f (op a b) = op (mp f a) (mp f b)
  mp_comp : ∀ f g x, Fv f → Fv g → V x → mp (comp f g) x = mp f (mp g x)
  mp_id : ∀ x, V x → mp fid x = x
  comp_assoc : ∀ f g h, Fv f → Fv g → Fv h → comp (comp f g) h = comp f (comp g h)
  comp_idl : ∀ g, Fv g → comp fid g = g
  comp_idr : ∀ f, Fv f → comp f fid = f

variable (L : LMon)

/-- All pending actions are valid. -/
def AllF (lz : List Int) : Prop := ∀ x ∈ lz, L.Fv x

theorem getD_F (lz : List Int) (h : AllF L lz) (a : Nat) : L.Fv (lz.getD a L.fid) := by
  by_cases ha : a < lz.length
  · have : lz.getD a L.fid = lz[a] := by simp [List.getD_eq_getElem?_getD, ha]
    rw [this]; exact h _ (List.getElem_mem _)
  · have : lz.getD a L.fid = L.fid := by simp [List.getD_eq_getElem?_getD, ha]
    rw [this]; exact L.fid_v

theorem allF_set (lz : List Int) (h : AllF L lz) (i : Nat) (x : Int) (hx : L.Fv x) : AllF L (lz.set i x) := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h' | h'
  · exact h y h'
  · rw [h']; exact hx

/-- The action accumulated from the strict ancestors of the node `k` (the nearest ancestor acts first). -/
def G (lz : List Int) (k : Nat) : Int :=
  if h : k ≤ 1 then L.fid else L.comp (G lz (k / 2)) (lz.getD (k / 2) L.fid)
termination_by k
decreasing_by omega

theorem G_le (lz : List Int) (k : Nat) (h : k ≤ 1) : G L lz k = L.fid := by
  rw [G, dif_pos h]

theorem G_ge (lz : List Int) (k : Nat) (h : 2 ≤ k) : G L lz k = L.comp (G L lz (k / 2)) (lz.getD (k / 2) L.fid) := by
  rw [G, dif_neg (by omega)]

theorem G_v (lz : List Int) (h : AllF L lz) : ∀ k, L.Fv (G L lz k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k ≤ 1
    · rw [G_le L lz k hk]; exact L.fid_v
    · rw [G_ge L lz k (by omega)]
      exact L.comp_v _ _ (ih (k / 2) (by omega)) (getD_F L lz h _)

/-- All strict ancestors of `k` have no pending action. -/
def Cl (lz : List Int) (k : Nat) : Prop := ∀ t, 1 ≤ t → 1 ≤ k / 2 ^ t → lz.getD (k / 2 ^ t) L.fid = L.fid

theorem Cl_half (lz : List Int) (k : Nat) (h : Cl L lz k) : Cl L lz (k / 2) := by
  intro t ht h1
  have e : k / 2 / 2 ^ t = k / 2 ^ (t + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
  rw [e] at h1 ⊢
  exact h (t + 1) (by omega) h1

theorem G_clean (lz : List Int) (h : AllF L lz) : ∀ k, Cl L lz k → G L lz k = L.fid := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hc
    by_cases hk : k ≤ 1
    · exact G_le L lz k hk
    · rw [G_ge L lz k (by omega), ih (k / 2) (by omega) (Cl_half L lz k hc)]
      have h1 : lz.getD (k / 2) L.fid = L.fid := by
        have := hc 1 (by omega) (by simp; omega)
        simpa using this
      rw [h1]
      exact L.comp_idl _ L.fid_v

/-! ### Ancestors -/

theorem anc_refl (x : Nat) : Anc x x := ⟨0, by simp⟩

theorem anc_child (x d : Nat) (h : Anc x (2 * d) ∨ Anc x (2 * d + 1)) : Anc x d := by
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine ⟨t + 1, ?_⟩
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← ht]; omega
  · refine ⟨t + 1, ?_⟩
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← ht]; omega

theorem anc_trans (x a b : Nat) (h1 : Anc x a) (h2 : Anc a b) : Anc x b := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨s + t, ?_⟩
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, ← hs, ← ht]

theorem anc_cmp (x a b : Nat) (h1 : Anc x a) (h2 : Anc x b) : Anc a b ∨ Anc b a := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  rcases Nat.le_total s t with hst | hst
  · left
    refine ⟨t - s, ?_⟩
    rw [hs, ht, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2; omega
  · right
    refine ⟨s - t, ?_⟩
    rw [hs, ht, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2; omega

theorem anc_antisymm (a b : Nat) (h1 : Anc a b) (h2 : Anc b a) : a = b := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have e1 : b ≤ a := by rw [hs]; exact Nat.div_le_self _ _
  have e2 : a ≤ b := by rw [ht]; exact Nat.div_le_self _ _
  omega

theorem anc_succ_half (d k : Nat) (h : Anc d k) (hne : d ≠ k) : Anc (d / 2) k := by
  rcases (anc_step d k).mp h with e | e
  · exact absurd e.symm hne
  · exact e

/-! ### The ideal tree of a leaf function -/

/-- The value of the node `k` of a tree with `N` leaves when the leaf `x` (`N <= x < 2N`) has the value `lf x`. -/
def tr (lf : Nat → Int) (N k : Nat) : Int :=
  if h : 1 ≤ k ∧ k < N then L.op (tr lf N (2 * k)) (tr lf N (2 * k + 1)) else lf k
termination_by 2 * N - k
decreasing_by all_goals omega

theorem tr_leaf (lf : Nat → Int) (N k : Nat) (h : ¬ (1 ≤ k ∧ k < N)) : tr L lf N k = lf k := by
  rw [tr, dif_neg h]

theorem tr_node (lf : Nat → Int) (N k : Nat) (h1 : 1 ≤ k) (h2 : k < N) :
    tr L lf N k = L.op (tr L lf N (2 * k)) (tr L lf N (2 * k + 1)) := by
  rw [tr, dif_pos ⟨h1, h2⟩]

/-- The leaf values are representable. -/
def LeafV (lf : Nat → Int) (N : Nat) : Prop := ∀ x, N ≤ x → x < 2 * N → L.V (lf x)

theorem tr_v (lf : Nat → Int) (N : Nat) (hl : LeafV L lf N) : ∀ d, 1 ≤ d → d < 2 * N → L.V (tr L lf N d) := by
  have key : ∀ m d, 2 * N - d = m → 1 ≤ d → d < 2 * N → L.V (tr L lf N d) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro d hm h1 h2
      by_cases hd : d < N
      · rw [tr_node L lf N d h1 hd]
        exact L.closed _ _ (ih (2 * N - 2 * d) (by omega) (2 * d) rfl (by omega) (by omega))
          (ih (2 * N - (2 * d + 1)) (by omega) (2 * d + 1) rfl (by omega) (by omega))
      · rw [tr_leaf L lf N d (by omega)]
        exact hl d (by omega) h2
  intro d h1 h2
  exact key _ d rfl h1 h2

theorem tr_congr (lf lf' : Nat → Int) (N : Nat) :
    ∀ d, 1 ≤ d → d < 2 * N → (∀ x, N ≤ x → x < 2 * N → Anc x d → lf' x = lf x) → tr L lf' N d = tr L lf N d := by
  have key : ∀ m d, 2 * N - d = m → 1 ≤ d → d < 2 * N → (∀ x, N ≤ x → x < 2 * N → Anc x d → lf' x = lf x) →
      tr L lf' N d = tr L lf N d := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro d hm h1 h2 hx
      by_cases hd : d < N
      · rw [tr_node L lf N d h1 hd, tr_node L lf' N d h1 hd]
        rw [ih (2 * N - 2 * d) (by omega) (2 * d) rfl (by omega) (by omega)
              (fun x a b c => hx x a b (anc_child x d (Or.inl c))),
            ih (2 * N - (2 * d + 1)) (by omega) (2 * d + 1) rfl (by omega) (by omega)
              (fun x a b c => hx x a b (anc_child x d (Or.inr c)))]
      · rw [tr_leaf L lf N d (by omega), tr_leaf L lf' N d (by omega)]
        exact hx d (by omega) h2 (anc_refl d)
  intro d h1 h2 hx
  exact key _ d rfl h1 h2 hx

theorem tr_mapped (lf lf' : Nat → Int) (N : Nat) (f : Int) (hf : L.Fv f) (hl : LeafV L lf N) :
    ∀ d, 1 ≤ d → d < 2 * N → (∀ x, N ≤ x → x < 2 * N → Anc x d → lf' x = L.mp f (lf x)) →
      tr L lf' N d = L.mp f (tr L lf N d) := by
  have key : ∀ m d, 2 * N - d = m → 1 ≤ d → d < 2 * N → (∀ x, N ≤ x → x < 2 * N → Anc x d → lf' x = L.mp f (lf x)) →
      tr L lf' N d = L.mp f (tr L lf N d) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro d hm h1 h2 hx
      by_cases hd : d < N
      · rw [tr_node L lf N d h1 hd, tr_node L lf' N d h1 hd]
        rw [ih (2 * N - 2 * d) (by omega) (2 * d) rfl (by omega) (by omega)
              (fun x a b c => hx x a b (anc_child x d (Or.inl c))),
            ih (2 * N - (2 * d + 1)) (by omega) (2 * d + 1) rfl (by omega) (by omega)
              (fun x a b c => hx x a b (anc_child x d (Or.inr c)))]
        rw [L.mp_op f _ _ hf (tr_v L lf N hl _ (by omega) (by omega)) (tr_v L lf N hl _ (by omega) (by omega))]
      · rw [tr_leaf L lf N d (by omega), tr_leaf L lf' N d (by omega)]
        exact hx d (by omega) h2 (anc_refl d)
  intro d h1 h2 hx
  exact key _ d rfl h1 h2 hx

/-! ### `push` -/

/-- `Ext`: every node outside `B` holds, after its ancestors' pending actions, the value of the ideal tree. -/
def Ext (lf : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop) : Prop :=
  ∀ d, 1 ≤ d → d < 2 * N → ¬ B d → L.mp (G L lz d) (node.getD d L.e) = tr L lf N d

/-- `push(k)`: the nodes. -/
def pushNode (node lz : List Int) (k : Nat) : List Int :=
  (node.set (2 * k) (L.mp (lz.getD k L.fid) (node.getD (2 * k) L.e))).set (2 * k + 1)
    (L.mp (lz.getD k L.fid) (node.getD (2 * k + 1) L.e))

/-- `all_apply(c, f)` on the pending actions: only the inner nodes (`c < N`) keep a pending action. -/
def alz (N : Nat) (lz : List Int) (c : Nat) (f : Int) : List Int :=
  if c < N then lz.set c (L.comp f (lz.getD c L.fid)) else lz

/-- `push(k)`: the pending actions. -/
def pushLz (N : Nat) (lz : List Int) (k : Nat) : List Int :=
  (alz L N (alz L N lz (2 * k) (lz.getD k L.fid)) (2 * k + 1) (lz.getD k L.fid)).set k L.fid

theorem getD_set_default (v : List Int) (i : Nat) (x : Int) (j : Nat) (dflt : Int) :
    (v.set i x).getD j dflt = if j = i ∧ i < v.length then x else v.getD j dflt := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

theorem alz_len (N : Nat) (lz : List Int) (c : Nat) (f : Int) : (alz L N lz c f).length = lz.length := by
  unfold alz; split <;> simp

theorem getD_alz (N : Nat) (lz : List Int) (hlen : lz.length = N) (c : Nat) (f : Int) (p : Nat) :
    (alz L N lz c f).getD p L.fid = if p = c ∧ c < N then L.comp f (lz.getD p L.fid) else lz.getD p L.fid := by
  unfold alz
  by_cases hc : c < N
  · rw [if_pos hc, getD_set_default]
    by_cases hp : p = c
    · subst hp
      rw [if_pos ⟨rfl, by omega⟩, if_pos ⟨rfl, hc⟩]
    · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
  · rw [if_neg hc, if_neg (fun h => hc h.2)]

theorem pushLz_len (N : Nat) (lz : List Int) (k : Nat) : (pushLz L N lz k).length = lz.length := by
  unfold pushLz
  simp [alz_len]

theorem pushLz_get (N : Nat) (lz : List Int) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < N) (hlen : lz.length = N) (p : Nat) :
    (pushLz L N lz k).getD p L.fid =
      if p = k then L.fid
      else if p = 2 * k ∧ 2 * k < N then L.comp (lz.getD k L.fid) (lz.getD p L.fid)
      else if p = 2 * k + 1 ∧ 2 * k + 1 < N then L.comp (lz.getD k L.fid) (lz.getD p L.fid)
      else lz.getD p L.fid := by
  unfold pushLz
  have hl1 : (alz L N lz (2 * k) (lz.getD k L.fid)).length = N := by rw [alz_len, hlen]
  rw [getD_set_default, alz_len, alz_len, hlen]
  rw [getD_alz L N _ hl1, getD_alz L N lz hlen]
  have hkN : k < N := hk2
  by_cases h0 : p = k
  · subst h0
    rw [if_pos ⟨rfl, hkN⟩, if_pos rfl]
  · rw [if_neg (fun h => h0 h.1), if_neg h0]
    by_cases h1 : p = 2 * k + 1 ∧ 2 * k + 1 < N
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      rw [if_pos ⟨rfl, h1b⟩, if_neg (show ¬ (2 * k + 1 = 2 * k ∧ 2 * k < N) by omega), if_neg (show ¬ (2 * k + 1 = 2 * k ∧ 2 * k < N) by omega),
        if_pos ⟨rfl, h1b⟩]
    · by_cases h2 : p = 2 * k ∧ 2 * k < N
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        rw [if_neg h1, if_pos ⟨rfl, h2b⟩, if_neg h1, if_pos ⟨rfl, h2b⟩]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem G_push (N : Nat) (lz : List Int) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < N) (hlen : lz.length = N) (hF : AllF L lz) :
    ∀ d, d < 2 * N →
      ((d = 2 * k ∨ d = 2 * k + 1) → G L (pushLz L N lz k) d = G L lz k) ∧
      ((d ≠ 2 * k ∧ d ≠ 2 * k + 1) → G L (pushLz L N lz k) d = G L lz d) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases hd1 : d ≤ 1
    · refine ⟨fun h => by omega, fun _ => ?_⟩
      rw [G_le L _ d hd1, G_le L _ d hd1]
    · have hp1 : 1 ≤ d / 2 := by omega
      have hpN : d / 2 < N := by omega
      have hpd : d / 2 < d := by omega
      have get := pushLz_get L N lz k hk1 hk2 hlen (d / 2)
      rw [G_ge L _ d (by omega)]
      have hf := getD_F L lz hF k
      by_cases hpk : d / 2 = k
      · -- d is a child of k
        have h2 : d = 2 * k ∨ d = 2 * k + 1 := by omega
        refine ⟨fun _ => ?_, fun h => by omega⟩
        rw [get, if_pos hpk]
        have ih' := (ih (d / 2) hpd (by omega)).2 (by omega)
        rw [ih', hpk]
        exact L.comp_idr _ (G_v L lz hF k)
      · by_cases hp2 : d / 2 = 2 * k ∨ d / 2 = 2 * k + 1
        · -- grandchild
          have hn : d ≠ 2 * k ∧ d ≠ 2 * k + 1 := by omega
          refine ⟨fun h => by omega, fun _ => ?_⟩
          have ih' := (ih (d / 2) hpd (by omega)).1 hp2
          rw [ih']
          rw [G_ge L lz d (by omega)]
          have hGp : G L lz (d / 2) = L.comp (G L lz k) (lz.getD k L.fid) := by
            rw [G_ge L lz (d / 2) (by omega)]
            have : d / 2 / 2 = k := by omega
            rw [this]
          rw [hGp]
          have hcond : ((d / 2 = 2 * k ∧ 2 * k < N) ∨ (d / 2 = 2 * k + 1 ∧ 2 * k + 1 < N)) := by
            rcases hp2 with h | h
            · exact Or.inl ⟨h, by omega⟩
            · exact Or.inr ⟨h, by omega⟩
          have hget : (pushLz L N lz k).getD (d / 2) L.fid = L.comp (lz.getD k L.fid) (lz.getD (d / 2) L.fid) := by
            rw [get, if_neg hpk]
            rcases hp2 with h | h
            · rw [if_pos ⟨h, by omega⟩]
            · rw [if_neg (by omega), if_pos ⟨h, by omega⟩]
          rw [hget, L.comp_assoc _ _ _ (G_v L lz hF k) hf (getD_F L lz hF _)]
        · have hn : d ≠ 2 * k ∧ d ≠ 2 * k + 1 := by omega
          refine ⟨fun h => by omega, fun _ => ?_⟩
          have ih' := (ih (d / 2) hpd (by omega)).2 (by omega)
          rw [ih', G_ge L lz d (by omega)]
          have hget : (pushLz L N lz k).getD (d / 2) L.fid = lz.getD (d / 2) L.fid := by
            rw [get, if_neg hpk, if_neg (by omega), if_neg (by omega)]
          rw [hget]

theorem getD_Ve (v : List Int) (h : AllV L.toMon v) (a : Nat) (ha : a < v.length) : L.V (v.getD a L.e) := by
  have : v.getD a L.e = v[a] := by simp [List.getD_eq_getElem?_getD, ha]
  rw [this]; exact h _ (List.getElem_mem _)

theorem getD_pushNode (node lz : List Int) (k : Nat) (hnode : node.length = 2 * N) (hk2 : k < N) (d : Nat) :
    (pushNode L node lz k).getD d L.e =
      if d = 2 * k then L.mp (lz.getD k L.fid) (node.getD d L.e)
      else if d = 2 * k + 1 then L.mp (lz.getD k L.fid) (node.getD d L.e)
      else node.getD d L.e := by
  unfold pushNode
  rw [getD_set_default, getD_set_default]
  simp only [List.length_set, hnode]
  by_cases h1 : d = 2 * k + 1
  · subst h1
    rw [if_pos ⟨rfl, by omega⟩, if_neg (by omega)]
    simp
  · rw [if_neg (fun h => h1 h.1)]
    by_cases h2 : d = 2 * k
    · subst h2
      rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.1), if_neg h2, if_neg h1]

theorem pushNode_len (node lz : List Int) (k : Nat) : (pushNode L node lz k).length = node.length := by
  unfold pushNode; simp

theorem ext_push (lf : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < N)
    (hlen : lz.length = N) (hnode : node.length = 2 * N) (hV : AllV L.toMon node) (hF : AllF L lz)
    (h : Ext L lf N node lz B) : Ext L lf N (pushNode L node lz k) (pushLz L N lz k) B := by
  intro d hd1 hd2 hB
  have hgp := G_push L N lz k hk1 hk2 hlen hF d hd2
  rw [getD_pushNode L node lz k hnode hk2]
  have hf := getD_F L lz hF k
  by_cases h2 : d = 2 * k
  · have hG := hgp.1 (Or.inl h2)
    rw [hG, if_pos h2]
    subst h2
    have := h (2 * k) hd1 hd2 hB
    rw [G_ge L lz (2 * k) (by omega)] at this
    have e2 : 2 * k / 2 = k := by omega
    rw [e2] at this
    rw [← this, L.mp_comp _ _ _ (G_v L lz hF k) hf (getD_Ve L node hV _ (by omega))]
  · by_cases h3 : d = 2 * k + 1
    · have hG := hgp.1 (Or.inr h3)
      rw [hG, if_neg h2, if_pos h3]
      subst h3
      have := h (2 * k + 1) hd1 hd2 hB
      rw [G_ge L lz (2 * k + 1) (by omega)] at this
      have e2 : (2 * k + 1) / 2 = k := by omega
      rw [e2] at this
      rw [← this, L.mp_comp _ _ _ (G_v L lz hF k) hf (getD_Ve L node hV _ (by omega))]
    · rw [hgp.2 ⟨h2, h3⟩, if_neg h2, if_neg h3]
      exact h d hd1 hd2 hB

/-! ### `all_apply`, `update` and the write of a leaf -/

/-- `node[k] = mapping(f, node[k])`. -/
def applyNode (node : List Int) (k : Nat) (f : Int) : List Int := node.set k (L.mp f (node.getD k L.e))

/-- `node[i] = op(node[2i], node[2i+1])`. -/
def updNode (node : List Int) (i : Nat) : List Int := node.set i (L.op (node.getD (2 * i) L.e) (node.getD (2 * i + 1) L.e))

theorem G_apply (N : Nat) (lz : List Int) (k : Nat) (f : Int) (hk1 : 1 ≤ k) (hlen : lz.length = N) (hF : AllF L lz)
    (hf : L.Fv f) (hGk : G L lz k = L.fid) :
    ∀ d, d < 2 * N →
      (d = k → G L (alz L N lz k f) d = G L lz d) ∧
      (Anc d k ∧ d ≠ k → G L (alz L N lz k f) d = L.comp f (G L lz d)) ∧
      (¬ Anc d k → G L (alz L N lz k f) d = G L lz d) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases hd1 : d ≤ 1
    · refine ⟨fun _ => ?_, fun h => ?_, fun _ => ?_⟩
      · rw [G_le L _ d hd1, G_le L _ d hd1]
      · exfalso
        obtain ⟨⟨t, ht⟩, hne⟩ := h
        have : d / 2 ^ t ≤ d := Nat.div_le_self _ _
        omega
      · rw [G_le L _ d hd1, G_le L _ d hd1]
    · have hpd : d / 2 < d := by omega
      have hpN : d / 2 < N := by omega
      have hp1 : 1 ≤ d / 2 := by omega
      rw [G_ge L _ d (by omega), G_ge L lz d (by omega)]
      have hget := getD_alz L N lz hlen k f (d / 2)
      have hFp := getD_F L lz hF (d / 2)
      by_cases hpk : d / 2 = k
      · have hkN : k < N := by omega
        have hAnc : Anc d k := (anc_step d k).mpr (Or.inr (by rw [hpk]; exact anc_refl k))
        have hdk : d ≠ k := by omega
        refine ⟨fun h => absurd h hdk, fun _ => ?_, fun h => absurd hAnc h⟩
        rw [hget, if_pos ⟨hpk, hkN⟩]
        have ihk := (ih (d / 2) hpd (by omega)).1 hpk
        rw [ihk]
        have e1 : G L lz (d / 2) = L.fid := by rw [hpk]; exact hGk
        rw [e1]
        have hlk : L.Fv (lz.getD (d / 2) L.fid) := hFp
        rw [L.comp_idl _ (L.comp_v _ _ hf hFp), L.comp_idl _ hFp]
      · have hget' : (alz L N lz k f).getD (d / 2) L.fid = lz.getD (d / 2) L.fid := by
          rw [hget, if_neg (fun h => hpk h.1)]
        rw [hget']
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
        · -- d = k
          have hnA : ¬ Anc (d / 2) k := by
            rintro ⟨t, ht⟩
            have : (d / 2) / 2 ^ t ≤ d / 2 := Nat.div_le_self _ _
            omega
          rw [(ih (d / 2) hpd (by omega)).2.2 hnA]
        · obtain ⟨hA, hne⟩ := h
          have hA' : Anc (d / 2) k := anc_succ_half d k hA hne
          rw [(ih (d / 2) hpd (by omega)).2.1 ⟨hA', hpk⟩]
          rw [L.comp_assoc _ _ _ hf (G_v L lz hF _) hFp]
        · have hnA : ¬ Anc (d / 2) k := by
            intro hA
            exact h (anc_trans d (d / 2) k ((anc_step d (d / 2)).mpr (Or.inr (anc_refl _)) |> fun _ => ⟨1, by simp⟩) hA)
          rw [(ih (d / 2) hpd (by omega)).2.2 hnA]

theorem ext_apply (lf lf' : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop) (k : Nat) (f : Int)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * N) (hlen : lz.length = N) (hnode : node.length = 2 * N) (hV : AllV L.toMon node)
    (hF : AllF L lz) (hf : L.Fv f) (hlfV : LeafV L lf N) (hGk : G L lz k = L.fid) (hB : ∀ d, Anc d k → ¬ B d)
    (hl1 : ∀ x, Anc x k → lf' x = L.mp f (lf x)) (hl2 : ∀ x, ¬ Anc x k → lf' x = lf x)
    (h : Ext L lf N node lz B) :
    Ext L lf' N (applyNode L node k f) (alz L N lz k f) (fun d => B d ∨ (Anc k d ∧ d ≠ k)) := by
  intro d hd1 hd2 hB'
  have hga := G_apply L N lz k f hk1 hlen hF hf hGk d hd2
  have hnB : ¬ B d := fun hb => hB' (Or.inl hb)
  have hgetN : (applyNode L node k f).getD d L.e = if d = k then L.mp f (node.getD d L.e) else node.getD d L.e := by
    unfold applyNode
    rw [getD_set_default]
    by_cases hdk : d = k
    · subst hdk; rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (fun h => hdk h.1), if_neg hdk]
  rw [hgetN]
  have hVd := getD_Ve L node hV d (by omega)
  by_cases hdk : d = k
  · subst hdk
    rw [if_pos rfl, hga.1 rfl, hGk]
    have hExt := h d hd1 hd2 (hB d (anc_refl d))
    rw [hGk, L.mp_id _ hVd] at hExt
    have := tr_mapped L lf lf' N f hf hlfV d hd1 hd2 (fun x _ _ hx => hl1 x hx)
    rw [this, ← hExt, L.mp_id _ (L.mp_v _ _ hf hVd)]
  · rw [if_neg hdk]
    by_cases hA : Anc d k
    · rw [hga.2.1 ⟨hA, hdk⟩]
      have hExt := h d hd1 hd2 (hB d hA)
      have := tr_mapped L lf lf' N f hf hlfV d hd1 hd2 (fun x _ _ hx => hl1 x (anc_trans x d k hx hA))
      rw [this, ← hExt, L.mp_comp _ _ _ hf (G_v L lz hF d) hVd]
    · rw [hga.2.2 hA]
      have hnA2 : ¬ Anc k d := fun hk => hB' (Or.inr ⟨hk, hdk⟩)
      have := tr_congr L lf lf' N d hd1 hd2 (fun x _ _ hx => by
        apply hl2
        intro hxk
        rcases anc_cmp x d k hx hxk with h1 | h1
        · exact hA h1
        · exact hnA2 h1)
      rw [this]
      exact h d hd1 hd2 hnB

theorem ext_update (lf : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop) (i : Nat) (hi1 : 1 ≤ i) (hiN : i < N)
    (hlen : lz.length = N) (hnode : node.length = 2 * N) (hV : AllV L.toMon node) (hF : AllF L lz)
    (hlzi : lz.getD i L.fid = L.fid) (hB1 : ¬ B (2 * i)) (hB2 : ¬ B (2 * i + 1))
    (h : Ext L lf N node lz B) : Ext L lf N (updNode L node i) lz (fun d => B d ∧ d ≠ i) := by
  intro d hd1 hd2 hB'
  have hgetN : (updNode L node i).getD d L.e = if d = i then L.op (node.getD (2 * i) L.e) (node.getD (2 * i + 1) L.e)
      else node.getD d L.e := by
    unfold updNode
    rw [getD_set_default]
    by_cases hdi : d = i
    · subst hdi; rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (fun h => hdi h.1), if_neg hdi]
  rw [hgetN]
  by_cases hdi : d = i
  · subst hdi
    rw [if_pos rfl]
    have hl := h (2 * d) (by omega) (by omega) hB1
    have hr := h (2 * d + 1) (by omega) (by omega) hB2
    have e1 : G L lz (2 * d) = G L lz d := by
      rw [G_ge L lz (2 * d) (by omega)]
      have : 2 * d / 2 = d := by omega
      rw [this, hlzi]
      exact L.comp_idr _ (G_v L lz hF d)
    have e2 : G L lz (2 * d + 1) = G L lz d := by
      rw [G_ge L lz (2 * d + 1) (by omega)]
      have : (2 * d + 1) / 2 = d := by omega
      rw [this, hlzi]
      exact L.comp_idr _ (G_v L lz hF d)
    rw [e1] at hl
    rw [e2] at hr
    rw [L.mp_op _ _ _ (G_v L lz hF d) (getD_Ve L node hV _ (by omega)) (getD_Ve L node hV _ (by omega)), hl, hr,
      tr_node L lf N d hd1 hiN]
  · rw [if_neg hdi]
    exact h d hd1 hd2 (fun hb => hB' ⟨hb, hdi⟩)

theorem ext_setleaf (lf : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop) (p : Nat) (val : Int)
    (hp1 : N ≤ p) (hp2 : p < 2 * N) (hlen : lz.length = N) (hnode : node.length = 2 * N) (hF : AllF L lz)
    (hGp : G L lz p = L.fid) (hval : L.V val) (h : Ext L lf N node lz B) :
    Ext L (fun x => if x = p then val else lf x) N (node.set p val) lz (fun d => B d ∨ (Anc p d ∧ d ≠ p)) := by
  intro d hd1 hd2 hB'
  have hgetN : (node.set p val).getD d L.e = if d = p then val else node.getD d L.e := by
    rw [getD_set_default]
    by_cases hdp : d = p
    · subst hdp; rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (fun h => hdp h.1), if_neg hdp]
  rw [hgetN]
  by_cases hdp : d = p
  · subst hdp
    rw [if_pos rfl, hGp, L.mp_id _ hval, tr_leaf L _ N d (by omega)]
    simp
  · rw [if_neg hdp]
    have hnA : ¬ Anc p d := fun hk => hB' (Or.inr ⟨hk, hdp⟩)
    have := tr_congr L lf (fun x => if x = p then val else lf x) N d hd1 hd2 (fun x _ _ hx => by
      have hxp : x ≠ p := by
        intro e; subst e; exact hnA hx
      simp [hxp])
    rw [this]
    exact h d hd1 hd2 (fun hb => hB' (Or.inl hb))

/-! ### Bookkeeping for the push phases -/

theorem allF_alz (N : Nat) (lz : List Int) (hF : AllF L lz) (c : Nat) (f : Int) (hf : L.Fv f) : AllF L (alz L N lz c f) := by
  unfold alz
  split
  · exact allF_set L lz hF c _ (L.comp_v _ _ hf (getD_F L lz hF c))
  · exact hF

theorem allF_pushLz (N : Nat) (lz : List Int) (hF : AllF L lz) (k : Nat) : AllF L (pushLz L N lz k) := by
  unfold pushLz
  exact allF_set L _ (allF_alz L N _ (allF_alz L N lz hF _ _ (getD_F L lz hF k)) _ _ (getD_F L lz hF k)) k _ L.fid_v

theorem allV_applyNode (node : List Int) (hV : AllV L.toMon node) (k : Nat) (f : Int) (hf : L.Fv f) (hk : k < node.length) :
    AllV L.toMon (applyNode L node k f) := by
  unfold applyNode
  exact allV_set L.toMon node hV k _ (L.mp_v _ _ hf (getD_Ve L node hV k hk))

theorem allV_pushNode (node lz : List Int) (hV : AllV L.toMon node) (hF : AllF L lz) (k : Nat) (hk : 2 * k + 1 < node.length) :
    AllV L.toMon (pushNode L node lz k) := by
  unfold pushNode
  exact allV_set L.toMon _ (allV_set L.toMon node hV _ _ (L.mp_v _ _ (getD_F L lz hF k) (getD_Ve L node hV _ (by omega))))
    _ _ (L.mp_v _ _ (getD_F L lz hF k) (getD_Ve L node hV _ hk))

theorem allV_updNode (node : List Int) (hV : AllV L.toMon node) (i : Nat) (hi : 2 * i + 1 < node.length) :
    AllV L.toMon (updNode L node i) := by
  unfold updNode
  exact allV_set L.toMon node hV i _ (L.closed _ _ (getD_Ve L node hV _ (by omega)) (getD_Ve L node hV _ hi))

/-- The nodes of `S` have no pending action. -/
def LzFid (S : Nat → Prop) (lz : List Int) : Prop := ∀ s, S s → lz.getD s L.fid = L.fid

theorem pushLz_fid (N : Nat) (lz : List Int) (k : Nat) (S : Nat → Prop) (hk1 : 1 ≤ k) (hk2 : k < N) (hlen : lz.length = N)
    (hS : ∀ s, S s → s < k) (h : LzFid L S lz) : LzFid L (fun s => S s ∨ s = k) (pushLz L N lz k) := by
  intro s hs
  rw [pushLz_get L N lz k hk1 hk2 hlen s]
  rcases hs with hs | hs
  · have := hS s hs
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact h s hs
  · rw [if_pos hs]

/-- The abstract contents `A` of a lazy tree with `N` leaves, as a leaf function. -/
def lfA (A : List Int) (N : Nat) : Nat → Int := fun x => A.getD (x - N) L.e

/-- `node`/`lz` represent the array `A`. -/
def Rep (N : Nat) (A node lz : List Int) : Prop :=
  node.length = 2 * N ∧ lz.length = N ∧ A.length = N ∧ AllV L.toMon node ∧ AllF L lz ∧ AllV L.toMon A ∧
    Ext L (lfA L A N) N node lz (fun _ => False)

theorem leafV_lfA (A : List Int) (N : Nat) (hA : AllV L.toMon A) (hlen : A.length = N) : LeafV L (lfA L A N) N := by
  intro x hx1 hx2
  exact getD_Ve L A hA _ (by omega)

/-- After pushing all strict ancestors of a leaf `p`, the leaf holds its true value. -/
theorem rep_leaf (N : Nat) (A node lz : List Int) (p : Nat) (hp1 : N ≤ p) (hp2 : p < 2 * N)
    (hR : Rep L N A node lz) (hCl : Cl L lz p) : node.getD p L.e = A.getD (p - N) L.e := by
  obtain ⟨hn, hl, hA, hV, hF, hAV, hE⟩ := hR
  have hG := G_clean L lz hF p hCl
  have := hE p (by omega) hp2 (fun h => h)
  rw [hG, L.mp_id _ (getD_Ve L node hV p (by omega)), tr_leaf L _ N p (by omega)] at this
  exact this

theorem rep_push (N : Nat) (A node lz : List Int) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < N) (hR : Rep L N A node lz) :
    Rep L N A (pushNode L node lz k) (pushLz L N lz k) := by
  obtain ⟨hn, hl, hA, hV, hF, hAV, hE⟩ := hR
  refine ⟨?_, ?_, hA, allV_pushNode L node lz hV hF k (by omega), allF_pushLz L N lz hF k, hAV, ?_⟩
  · rw [pushNode_len]; exact hn
  · rw [pushLz_len]; exact hl
  · exact ext_push L (lfA L A N) N node lz _ k hk1 hk2 hl hn hV hF hE

/-! ### Writing a leaf and updating the ancestors -/

theorem ext_congr (lf lf' : Nat → Int) (N : Nat) (node lz : List Int) (B : Nat → Prop)
    (h : ∀ x, N ≤ x → x < 2 * N → lf' x = lf x) (hE : Ext L lf N node lz B) : Ext L lf' N node lz B := by
  intro d hd1 hd2 hB
  rw [tr_congr L lf lf' N d hd1 hd2 (fun x a b _ => h x a b)]
  exact hE d hd1 hd2 hB

theorem ext_weaken (lf : Nat → Int) (N : Nat) (node lz : List Int) (B1 B2 : Nat → Prop)
    (hB : ∀ d, 1 ≤ d → d < 2 * N → B1 d → B2 d) (hE : Ext L lf N node lz B1) : Ext L lf N node lz B2 := by
  intro d hd1 hd2 hB2
  exact hE d hd1 hd2 (fun hb => hB2 (hB d hd1 hd2 hb))

/-- After writing the leaf `p` and updating its ancestors at the levels `1 .. t`. -/
def SInvL (N : Nat) (A' : List Int) (p h t : Nat) (node lz : List Int) : Prop :=
  node.length = 2 * N ∧ lz.length = N ∧ AllV L.toMon node ∧ AllF L lz ∧ AllV L.toMon A' ∧ A'.length = N ∧
    LzFid L (fun s => ∃ u, 0 < u ∧ u ≤ h ∧ s = p / 2 ^ u) lz ∧
    Ext L (lfA L A' N) N node lz (fun d => ∃ s, t < s ∧ s ≤ h ∧ d = p / 2 ^ s)

theorem sInvL_step (N : Nat) (A' : List Int) (p h t : Nat) (node lz : List Int) (hN : N = 2 ^ h) (hp1 : N ≤ p) (hp2 : p < 2 * N)
    (ht : t + 1 ≤ h) (hS : SInvL L N A' p h t node lz) :
    SInvL L N A' p h (t + 1) (updNode L node (p / 2 ^ (t + 1))) lz := by
  obtain ⟨hn, hl, hV, hF, hAV, hA, hz, hE⟩ := hS
  have hpos : 0 < 2 ^ (t + 1) := Nat.two_pow_pos _
  have hi1 : 1 ≤ p / 2 ^ (t + 1) := by
    rw [Nat.le_div_iff_mul_le hpos]
    have : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) ht
    omega
  have hiN : p / 2 ^ (t + 1) < N := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have : 2 ^ 1 ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : N * 2 ≤ N * 2 ^ (t + 1) := Nat.mul_le_mul_left N (by simpa using this)
    omega
  have hlzi : lz.getD (p / 2 ^ (t + 1)) L.fid = L.fid := hz _ ⟨t + 1, by omega, ht, rfl⟩
  have hB1 : ¬ (∃ s, t < s ∧ s ≤ h ∧ 2 * (p / 2 ^ (t + 1)) = p / 2 ^ s) := by
    rintro ⟨s, hs1, hs2, hs3⟩
    have : p / 2 ^ s ≤ p / 2 ^ (t + 1) := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (by omega)) hpos
    omega
  have hB2 : ¬ (∃ s, t < s ∧ s ≤ h ∧ 2 * (p / 2 ^ (t + 1)) + 1 = p / 2 ^ s) := by
    rintro ⟨s, hs1, hs2, hs3⟩
    have : p / 2 ^ s ≤ p / 2 ^ (t + 1) := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (by omega)) hpos
    omega
  refine ⟨?_, hl, allV_updNode L node hV _ (by omega), hF, hAV, hA, hz, ?_⟩
  · unfold updNode; simp [hn]
  · have := ext_update L (lfA L A' N) N node lz _ (p / 2 ^ (t + 1)) hi1 hiN hl hn hV hF hlzi hB1 hB2 hE
    refine ext_weaken L _ N _ _ _ _ ?_ this
    rintro d _ _ ⟨⟨s, hs1, hs2, rfl⟩, hne⟩
    refine ⟨s, ?_, hs2, rfl⟩
    apply Classical.byContradiction
    intro hcon
    have : s = t + 1 := by omega
    exact hne (by rw [this])

theorem cl_of_lzfid (N h p : Nat) (hN : N = 2 ^ h) (hp1 : N ≤ p) (hp2 : p < 2 * N) (lz : List Int)
    (hF : LzFid L (fun s => ∃ t, 0 < t ∧ t ≤ h ∧ s = p / 2 ^ t) lz) : Cl L lz p := by
  intro t ht h1
  apply hF
  refine ⟨t, ht, ?_, rfl⟩
  apply Classical.byContradiction
  intro hth
  have : 2 ^ (h + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : p < 2 ^ t := by rw [Nat.pow_succ] at this; omega
  rw [Nat.div_eq_of_lt hlt] at h1
  omega

theorem sInvL_init (N : Nat) (A : List Int) (p h idx : Nat) (val : Int) (node lz : List Int) (hN : N = 2 ^ h) (hp : p = idx + N)
    (hidx : idx < N) (hval : L.V val) (hR : Rep L N A node lz)
    (hF : LzFid L (fun s => ∃ u, 0 < u ∧ u ≤ h ∧ s = p / 2 ^ u) lz) :
    SInvL L N (A.set idx val) p h 0 (node.set p val) lz := by
  obtain ⟨hn, hl, hA, hV, hFa, hAV, hE⟩ := hR
  have hCl := cl_of_lzfid L N h p hN (by omega) (by omega) lz hF
  have hG := G_clean L lz hFa p hCl
  have hE1 := ext_setleaf L (lfA L A N) N node lz _ p val (by omega) (by omega) hl hn hFa hG hval hE
  refine ⟨by simp [hn], hl, allV_set L.toMon node hV p val hval, hFa, allV_set L.toMon A hAV idx val hval, by simp [hA], hF, ?_⟩
  have hE2 := ext_congr L _ (lfA L (A.set idx val) N) N _ _ _ (fun x hx1 hx2 => by
    unfold lfA
    rw [getD_set_default]
    by_cases hxp : x = p
    · subst hxp
      have : x - N = idx := by omega
      rw [this, if_pos ⟨rfl, by omega⟩]
      simp
    · have : ¬ (x - N = idx ∧ idx < A.length) := fun h' => hxp (by omega)
      rw [if_neg this]
      simp [hxp]) hE1
  refine ext_weaken L _ N _ _ _ _ ?_ hE2
  rintro d hd1 hd2 (hb | ⟨⟨u, hu⟩, hne⟩)
  · exact hb.elim
  · have hu0 : u ≠ 0 := by
      intro h0; rw [h0] at hu; simp at hu; exact hne hu
    refine ⟨u, by omega, ?_, hu⟩
    apply Classical.byContradiction
    intro huh
    have : 2 ^ (h + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : p < 2 ^ u := by rw [Nat.pow_succ] at this; omega
    rw [hu, Nat.div_eq_of_lt hlt] at hd1
    omega

theorem rep_of_sInvL (N : Nat) (A' : List Int) (p h : Nat) (node lz : List Int) (hS : SInvL L N A' p h h node lz) :
    Rep L N A' node lz := by
  obtain ⟨hn, hl, hV, hF, hAV, hA, hz, hE⟩ := hS
  refine ⟨hn, hl, hA, hV, hF, hAV, ?_⟩
  refine ext_weaken L _ N _ _ _ _ ?_ hE
  rintro d _ _ ⟨s, hs1, hs2, _⟩
  omega

theorem anc_leaf_eq (N x p : Nat) (hp : N ≤ p) (hx : x < 2 * N) (h : Anc x p) : x = p := by
  obtain ⟨t, ht⟩ := h
  cases t with
  | zero => simpa using ht.symm
  | succ t =>
    exfalso
    have h1 : x / 2 ^ (t + 1) ≤ x / 2 := by
      apply Nat.div_le_div_left _ (by decide)
      rw [Nat.pow_succ]
      have : 0 < 2 ^ t := Nat.two_pow_pos t
      omega
    omega

open Classical in
theorem sInvL_init_apply (N : Nat) (A : List Int) (p h idx : Nat) (f : Int) (node lz : List Int) (hN : N = 2 ^ h) (hp : p = idx + N)
    (hidx : idx < N) (hf : L.Fv f) (hR : Rep L N A node lz)
    (hF : LzFid L (fun s => ∃ u, 0 < u ∧ u ≤ h ∧ s = p / 2 ^ u) lz) :
    SInvL L N (A.set idx (L.mp f (A.getD idx L.e))) p h 0 (applyNode L node p f) lz := by
  obtain ⟨hn, hl, hA, hV, hFa, hAV, hE⟩ := hR
  have hCl := cl_of_lzfid L N h p hN (by omega) (by omega) lz hF
  have hG := G_clean L lz hFa p hCl
  have hAidx : L.V (A.getD idx L.e) := getD_Ve L A hAV idx (by omega)
  have hmv : L.V (L.mp f (A.getD idx L.e)) := L.mp_v _ _ hf hAidx
  have hE1 := ext_apply L (lfA L A N) (fun x => if Anc x p then L.mp f (lfA L A N x) else lfA L A N x) N node lz _ p f
    (by omega) (by omega) hl hn hV hFa hf (leafV_lfA L A N hAV hA) hG (fun d hd => id) 
    (fun x hx => by simp [hx]) (fun x hx => by simp [hx]) hE
  refine ⟨by unfold applyNode; simp [hn], hl, allV_applyNode L node hV p f hf (by omega), hFa,
    allV_set L.toMon A hAV idx _ hmv, by simp [hA], hF, ?_⟩
  have hE2 := ext_congr L _ (lfA L (A.set idx (L.mp f (A.getD idx L.e))) N) N _ _ _ (fun x hx1 hx2 => by
    unfold lfA
    rw [getD_set_default]
    by_cases hxp : x = p
    · subst hxp
      have : x - N = idx := by omega
      rw [this, if_pos ⟨rfl, by omega⟩]
      simp [anc_refl]
    · have : ¬ (x - N = idx ∧ idx < A.length) := fun h' => hxp (by omega)
      rw [if_neg this]
      have hna : ¬ Anc x p := fun hh => hxp (anc_leaf_eq N x p (by omega) hx2 hh)
      simp [hna]) hE1
  have hAl : alz L N lz p f = lz := by unfold alz; rw [if_neg (by omega)]
  rw [hAl] at hE2
  refine ext_weaken L _ N _ _ _ _ ?_ hE2
  rintro d hd1 hd2 (hb | ⟨⟨u, hu⟩, hne⟩)
  · exact hb.elim
  · have hu0 : u ≠ 0 := by
      intro h0; rw [h0] at hu; simp at hu; exact hne hu
    refine ⟨u, by omega, ?_, hu⟩
    apply Classical.byContradiction
    intro huh
    have : 2 ^ (h + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : p < 2 ^ u := by rw [Nat.pow_succ] at this; omega
    rw [hu, Nat.div_eq_of_lt hlt] at hd1
    omega

theorem pushLz_fid2 (N : Nat) (lz : List Int) (k : Nat) (S : Nat → Prop) (hk1 : 1 ≤ k) (hk2 : k < N) (hlen : lz.length = N)
    (hS : ∀ s, S s → s ≠ 2 * k ∧ s ≠ 2 * k + 1) (h : LzFid L S lz) :
    LzFid L (fun s => S s ∨ s = k) (pushLz L N lz k) := by
  intro s hs
  rw [pushLz_get L N lz k hk1 hk2 hlen s]
  rcases hs with hs | hs
  · by_cases hsk : s = k
    · rw [if_pos hsk]
    · obtain ⟨h1, h2⟩ := hS s hs
      rw [if_neg hsk, if_neg (fun h' => h1 h'.1), if_neg (fun h' => h2 h'.1)]
      exact h s hs
  · rw [if_pos hs]

/-! ### A freshly built tree -/

theorem G_allfid (lz : List Int) (hF : AllF L lz) (h : ∀ j, lz.getD j L.fid = L.fid) : ∀ k, G L lz k = L.fid := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k ≤ 1
    · exact G_le L lz k hk
    · rw [G_ge L lz k (by omega), ih (k / 2) (by omega), h]
      exact L.comp_idl _ L.fid_v

theorem tr_of_tinv (V : List Int) (N : Nat) (lf : Nat → Int) (hT : TInv L.toMon V N)
    (hleaf : ∀ x, N ≤ x → x < 2 * N → V.getD x 0 = lf x) :
    ∀ d, 1 ≤ d → d < 2 * N → V.getD d 0 = tr L lf N d := by
  have key : ∀ m d, 2 * N - d = m → 1 ≤ d → d < 2 * N → V.getD d 0 = tr L lf N d := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro d hm h1 h2
      by_cases hd : d < N
      · rw [tr_node L lf N d h1 hd, hT.2.2 d h1 hd,
          ih (2 * N - 2 * d) (by omega) (2 * d) rfl (by omega) (by omega),
          ih (2 * N - (2 * d + 1)) (by omega) (2 * d + 1) rfl (by omega) (by omega)]
      · rw [tr_leaf L lf N d (by omega)]
        exact hleaf d (by omega) h2
  intro d h1 h2
  exact key _ d rfl h1 h2

end Proofs.LazySegMath
