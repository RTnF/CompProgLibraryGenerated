import Proofs.Cpp.Lib.SegmentTreeMath

/-! # The mathematics of the lazy segment tree

`Act M F` is a monoid `m : Mon M` with an action of the tags `F`: `ap f` is a monoid endomorphism on the
representable values, `comp f g` is "`g` first, then `f`" and `id` acts trivially. The node values are `a : Nat → M`
and the tags of the inner nodes `z : Nat → F`. The tree invariant (`LTInv`) is the one of ACL: an inner node holds the
tag applied to the product of its children. `P z k x` applies the tags of the strict ancestors of `k` to `x` (the
parent's tag first); `virt a z k = P z k (a k)` is the tree after pushing every tag down. It satisfies the plain tree
invariant `TInv` of `Proofs.Cpp.SegmentTreeMath`, so every fact about the plain tree applies to it. -/

namespace Proofs.Cpp.LazySegmentTreeMath

open Proofs.Cpp.SegmentTreeMath

structure Act (M F : Type) where
  m : Mon M
  VF : F → Prop
  ap : F → M → M
  comp : F → F → F
  id : F
  hid : VF id
  hcomp : ∀ f g, VF f → VF g → VF (comp f g)
  ap_V : ∀ f x, VF f → m.V x → m.V (ap f x)
  ap_op : ∀ f x y, VF f → m.V x → m.V y → ap f (m.op x y) = m.op (ap f x) (ap f y)
  ap_comp : ∀ f g x, VF f → VF g → m.V x → ap (comp f g) x = ap f (ap g x)
  ap_id : ∀ x, m.V x → ap id x = x

variable {M F : Type} (A : Act M F)

/-- The tags of the strict ancestors of `k`, applied to `x` (nearest first). -/
def P (z : Nat → F) : Nat → M → M
  | k, x => if h : k ≤ 1 then x else P z (k / 2) (A.ap (z (k / 2)) x)
termination_by k => k
decreasing_by omega

theorem P_le_one (z : Nat → F) (k : Nat) (x : M) (hk : k ≤ 1) : P A z k x = x := by
  rw [P]; simp [hk]

theorem P_step (z : Nat → F) (k : Nat) (x : M) (hk : 2 ≤ k) : P A z k x = P A z (k / 2) (A.ap (z (k / 2)) x) := by
  rw [P]; simp [show ¬ k ≤ 1 by omega]

/-- The tags of all inner nodes are representable. -/
def AllVF (z : Nat → F) (N : Nat) : Prop := ∀ k, 1 ≤ k → k < N → A.VF (z k)

theorem P_V (z : Nat → F) (N : Nat) (hz : AllVF A z N) : ∀ k x, k < 2 * N → A.m.V x → A.m.V (P A z k x) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases h1 : k ≤ 1
    · rw [P_le_one A z k x h1]; exact hx
    · rw [P_step A z k x (by omega)]
      exact ih (k / 2) (by omega) _ (by omega) (A.ap_V _ _ (hz _ (by omega) (by omega)) hx)

theorem P_op (z : Nat → F) (N : Nat) (hz : AllVF A z N) :
    ∀ k x y, k < 2 * N → A.m.V x → A.m.V y → P A z k (A.m.op x y) = A.m.op (P A z k x) (P A z k y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x y hk hx hy
    by_cases h1 : k ≤ 1
    · simp only [P_le_one A z k _ h1]
    · simp only [P_step A z k _ (by omega)]
      have hf := hz (k / 2) (by omega) (by omega)
      rw [A.ap_op _ _ _ hf hx hy]
      exact ih (k / 2) (by omega) _ _ (by omega) (A.ap_V _ _ hf hx) (A.ap_V _ _ hf hy)

/-- The lazy tree invariant: an inner node holds its tag applied to the product of its children. -/
def LTInv (a : Nat → M) (z : Nat → F) (N : Nat) : Prop :=
  ∀ k, 1 ≤ k → k < N → a k = A.ap (z k) (A.m.op (a (2 * k)) (a (2 * k + 1)))

/-- The tree after pushing every tag down to the leaves. -/
def virt (a : Nat → M) (z : Nat → F) : Nat → M := fun k => P A z k (a k)

theorem virt_tree (a : Nat → M) (z : Nat → F) (N : Nat) (hV : AllV A.m a (2 * N)) (hz : AllVF A z N)
    (hT : LTInv A a z N) : TInv A.m (virt A a z) N := by
  intro k h1 h2
  simp only [virt]
  have hc1 : P A z (2 * k) (a (2 * k)) = P A z k (A.ap (z k) (a (2 * k))) := by
    rw [P_step A z (2 * k) _ (by omega), show 2 * k / 2 = k by omega]
  have hc2 : P A z (2 * k + 1) (a (2 * k + 1)) = P A z k (A.ap (z k) (a (2 * k + 1))) := by
    rw [P_step A z (2 * k + 1) _ (by omega), show (2 * k + 1) / 2 = k by omega]
  have hf := hz k h1 h2
  have v0 := hV (2 * k) (by omega)
  have v1 := hV (2 * k + 1) (by omega)
  rw [hc1, hc2, ← P_op A z N hz k _ _ (by omega) (A.ap_V _ _ hf v0) (A.ap_V _ _ hf v1), ← A.ap_op _ _ _ hf v0 v1,
    ← hT k h1 h2]

theorem virt_V (a : Nat → M) (z : Nat → F) (N : Nat) (hV : AllV A.m a (2 * N)) (hz : AllVF A z N) :
    AllV A.m (virt A a z) (2 * N) := fun k hk => P_V A z N hz k _ hk (hV k hk)

/-- A node whose strict ancestors all carry the identity tag reads the same as the pushed-down tree. -/
theorem virt_of_id (a : Nat → M) (z : Nat → F) (N : Nat) (hV : AllV A.m a (2 * N)) :
    ∀ k, k < 2 * N → (∀ j, 1 ≤ j → Anc k j → j ≠ k → z j = A.id) → virt A a z k = a k := by
  intro k hk hid
  simp only [virt]
  suffices ∀ k x, k < 2 * N → A.m.V x → (∀ j, 1 ≤ j → Anc k j → j ≠ k → z j = A.id) → P A z k x = x from
    this k (a k) hk (hV k hk) hid
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx hj
    by_cases h1 : k ≤ 1
    · exact P_le_one A z k x h1
    · rw [P_step A z k x (by omega), hj (k / 2) (by omega) ⟨1, by simp⟩ (by omega), A.ap_id _ hx]
      apply ih (k / 2) (by omega) x (by omega) hx
      intro j hj1 ⟨t, ht⟩ hne
      apply hj j hj1 ⟨t + 1, by rw [ht, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]⟩
      intro e
      have : k / 2 / 2 ^ t ≤ k / 2 := Nat.div_le_self _ _
      rw [ht] at e
      omega

/-! ## `push(k)` -/

/-- `k` is a strict ancestor of `j`. -/
def SAnc (k j : Nat) : Prop := ∃ t, 1 ≤ t ∧ j / 2 ^ t = k

theorem sanc_step (k j : Nat) (hj : 2 ≤ j) : SAnc k j ↔ j / 2 = k ∨ SAnc k (j / 2) := by
  constructor
  · rintro ⟨t, ht, e⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · left; subst h0; simpa using e
    · right; refine ⟨s, h0, ?_⟩
      rw [← e, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · rintro (e | ⟨t, ht, e⟩)
    · exact ⟨1, le_refl _, by simpa using e⟩
    · refine ⟨t + 1, by omega, ?_⟩
      rw [← e, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem sanc_le (k j : Nat) (h : SAnc k j) (hj : 1 ≤ j) : k < j := by
  obtain ⟨t, ht, rfl⟩ := h
  have : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  exact Nat.div_lt_self hj (by omega)

theorem sanc_two (k j : Nat) (h : SAnc k j) (hk : 1 ≤ k) : 2 ≤ j := by
  obtain ⟨t, ht, e⟩ := h
  by_contra hc
  have : j / 2 ^ t = 0 := by
    apply Nat.div_eq_of_lt
    calc j < 2 := by omega
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  omega

/-- The tags after `push(k)`. -/
def pushZ (z : Nat → F) (N k : Nat) : Nat → F := fun j =>
  if j = k then A.id
  else if (j = 2 * k ∨ j = 2 * k + 1) ∧ j < N then A.comp (z k) (z j) else z j

/-- The values after `push(k)`. -/
def pushA (a : Nat → M) (z : Nat → F) (k : Nat) : Nat → M := fun j =>
  if j = 2 * k ∨ j = 2 * k + 1 then A.ap (z k) (a j) else a j

theorem P_push_out (z : Nat → F) (N k : Nat) (hk : 1 ≤ k) :
    ∀ j x, ¬ SAnc k j → P A (pushZ A z N k) j x = P A z j x := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hj
    by_cases h1 : j ≤ 1
    · simp only [P_le_one A _ j x h1]
    · rw [P_step A _ j x (by omega), P_step A _ j x (by omega)]
      have hs := (sanc_step k j (by omega)).not.mp hj
      push_neg at hs
      have hne : j / 2 ≠ k := hs.1
      have hc : ¬ (j / 2 = 2 * k ∨ j / 2 = 2 * k + 1) := by
        rintro (e | e) <;> exact hs.2 ⟨1, le_refl _, by simp [e]; try omega⟩
      simp only [pushZ, if_neg hne, hc, false_and, ite_false]
      exact ih (j / 2) (by omega) _ hs.2

theorem P_push_child (z : Nat → F) (N k : Nat) (hk : 1 ≤ k) (c : Nat) (hc : c / 2 = k) (hc2 : 2 ≤ c) (x : M) :
    P A (pushZ A z N k) c x = P A z k (A.ap A.id x) := by
  rw [P_step A _ c x hc2, hc]
  simp only [pushZ, ite_true]
  exact P_push_out A z N k hk k _ (fun h => absurd (sanc_le k k h hk) (lt_irrefl _))

theorem P_push_deep (z : Nat → F) (N k : Nat) (hz : AllVF A z N) (hk : 1 ≤ k) (hkN : k < N) :
    ∀ j x, SAnc k (j / 2) → j < 2 * N → A.m.V x → P A (pushZ A z N k) j x = P A z j x := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hj hjN hx
    have hj2 : 2 ≤ j / 2 := sanc_two k (j / 2) hj hk
    rw [P_step A _ j x (by omega), P_step A z j x (by omega)]
    rcases (sanc_step k (j / 2) hj2).mp hj with e | e
    · -- j / 2 is a child of k
      have hcN' : j / 2 < N := by omega
      rw [P_push_child A z N k hk (j / 2) e (by omega)]
      simp only [pushZ, show j / 2 ≠ k by omega, ite_false, show (j / 2 = 2 * k ∨ j / 2 = 2 * k + 1) by omega,
        true_and, if_pos hcN']
      have hf := hz k hk hkN
      have hg := hz (j / 2) (by omega) hcN'
      rw [A.ap_id _ (A.ap_V _ _ (A.hcomp _ _ hf hg) hx), A.ap_comp _ _ _ hf hg hx,
        P_step A z (j / 2) _ (by omega), e]
    · have h4 := sanc_two k (j / 2 / 2) e hk
      have hlt := sanc_le k (j / 2 / 2) e (by omega)
      have hne : j / 2 ≠ k := by omega
      have hc : ¬ (j / 2 = 2 * k ∨ j / 2 = 2 * k + 1) := by omega
      simp only [pushZ, if_neg hne, hc, false_and, ite_false]
      exact ih (j / 2) (by omega) _ e (by omega) (A.ap_V _ _ (hz _ (by omega) (by omega)) hx)

theorem push_V (a : Nat → M) (z : Nat → F) (N k : Nat) (hV : AllV A.m a (2 * N)) (hz : AllVF A z N) (hk : 1 ≤ k)
    (hkN : k < N) : AllV A.m (pushA A a z k) (2 * N) ∧ AllVF A (pushZ A z N k) N := by
  have hf := hz k hk hkN
  refine ⟨fun j hj => ?_, fun j h1 h2 => ?_⟩
  · simp only [pushA]; split
    · exact A.ap_V _ _ hf (hV j hj)
    · exact hV j hj
  · simp only [pushZ]; split
    · exact A.hid
    · split
      · rename_i h; exact A.hcomp _ _ hf (hz j h1 h2)
      · exact hz j h1 h2

theorem push_tree (a : Nat → M) (z : Nat → F) (N k : Nat) (hV : AllV A.m a (2 * N)) (hz : AllVF A z N)
    (hT : LTInv A a z N) (hk : 1 ≤ k) (hkN : k < N) : LTInv A (pushA A a z k) (pushZ A z N k) N := by
  have hf := hz k hk hkN
  intro j h1 h2
  have v0 := hV (2 * j) (by omega)
  have v1 := hV (2 * j + 1) (by omega)
  by_cases hjk : j = k
  · subst hjk
    simp only [pushA, pushZ, ite_true, show ¬ (j = 2 * j ∨ j = 2 * j + 1) by omega, ite_false, true_or, or_true]
    rw [A.ap_id _ (A.m.closed _ _ (A.ap_V _ _ hf v0) (A.ap_V _ _ hf v1)), ← A.ap_op _ _ _ hf v0 v1]
    exact hT j h1 h2
  · by_cases hc : j = 2 * k ∨ j = 2 * k + 1
    · have hg := hz j h1 h2
      simp only [pushA, pushZ, if_pos hc, if_neg hjk, hc, true_and, if_pos h2,
        show ¬ (2 * j = 2 * k ∨ 2 * j = 2 * k + 1) by omega, show ¬ (2 * j + 1 = 2 * k ∨ 2 * j + 1 = 2 * k + 1) by omega,
        ite_false, ite_true]
      rw [A.ap_comp _ _ _ hf hg (A.m.closed _ _ v0 v1), ← hT j h1 h2]
    · simp only [pushA, pushZ, if_neg hc, if_neg hjk, hc, false_and, ite_false,
        show ¬ (2 * j = 2 * k ∨ 2 * j = 2 * k + 1) by omega, show ¬ (2 * j + 1 = 2 * k ∨ 2 * j + 1 = 2 * k + 1) by omega]
      exact hT j h1 h2

theorem push_virt (a : Nat → M) (z : Nat → F) (N k : Nat) (hV : AllV A.m a (2 * N)) (hz : AllVF A z N)
    (hk : 1 ≤ k) (hkN : k < N) : ∀ j, j < 2 * N → virt A (pushA A a z k) (pushZ A z N k) j = virt A a z j := by
  intro j hj
  simp only [virt]
  by_cases hs : SAnc k j
  · have hj2 := sanc_two k j hs hk
    rcases (sanc_step k j hj2).mp hs with e | e
    · have hc : j = 2 * k ∨ j = 2 * k + 1 := by omega
      have hf := hz k hk hkN
      simp only [pushA, if_pos hc]
      rw [P_push_child A z N k hk j e hj2, A.ap_id _ (A.ap_V _ _ hf (hV j hj)), P_step A z j _ hj2, e]
    · have h4 := sanc_two k (j / 2) e hk
      have hlt := sanc_le k (j / 2) e (by omega)
      simp only [pushA, show ¬ (j = 2 * k ∨ j = 2 * k + 1) by omega, ite_false]
      exact P_push_deep A z N k hz hk hkN j _ e hj (hV j hj)
  · have hc : ¬ (j = 2 * k ∨ j = 2 * k + 1) := by
      rintro (e | e) <;> exact hs ⟨1, le_refl _, by simp [e]; try omega⟩
    simp only [pushA, if_neg hc]
    exact P_push_out A z N k hk j _ hs

/-! ## Trivial tags -/

/-- A tag that acts as the identity on the representable values. -/
def IdTag (f : F) : Prop := ∀ x, A.m.V x → A.ap f x = x

theorem idTag_id : IdTag A A.id := fun x hx => A.ap_id x hx

/-- A node whose strict ancestors all carry trivial tags reads the same as the pushed-down tree. -/
theorem P_of_idTag (z : Nat → F) : ∀ k x, A.m.V x → (∀ j, 1 ≤ j → SAnc j k → IdTag A (z j)) → P A z k x = x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hj
    by_cases h1 : k ≤ 1
    · exact P_le_one A z k x h1
    · rw [P_step A z k x (by omega), hj (k / 2) (by omega) ⟨1, le_refl _, by simp⟩ x hx]
      apply ih (k / 2) (by omega) x hx
      intro j h1 hs
      exact hj j h1 ((sanc_step j k (by omega)).mpr (Or.inr hs))

theorem pushZ_other (z : Nat → F) (N k j : Nat) (h0 : j ≠ k) (h1 : j ≠ 2 * k) (h2 : j ≠ 2 * k + 1) :
    pushZ A z N k j = z j := by
  simp only [pushZ, if_neg h0, show ¬ ((j = 2 * k ∨ j = 2 * k + 1) ∧ j < N) by omega, ite_false]

theorem pushZ_self (z : Nat → F) (N k : Nat) : pushZ A z N k k = A.id := by simp [pushZ]

/-- The state of a lazy tree: values, tags, the tree invariant and representability. -/
def LState (a : Nat → M) (z : Nat → F) (N : Nat) : Prop :=
  AllV A.m a (2 * N) ∧ AllVF A z N ∧ LTInv A a z N

theorem push_state (a : Nat → M) (z : Nat → F) (N k : Nat) (h : LState A a z N) (hk : 1 ≤ k) (hkN : k < N) :
    LState A (pushA A a z k) (pushZ A z N k) N ∧
      (∀ j, j < 2 * N → virt A (pushA A a z k) (pushZ A z N k) j = virt A a z j) := by
  obtain ⟨hV, hz, hT⟩ := h
  obtain ⟨hV', hz'⟩ := push_V A a z N k hV hz hk hkN
  exact ⟨⟨hV', hz', push_tree A a z N k hV hz hT hk hkN⟩, push_virt A a z N k hV hz hk hkN⟩

/-! ## The nodes read by the bottom-up loops

At level `t` the left cursor is `⌈l0 / 2^t⌉` and the right cursor `⌊r0 / 2^t⌋`. A node read there (the left cursor
when it is odd, the node before the right cursor when that is odd) has only strict ancestors that cut through `l0` or
`r0`; those are exactly the nodes pushed before the loop. -/

theorem odd_succ_div (q u : Nat) (hq : q % 2 = 0) (hu : 1 ≤ u) : (q + 1) / 2 ^ u = q / 2 ^ u := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, show (q + 1) / 2 = q / 2 by omega]

theorem read_left (l0 t x u : Nat) (hx : x = (l0 + 2 ^ t - 1) / 2 ^ t) (hodd : x % 2 = 1) (hu : 1 ≤ u) :
    x / 2 ^ u = l0 / 2 ^ (t + u) ∧ l0 % 2 ^ (t + u) ≠ 0 := by
  have hp := Nat.two_pow_pos t
  have hpu := Nat.two_pow_pos u
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  obtain ⟨q, ρ, hρ, rfl⟩ : ∃ q ρ, ρ < 2 ^ t ∧ l0 = q * 2 ^ t + ρ :=
    ⟨l0 / 2 ^ t, l0 % 2 ^ t, Nat.mod_lt _ hp, by rw [Nat.mul_comm]; exact (Nat.div_add_mod l0 _).symm⟩
  have hdiv : (q * 2 ^ t + ρ) / 2 ^ t = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hρ, Nat.zero_add]
  rw [hdiv]
  rcases Nat.eq_zero_or_pos ρ with h0 | h0
  · subst h0
    have hx' : x = q := by
      rw [hx, Nat.add_zero, show q * 2 ^ t + 2 ^ t - 1 = (2 ^ t - 1) + q * 2 ^ t by omega,
        Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    subst hx'
    refine ⟨rfl, fun hm => ?_⟩
    rw [Nat.add_zero, Nat.mul_comm, Nat.mul_mod_mul_left] at hm
    have : x % 2 ^ u = 0 := by
      rcases Nat.mul_eq_zero.mp hm with h | h
      · omega
      · exact h
    have : 2 ∣ x := Nat.dvd_trans (dvd_pow_self 2 (by omega)) (Nat.dvd_of_mod_eq_zero this)
    omega
  · have hx' : x = q + 1 := by
      rw [hx, show q * 2 ^ t + ρ + 2 ^ t - 1 = (ρ - 1) + (q + 1) * 2 ^ t by rw [Nat.add_mul]; omega,
        Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    subst hx'
    refine ⟨odd_succ_div q u (by omega) hu, fun hm => ?_⟩
    have : 2 ^ t ∣ q * 2 ^ t + ρ := Nat.dvd_trans (Dvd.intro _ rfl) (Nat.dvd_of_mod_eq_zero hm)
    have : 2 ^ t ∣ ρ := (Nat.dvd_add_right (dvd_mul_left _ _)).mp this
    have := Nat.le_of_dvd h0 this
    omega

theorem read_right (r0 t y u : Nat) (hy : y = r0 / 2 ^ t) (hodd : y % 2 = 1) (hu : 1 ≤ u) :
    (y - 1) / 2 ^ u = (r0 - 1) / 2 ^ (t + u) ∧ r0 % 2 ^ (t + u) ≠ 0 := by
  have hp := Nat.two_pow_pos t
  have hpu := Nat.two_pow_pos u
  obtain ⟨ρ, hρ, hr⟩ : ∃ ρ, ρ < 2 ^ t ∧ r0 = y * 2 ^ t + ρ :=
    ⟨r0 % 2 ^ t, Nat.mod_lt _ hp, by rw [hy, Nat.mul_comm]; exact (Nat.div_add_mod r0 _).symm⟩
  subst hr
  have hy1 : 1 ≤ y := by omega
  have hyt : 2 ^ t ≤ y * 2 ^ t := Nat.le_mul_of_pos_left _ hy1
  refine ⟨?_, fun hm => ?_⟩
  · rw [pow_add, ← Nat.div_div_eq_div_mul]
    rcases Nat.eq_zero_or_pos ρ with h0 | h0
    · subst h0
      have e : y * 2 ^ t + 0 - 1 = (2 ^ t - 1) + (y - 1) * 2 ^ t := by rw [Nat.sub_mul, Nat.one_mul]; omega
      rw [e, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (show 2 ^ t - 1 < 2 ^ t by omega), Nat.zero_add]
    · rw [show y * 2 ^ t + ρ - 1 = (ρ - 1) + y * 2 ^ t by omega, Nat.add_mul_div_right _ _ hp,
        Nat.div_eq_of_lt (show ρ - 1 < 2 ^ t by omega), Nat.zero_add]
      have := odd_succ_div (y - 1) u (by omega) hu
      rw [show y - 1 + 1 = y by omega] at this
      exact this.symm
  · rw [pow_add] at hm
    have h1 : 2 ^ t ∣ y * 2 ^ t + ρ := Nat.dvd_trans (Dvd.intro _ rfl) (Nat.dvd_of_mod_eq_zero hm)
    have h2 : 2 ^ t ∣ ρ := (Nat.dvd_add_right (dvd_mul_left _ _)).mp h1
    have hρ0 : ρ = 0 := by
      rcases Nat.eq_zero_or_pos ρ with h | h
      · exact h
      · have := Nat.le_of_dvd h h2; omega
    subst hρ0
    rw [Nat.add_zero, Nat.mul_comm, Nat.mul_mod_mul_left] at hm
    have : y % 2 ^ u = 0 := by
      rcases Nat.mul_eq_zero.mp hm with h | h
      · omega
      · exact h
    have : 2 ∣ y := Nat.dvd_trans (dvd_pow_self 2 (by omega)) (Nat.dvd_of_mod_eq_zero this)
    omega

/-- The cursors of the bottom-up loops: `⌈l0 / 2^t⌉` and `⌊r0 / 2^t⌋`. -/
theorem cursor_left (l0 t x : Nat) (hx : x = (l0 + 2 ^ t - 1) / 2 ^ t) :
    pl1 x / 2 = (l0 + 2 ^ (t + 1) - 1) / 2 ^ (t + 1) := by
  have hp := Nat.two_pow_pos t
  have e : (l0 + 2 ^ t * 2 - 1) / 2 ^ t = x + 1 := by
    rw [hx, show l0 + 2 ^ t * 2 - 1 = (l0 + 2 ^ t - 1) + 1 * 2 ^ t by omega, Nat.add_mul_div_right _ _ hp]
  rw [pow_succ, ← Nat.div_div_eq_div_mul, e]
  unfold pl1; split <;> omega

theorem cursor_right (r0 t y : Nat) (hy : y = r0 / 2 ^ t) : pr1 y / 2 = r0 / 2 ^ (t + 1) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← hy]
  unfold pr1; split <;> omega

/-! ## Point updates: the path from a leaf to the root is recomputed -/

/-- The lazy tree invariant holds at every inner node off the path from `i` to the root. -/
def LSInv (a : Nat → M) (z : Nat → F) (N i : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < N → ¬ Anc i j → a j = A.ap (z j) (A.m.op (a (2 * j)) (a (2 * j + 1)))

theorem lsinv_init (a : Nat → M) (z : Nat → F) (N p : Nat) (x : M) (hT : LTInv A a z N) (hp1 : N ≤ p) :
    LSInv A (upd a p x) z N (p / 2) := by
  intro j hj1 hjN hna
  have c0 : ¬ (j = p) := by omega
  have c1 : ¬ (2 * j = p) := by intro e; apply hna; exact ⟨0, by omega⟩
  have c2 : ¬ (2 * j + 1 = p) := by intro e; apply hna; exact ⟨0, by omega⟩
  simp only [upd, if_neg c0, if_neg c1, if_neg c2]
  exact hT j hj1 hjN

theorem lsinv_step (a : Nat → M) (z : Nat → F) (N i : Nat) (h : LSInv A a z N i) (hi1 : 1 ≤ i) (hiN : i < N)
    (hid : IdTag A (z i)) (hv : A.m.V (A.m.op (a (2 * i)) (a (2 * i + 1)))) :
    LSInv A (upd a i (A.m.op (a (2 * i)) (a (2 * i + 1)))) z N (i / 2) := by
  intro j hj1 hjN hna
  by_cases hji : j = i
  · subst hji
    simp only [upd, if_neg (show ¬ (2 * j = j) by omega), if_neg (show ¬ (2 * j + 1 = j) by omega), if_true]
    exact (hid _ hv).symm
  · have hna' : ¬ Anc i j := by
      intro ha
      rcases (anc_step i j).mp ha with e | e
      · exact hji e
      · exact hna e
    have c1 : ¬ (2 * j = i) := by intro e; apply hna; exact ⟨0, by omega⟩
    have c2 : ¬ (2 * j + 1 = i) := by intro e; apply hna; exact ⟨0, by omega⟩
    simp only [upd, if_neg hji, if_neg c1, if_neg c2]
    exact h j hj1 hjN hna'

theorem lsinv_zero (a : Nat → M) (z : Nat → F) (N : Nat) (h : LSInv A a z N 0) : LTInv A a z N := by
  intro j hj1 hjN
  apply h j hj1 hjN
  rintro ⟨t, ht⟩
  simp at ht
  omega

/-- The leaves of the pushed-down tree only depend on the leaf values and the tags. -/
theorem virt_leaf_congr (a b : Nat → M) (z : Nat → F) (j : Nat) (h : a j = b j) : virt A a z j = virt A b z j := by
  simp only [virt, h]

/-! ## Range updates: applying a tag to a canonical node, recomputing a node -/
theorem lvl_bounds' (N h x s : Nat) (hN : N = 2 ^ h) (hx1 : N ≤ x) (hx2 : x < 2 * N) (hs : s ≤ h) :
    2 ^ (h - s) ≤ x / 2 ^ s ∧ x / 2 ^ s < 2 ^ (h + 1 - s) := by
  constructor
  · apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h - s + s = h by omega]; omega
  · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h + 1 - s + s = h + 1 by omega, pow_succ]; omega

/-- The values after `all_apply(k, f)`. -/
def applyA (a : Nat → M) (k : Nat) (f : F) : Nat → M := fun j => if j = k then A.ap f (a j) else a j

/-- The tags after `all_apply(k, f)`: only inner nodes carry tags. -/
def applyZ (z : Nat → F) (N k : Nat) (f : F) : Nat → F := fun j => if j = k ∧ k < N then A.comp f (z j) else z j

/-- The tree invariant outside the nodes `S`. -/
def RTInv (a : Nat → M) (z : Nat → F) (N : Nat) (S : Nat → Prop) : Prop :=
  ∀ k, 1 ≤ k → k < N → ¬ S k → a k = A.ap (z k) (A.m.op (a (2 * k)) (a (2 * k + 1)))

theorem P_congr (z z' : Nat → F) : ∀ j x, (∀ i, SAnc i j → z i = z' i) → P A z j x = P A z' j x := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x h
    by_cases h1 : j ≤ 1
    · simp only [P_le_one A _ j x h1]
    · rw [P_step A _ j x (by omega), P_step A _ j x (by omega)]
      rw [h (j / 2) ⟨1, le_refl _, by simp⟩]
      exact ih (j / 2) (by omega) _ (fun i hi => h i ((sanc_step i j (by omega)).mpr (Or.inr hi)))

/-- Applying `f` at an inner node `k` whose strict ancestors carry trivial tags applies `f` below `k`. -/
theorem P_apply_below (z : Nat → F) (N k : Nat) (f : F) (hf : A.VF f) (hz : AllVF A z N) (hk1 : 1 ≤ k)
    (hkN : k < N) (hid : ∀ j, 1 ≤ j → SAnc j k → IdTag A (z j)) :
    ∀ p x, p < 2 * N → A.m.V x → SAnc k p → P A (applyZ A z N k f) p x = A.ap f (P A z p x) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro x hp hx hs
    have hp2 := sanc_two k p hs hk1
    rw [P_step A _ p x (by omega), P_step A _ p x (by omega)]
    rcases (sanc_step k p hp2).mp hs with e | hs'
    · rw [e]
      have h1 : P A (applyZ A z N k f) k = P A z k := by
        funext y; exact P_congr A _ _ k y (fun i hi => by
          have := sanc_le i k hi (by omega)
          simp [applyZ]; omega)
      have hzk : A.VF (z k) := hz k hk1 hkN
      rw [h1, P_of_idTag A z k _ (by simp [applyZ, hkN]; exact A.ap_V _ _ (A.hcomp _ _ hf hzk) hx) hid,
        P_of_idTag A z k _ (A.ap_V _ _ hzk hx) hid]
      simp [applyZ, hkN, A.ap_comp _ _ _ hf hzk hx]
    · have hne : p / 2 ≠ k := by have := sanc_le k (p / 2) hs' (by omega); omega
      have hzv : A.VF (z (p / 2)) := hz _ (by omega) (by
        rcases hs' with ⟨t, ht, e⟩
        by_contra hc
        have hN2 : 2 * N ≤ 2 * (p / 2) := by omega
        omega)
      simp only [applyZ, hne, false_and, ite_false]
      exact ih (p / 2) (by omega) _ (by omega) (A.ap_V _ _ hzv hx) hs'

open Classical in
theorem virt_apply_leaf (a : Nat → M) (z : Nat → F) (N k : Nat) (f : F) (hf : A.VF f) (hV : AllV A.m a (2 * N))
    (hz : AllVF A z N) (hk1 : 1 ≤ k) (hk2 : k < 2 * N) (hid : ∀ j, 1 ≤ j → SAnc j k → IdTag A (z j))
    (p : Nat) (hp1 : N ≤ p) (hp2 : p < 2 * N) :
    virt A (applyA A a k f) (applyZ A z N k f) p = if p = k ∨ SAnc k p then A.ap f (virt A a z p) else virt A a z p := by
  simp only [virt]
  by_cases hkN : k < N
  · have hpk : p ≠ k := by omega
    have ha : applyA A a k f p = a p := by simp [applyA, hpk]
    rw [ha]
    by_cases hs : SAnc k p
    · simp only [hs, or_true, ite_true]
      exact P_apply_below A z N k f hf hz hk1 hkN hid p _ hp2 (hV p hp2) hs
    · simp only [hs, hpk, or_false, false_or, ite_false]
      exact P_congr A _ _ p _ (fun i hi => by
        have : i ≠ k := fun e => hs (e ▸ hi)
        simp [applyZ, this])
  · have hZ : applyZ A z N k f = z := by funext j; simp [applyZ, hkN]
    rw [hZ]
    by_cases hpk : p = k
    · subst hpk
      simp only [true_or, ite_true, applyA, ite_true]
      rw [P_of_idTag A z p _ (A.ap_V _ _ hf (hV p hp2)) hid, P_of_idTag A z p _ (hV p hp2) hid]
    · have hs : ¬ SAnc k p := by
        rintro ⟨t, ht, e⟩
        have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
        have : k * 2 ^ t ≤ p := by rw [← e]; exact Nat.div_mul_le_self _ _
        have : k * 2 ≤ k * 2 ^ t := Nat.mul_le_mul_left _ (by simpa using ‹2 ^ 1 ≤ 2 ^ t›)
        omega
      simp [hs, hpk, applyA]

theorem dyadic_unique (a b x : Nat) (h1 : 2 ^ a ≤ x) (h2 : x < 2 ^ (a + 1)) (h3 : 2 ^ b ≤ x) (h4 : x < 2 ^ (b + 1)) :
    a = b := by
  by_contra hc
  rcases Nat.lt_or_gt_of_ne hc with h | h
  · have : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
    omega
  · have : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
    omega

/-- A leaf lies below the node `k` of level `t` iff it divides down to `k`. -/
theorem below_iff (N H t k p : Nat) (hN : N = 2 ^ H) (ht : t ≤ H) (hk1 : 2 ^ (H - t) ≤ k)
    (hk2 : k < 2 ^ (H + 1 - t)) (hp1 : N ≤ p) (hp2 : p < 2 * N) : (p = k ∨ SAnc k p) ↔ p / 2 ^ t = k := by
  constructor
  · rintro (rfl | ⟨u, hu, e⟩)
    · have : t = 0 := by
        by_contra hc
        have : 2 ^ (H + 1 - t) ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst this; simp
    · have hu2 : u ≤ H := by
        by_contra hc
        have : p < 2 ^ u := by
          have : 2 ^ (H + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [pow_succ] at this; omega
        rw [Nat.div_eq_of_lt this] at e
        have := Nat.one_le_two_pow (n := H - t)
        omega
      have hb := lvl_bounds' N H p u hN hp1 hp2 hu2
      rw [e] at hb
      have : H - u = H - t := dyadic_unique _ _ k hb.1 (by rw [show H - u + 1 = H + 1 - u by omega]; exact hb.2) hk1
        (by rw [show H - t + 1 = H + 1 - t by omega]; exact hk2)
      have : u = t := by omega
      subst this; exact e
  · intro e
    by_cases ht0 : t = 0
    · subst ht0; left; simpa using e
    · right; exact ⟨t, by omega, e⟩

end Proofs.Cpp.LazySegmentTreeMath
