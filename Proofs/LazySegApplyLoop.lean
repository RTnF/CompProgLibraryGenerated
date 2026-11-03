import Proofs.LazySegApplyMath

namespace Proofs.LazySegApplyLoop
open Proofs.SegTreeMath Proofs.LazySegMath
open Proofs.LazySegChmin (chminMon mi)
open Proofs.LazySegRange
open Proofs.LazySegArith
open Proofs.LazySegApplyMath
open Proofs.LazySegAncLeaf (anc_leaf_iff)

open Classical in
/-- The ideal leaf function after `chmin f` has been applied on the leaves of `cv`. -/
noncomputable def lfCv (A : List Int) (nn : Nat) (f : Int) (cv : Nat → Prop) : Nat → Int :=
  fun x => if cv x then chminMon.mp f (lfA chminMon A nn x) else lfA chminMon A nn x

/-- Loop invariant of the `all_apply` phase of `update(l, r, f)`. -/
def AI (nn : Nat) (A : List Int) (f : Int) (S : Nat → Prop) (cv : Nat → Prop) (node lz : List Int) : Prop :=
  node.length = 2 * nn ∧ lz.length = nn ∧ AllV chminMon.toMon node ∧ AllF chminMon lz ∧ LzFid chminMon S lz ∧
    Ext chminMon (lfCv A nn f cv) nn node lz S

theorem mi_idem (f x : Int) : chminMon.mp f (chminMon.mp f x) = chminMon.mp f x := by
  show mi f (mi f x) = mi f x
  unfold mi
  split_ifs <;> omega

theorem leafV_lfCv (A : List Int) (nn : Nat) (f : Int) (cv : Nat → Prop) (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A)
    (hA : A.length = nn) : LeafV chminMon (lfCv A nn f cv) nn := by
  intro x hx1 hx2
  unfold lfCv
  have hv := leafV_lfA chminMon A nn hAV hA x hx1 hx2
  split
  · exact chminMon.mp_v _ _ hf hv
  · exact hv

theorem ai_block (nn h l0 r0 k j b : Nat) (A : List Int) (f : Int) (cv : Nat → Prop) (node lz : List Int)
    (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (hb1 : l0 ≤ b) (hb2 : b + 2 ^ j ≤ r0)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * nn)
    (hanc : ∀ x, nn ≤ x → x < 2 * nn → (Anc x k ↔ b ≤ x ∧ x < b + 2 ^ j))
    (hSA : ∀ d, 1 ≤ d → Anc k d → d ≠ k → S2 h l0 r0 0 d)
    (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A) (hA : A.length = nn)
    (hI : AI nn A f (S2 h l0 r0 0) cv node lz) :
    AI nn A f (S2 h l0 r0 0) (fun x => cv x ∨ (b ≤ x ∧ x < b + 2 ^ j)) (applyNode chminMon node k f)
      (alz chminMon nn lz k f) := by
  obtain ⟨hn, hlz, hV, hF, hFid, hE⟩ := hI
  have hD := hD_block nn h l0 r0 k j b hN hl hr hb1 hb2 hanc
  have hCl : Cl chminMon lz k := by
    intro t ht h1
    have hpos : 2 ≤ 2 ^ t := by
      have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
      simpa using this
    have hlt : k / 2 ^ t < k := Nat.div_lt_self (by omega) (by omega)
    exact hFid _ (hSA _ h1 ⟨t, rfl⟩ (by omega))
  have hB := apply_block nn node lz f (S2 h l0 r0 0) k j b (lfCv A nn f cv)
    (lfCv A nn f (fun x => cv x ∨ (b ≤ x ∧ x < b + 2 ^ j))) hk1 hk2 hlz hn hV hF hf
    (leafV_lfCv A nn f cv hf hAV hA) hCl hD (fun d _ _ ha hne => hSA d (by omega) ha hne) hanc
    (fun x hx1 hx2 => by
      unfold lfCv
      by_cases hc : cv x
      · by_cases hb : b ≤ x ∧ x < b + 2 ^ j
        · simp [hc, hb, mi_idem]
        · simp [hc, hb]
      · by_cases hb : b ≤ x ∧ x < b + 2 ^ j
        · simp [hc, hb]
        · simp [hc, hb]) hE
  refine ⟨?_, ?_, ?_, ?_, ?_, hB⟩
  · unfold applyNode; simp [hn]
  · rw [alz_len]; exact hlz
  · exact allV_applyNode chminMon node hV k f hf (by omega)
  · exact allF_alz chminMon nn lz hF k f hf
  · intro s hs
    rw [getD_alz chminMon nn lz hlz]
    rw [if_neg]
    · exact hFid s hs
    · rintro ⟨rfl, _⟩
      exact hD s (anc_refl s) hs

theorem ai_congr (nn : Nat) (A : List Int) (f : Int) (S : Nat → Prop) (cv cv' : Nat → Prop) (node lz : List Int)
    (h : ∀ x, cv x ↔ cv' x) (hI : AI nn A f S cv node lz) : AI nn A f S cv' node lz := by
  have : cv = cv' := funext fun x => propext (h x)
  subst this
  exact hI

/-- The covered leaves after `j` rounds, when the loop state is `(a, b)`. -/
def cvj (l0 r0 j a b : Nat) : Nat → Prop := fun x => (l0 ≤ x ∧ x < a * 2 ^ j) ∨ (b * 2 ^ j ≤ x ∧ x < r0)

theorem ceil_ge (l0 q : Nat) (hq : 0 < q) : l0 ≤ ceilDiv l0 q * q := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (l0 + q - 1) q
  have h2 := Nat.mod_lt (l0 + q - 1) hq
  rw [Nat.mul_comm]
  omega

theorem ai_left (nn h l0 r0 j a b : Nat) (A : List Int) (f : Int) (node lz : List Int)
    (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (ha : a = ceilDiv l0 (2 ^ j)) (hb : b = r0 / 2 ^ j) (hab : a < b)
    (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A) (hA : A.length = nn)
    (hI : AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j a b) node lz) :
    AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j (Proofs.SegTreeMath.pl1 a) b)
      (if a % 2 = 1 then applyNode chminMon node a f else node)
      (if a % 2 = 1 then alz chminMon nn lz a f else lz) := by
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  have hce := ceil_ge l0 (2 ^ j) hq
  rw [← ha] at hce
  have hfl : b * 2 ^ j ≤ r0 := by rw [hb]; exact Nat.div_mul_le_self r0 _
  have hbr : b ≤ r0 := by rw [hb]; exact Nat.div_le_self _ _
  have ha1 : 1 ≤ a := by rw [ha]; exact ceil_pos l0 _ (by omega) hq
  have hmul : (a + 1) * 2 ^ j ≤ b * 2 ^ j := Nat.mul_le_mul_right _ hab
  rw [Nat.add_mul, Nat.one_mul] at hmul
  by_cases hodd : a % 2 = 1
  · simp only [if_pos hodd]
    have hanc := fun x hx1 hx2 => anc_leaf_iff nn h a j x hN (by omega) (by omega) hx1 hx2
    have hB := ai_block nn h l0 r0 a j (a * 2 ^ j) A f (cvj l0 r0 j a b) node lz hN hl hr hce (by omega) ha1 (by omega)
      (fun x hx1 hx2 => by rw [hanc x hx1 hx2, Nat.add_mul, Nat.one_mul])
      (fun d hd1 hA' hne => anc_left_mem nn h l0 r0 j hN hl (by rw [← ha]; exact hodd) d hd1 (by rw [← ha]; exact hA') (by rw [← ha]; exact hne))
      hf hAV hA hI
    refine ai_congr nn A f _ _ _ _ _ (fun x => ?_) hB
    unfold cvj Proofs.SegTreeMath.pl1
    rw [if_pos hodd, Nat.add_mul, Nat.one_mul]
    omega
  · simp only [if_neg hodd]
    refine ai_congr nn A f _ _ _ _ _ (fun x => ?_) hI
    unfold Proofs.SegTreeMath.pl1
    rw [if_neg hodd]

theorem ai_right (nn h l0 r0 j a2 b : Nat) (A : List Int) (f : Int) (node lz : List Int)
    (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (hb : b = r0 / 2 ^ j) (ha1 : 1 ≤ a2) (ha2 : l0 ≤ a2 * 2 ^ j) (hle : b % 2 = 1 → a2 + 1 ≤ b)
    (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A) (hA : A.length = nn)
    (hI : AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j a2 b) node lz) :
    AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j a2 (Proofs.SegTreeMath.pr1 b))
      (if b % 2 = 1 then applyNode chminMon node (b - 1) f else node)
      (if b % 2 = 1 then alz chminMon nn lz (b - 1) f else lz) := by
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  have hfl : b * 2 ^ j ≤ r0 := by rw [hb]; exact Nat.div_mul_le_self r0 _
  have hbr : b ≤ r0 := by rw [hb]; exact Nat.div_le_self _ _
  by_cases hodd : b % 2 = 1
  · simp only [if_pos hodd]
    have hab := hle hodd
    have hmul : a2 * 2 ^ j ≤ (b - 1) * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
    have hbm : (b - 1) * 2 ^ j + 2 ^ j = b * 2 ^ j := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    have hanc := fun x hx1 hx2 => anc_leaf_iff nn h (b - 1) j x hN (by omega) (by omega) hx1 hx2
    have hB := ai_block nn h l0 r0 (b - 1) j ((b - 1) * 2 ^ j) A f (cvj l0 r0 j a2 b) node lz hN hl hr (by omega)
      (by omega) (by omega) (by omega)
      (fun x hx1 hx2 => by rw [hanc x hx1 hx2, Nat.add_mul, Nat.one_mul])
      (fun d hd1 hA' hne => anc_right_mem nn h l0 r0 j hN hr (by rw [← hb]; exact hodd) d hd1 (by rw [← hb]; exact hA') (by rw [← hb]; exact hne))
      hf hAV hA hI
    refine ai_congr nn A f _ _ _ _ _ (fun x => ?_) hB
    unfold cvj Proofs.SegTreeMath.pr1
    rw [if_pos hodd]
    omega
  · simp only [if_neg hodd]
    refine ai_congr nn A f _ _ _ _ _ (fun x => ?_) hI
    unfold Proofs.SegTreeMath.pr1
    rw [if_neg hodd]

theorem cvj_shift (l0 r0 j a b : Nat) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    ∀ x, cvj l0 r0 j a b x ↔ cvj l0 r0 (j + 1) (a / 2) (b / 2) x := by
  intro x
  obtain ⟨u, rfl⟩ : ∃ u, a = 2 * u := ⟨a / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, b = 2 * v := ⟨b / 2, by omega⟩
  have e1 : 2 * u * 2 ^ j = u * 2 ^ (j + 1) := by
    calc 2 * u * 2 ^ j = u * 2 * 2 ^ j := by rw [Nat.mul_comm 2 u]
      _ = u * (2 * 2 ^ j) := Nat.mul_assoc ..
      _ = u * 2 ^ (j + 1) := by rw [Nat.pow_succ']
  have e2 : 2 * v * 2 ^ j = v * 2 ^ (j + 1) := by
    calc 2 * v * 2 ^ j = v * 2 * 2 ^ j := by rw [Nat.mul_comm 2 v]
      _ = v * (2 * 2 ^ j) := Nat.mul_assoc ..
      _ = v * 2 ^ (j + 1) := by rw [Nat.pow_succ']
  have e3 : 2 * u / 2 = u := by omega
  have e4 : 2 * v / 2 = v := by omega
  unfold cvj
  rw [e1, e2, e3, e4]

/-- One round of the `all_apply` loop: nodes and pending actions. -/
def stepN (nn : Nat) (f : Int) (a b : Nat) (node : List Int) : List Int :=
  let n1 := if a % 2 = 1 then applyNode chminMon node a f else node
  if b % 2 = 1 then applyNode chminMon n1 (b - 1) f else n1

def stepZ (nn : Nat) (f : Int) (a b : Nat) (lz : List Int) : List Int :=
  let z1 := if a % 2 = 1 then alz chminMon nn lz a f else lz
  if b % 2 = 1 then alz chminMon nn z1 (b - 1) f else z1

theorem ai_iter (nn h l0 r0 j a b : Nat) (A : List Int) (f : Int) (node lz : List Int)
    (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn)
    (ha : a = ceilDiv l0 (2 ^ j)) (hb : b = r0 / 2 ^ j) (hab : a < b)
    (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A) (hA : A.length = nn)
    (hI : AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j a b) node lz) :
    AI nn A f (S2 h l0 r0 0) (cvj l0 r0 (j + 1) (Proofs.SegTreeMath.pl1 a / 2) (Proofs.SegTreeMath.pr1 b / 2))
      (stepN nn f a b node) (stepZ nn f a b lz) := by
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  have hce := ceil_ge l0 (2 ^ j) hq
  rw [← ha] at hce
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have ha1 : 1 ≤ a := by rw [ha]; exact ceil_pos l0 _ (by omega) hq
  have h1 := ai_left nn h l0 r0 j a b A f node lz hN hl hr ha hb hab hf hAV hA hI
  have hp1 : 1 ≤ Proofs.SegTreeMath.pl1 a := by unfold Proofs.SegTreeMath.pl1; split <;> omega
  have hp2 : l0 ≤ Proofs.SegTreeMath.pl1 a * 2 ^ j := by
    have : a * 2 ^ j ≤ Proofs.SegTreeMath.pl1 a * 2 ^ j :=
      Nat.mul_le_mul_right _ (by unfold Proofs.SegTreeMath.pl1; split <;> omega)
    omega
  have h2 := ai_right nn h l0 r0 j (Proofs.SegTreeMath.pl1 a) b A f _ _ hN hl hr hb hp1 hp2
    (fun hodd => by unfold Proofs.SegTreeMath.pl1; split <;> omega) hf hAV hA h1
  refine ai_congr nn A f _ _ _ _ _ (cvj_shift l0 r0 j _ _ ?_ ?_) h2
  · unfold Proofs.SegTreeMath.pl1; split <;> omega
  · unfold Proofs.SegTreeMath.pr1; split <;> omega

theorem ai_init (nn h l0 r0 : Nat) (A : List Int) (f : Int) (node lz : List Int)
    (hR : Rep chminMon nn A node lz) (hF : LzFid chminMon (S2 h l0 r0 0) lz) :
    AI nn A f (S2 h l0 r0 0) (cvj l0 r0 0 l0 r0) node lz := by
  obtain ⟨hn, hl, hA, hV, hFa, hAV, hE⟩ := hR
  refine ⟨hn, hl, hV, hFa, hF, ?_⟩
  refine ext_weaken chminMon _ nn _ _ (fun _ => False) _ (fun d _ _ hb => hb.elim) ?_
  refine ext_congr chminMon _ _ nn _ _ _ (fun x _ _ => ?_) hE
  unfold lfCv cvj
  rw [if_neg]
  omega

/-- When the loop has met (`a = b`), the covered leaves are exactly `[l0, r0)`. -/
theorem ai_final (nn h l0 r0 j a : Nat) (A : List Int) (f : Int) (node lz : List Int)
    (ha : a = ceilDiv l0 (2 ^ j)) (hb : a = r0 / 2 ^ j)
    (hI : AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j a a) node lz) :
    AI nn A f (S2 h l0 r0 0) (fun x => l0 ≤ x ∧ x < r0) node lz := by
  have hq : 0 < 2 ^ j := Nat.two_pow_pos j
  have hce := ceil_ge l0 (2 ^ j) hq
  rw [← ha] at hce
  have hfl : a * 2 ^ j ≤ r0 := by rw [hb]; exact Nat.div_mul_le_self r0 _
  refine ai_congr nn A f _ _ _ _ _ (fun x => ?_) hI
  unfold cvj
  omega

/-! ### The final bottom-up `update` loop -/

/-- The nodes on the two boundary paths at the levels above `i` have the right bound. -/
theorem S2_lt_tight (nn h l0 r0 i : Nat) (hN : nn = 2 ^ h) (hl : l0 ≤ 2 * nn) (hr : r0 ≤ 2 * nn) (hih : i ≤ h) :
    ∀ s, S2 h l0 r0 i s → s < 2 ^ (h - i) := by
  rintro s ⟨t, ht1, ht2, (⟨hm, rfl⟩ | ⟨hm, rfl⟩)⟩
  · have hlt : l0 < 2 ^ (h + 1) := by
      have hne : l0 ≠ 2 * nn := by
        intro e
        apply hm
        rw [e, hN, ← Nat.pow_succ']
        exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
      rw [Nat.pow_succ']; omega
    have := pow_hi h t l0 (by omega) hlt
    have h2 : 2 ^ (h + 1 - t) ≤ 2 ^ (h - i) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hlt : r0 - 1 < 2 ^ (h + 1) := by
      have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
      have hne : r0 - 1 < 2 * nn := by omega
      rw [Nat.pow_succ']; omega
    have := pow_hi h t (r0 - 1) (by omega) hlt
    have h2 : 2 ^ (h + 1 - t) ≤ 2 ^ (h - i) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

def UI (nn : Nat) (A' : List Int) (S B : Nat → Prop) (node lz : List Int) : Prop :=
  node.length = 2 * nn ∧ lz.length = nn ∧ AllV chminMon.toMon node ∧ AllF chminMon lz ∧ LzFid chminMon S lz ∧
    Ext chminMon (lfA chminMon A' nn) nn node lz B

theorem ui_weaken (nn : Nat) (A' : List Int) (S B1 B2 : Nat → Prop) (node lz : List Int)
    (h : ∀ d, B1 d → B2 d) (hU : UI nn A' S B1 node lz) : UI nn A' S B2 node lz := by
  obtain ⟨hn, hl, hV, hF, hS, hE⟩ := hU
  exact ⟨hn, hl, hV, hF, hS, ext_weaken chminMon _ nn _ _ _ _ (fun d _ _ hb => h d hb) hE⟩

/-- Optionally recompute the node `k` from its children. -/
def cu (c : Prop) [Decidable c] (node : List Int) (k : Nat) : List Int := if c then updNode chminMon node k else node

theorem ui_cu (nn : Nat) (A' : List Int) (S B : Nat → Prop) (node lz : List Int) (c : Prop) [Decidable c] (k : Nat)
    (hc : c → 1 ≤ k ∧ k < nn ∧ S k ∧ ¬ B (2 * k) ∧ ¬ B (2 * k + 1)) (hU : UI nn A' S B node lz) :
    UI nn A' S (fun d => B d ∧ ¬ (c ∧ d = k)) (cu c node k) lz := by
  by_cases h : c
  · obtain ⟨hk1, hk2, hk, hB1, hB2⟩ := hc h
    obtain ⟨hn, hl, hV, hF, hS, hE⟩ := hU
    unfold cu
    rw [if_pos h]
    refine ⟨by unfold updNode; simp [hn], hl, allV_updNode chminMon node hV k (by omega), hF, hS, ?_⟩
    have := ext_update chminMon (lfA chminMon A' nn) nn node lz B k hk1 hk2 hl hn hV hF (hS k hk) hB1 hB2 hE
    exact ext_weaken chminMon _ nn _ _ _ _ (fun d _ _ ⟨hb, hne⟩ => ⟨hb, fun ⟨_, e⟩ => hne e⟩) this
  · unfold cu
    rw [if_neg h]
    exact ui_weaken nn A' S B _ node lz (fun d hb => ⟨hb, fun ⟨hc', _⟩ => h hc'⟩) hU

theorem ui_step (nn h l0 r0 i : Nat) (A' : List Int) (node lz : List Int)
    (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hi : i + 1 ≤ h)
    (hU : UI nn A' (S2 h l0 r0 0) (S2 h l0 r0 i) node lz) :
    UI nn A' (S2 h l0 r0 0) (S2 h l0 r0 (i + 1))
      (cu (r0 % 2 ^ (i + 1) ≠ 0) (cu (l0 % 2 ^ (i + 1) ≠ 0) node (l0 / 2 ^ (i + 1))) ((r0 - 1) / 2 ^ (i + 1))) lz := by
  have hnn : 0 < nn := by rw [hN]; exact Nat.two_pow_pos h
  have hSlt := S2_lt_tight nn h l0 r0 i hN hl.2 hr.2 (by omega)
  have hpowi : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hsmall : 2 ^ (h - (i + 1)) < nn := by
    rw [hN]
    have : 2 ^ (h - (i + 1) + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ'] at this
    have := Nat.two_pow_pos (h - (i + 1))
    omega
  -- the left node
  have hS1 := ui_cu nn A' (S2 h l0 r0 0) (S2 h l0 r0 i) node lz (l0 % 2 ^ (i + 1) ≠ 0) (l0 / 2 ^ (i + 1))
    (fun hc => by
      have hb := left_bounds nn h (i + 1) l0 hN (by omega) hi hl hc
      refine ⟨by have := Nat.two_pow_pos (h - (i + 1)); omega, ?_, ⟨i + 1, by omega, hi, Or.inl ⟨hc, rfl⟩⟩, ?_, ?_⟩
      · have : l0 < 2 ^ (h + 1) := by
          have hne : l0 ≠ 2 * nn := by
            intro e; apply hc; rw [e, hN, ← Nat.pow_succ']
            exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
          rw [Nat.pow_succ']; omega
        have h3 := pow_hi h (i + 1) l0 (by omega) this
        have h4 : 2 ^ (h + 1 - (i + 1)) = 2 ^ (h - i) := by congr 1; omega
        rw [h4] at h3
        have h5 : 2 ^ (h - i) ≤ nn := by rw [hN]; exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      · intro hB; have := hSlt _ hB; omega
      · intro hB; have := hSlt _ hB; omega) hU
  -- the right node
  have hS2 := ui_cu nn A' (S2 h l0 r0 0) _ (cu (l0 % 2 ^ (i + 1) ≠ 0) node (l0 / 2 ^ (i + 1))) lz
    (r0 % 2 ^ (i + 1) ≠ 0) ((r0 - 1) / 2 ^ (i + 1))
    (fun hc => by
      have hb := right_bounds nn h (i + 1) r0 hN (by omega) hi hr hc
      refine ⟨by have := Nat.two_pow_pos (h - (i + 1)); omega, ?_, ⟨i + 1, by omega, hi, Or.inr ⟨hc, rfl⟩⟩, ?_, ?_⟩
      · have h3 := pow_hi h (i + 1) (r0 - 1) (by omega) (by rw [Nat.pow_succ']; omega)
        have h4 : 2 ^ (h + 1 - (i + 1)) = 2 ^ (h - i) := by congr 1; omega
        rw [h4] at h3
        have h5 : 2 ^ (h - i) ≤ nn := by rw [hN]; exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      · rintro ⟨hB, _⟩; have := hSlt _ hB; omega
      · rintro ⟨hB, _⟩; have := hSlt _ hB; omega) hS1
  refine ui_weaken nn A' _ _ _ _ _ ?_ hS2
  rintro s ⟨⟨hs, hn1⟩, hn2⟩
  obtain ⟨t, ht1, ht2, (⟨hm, rfl⟩ | ⟨hm, rfl⟩)⟩ := hs
  · by_cases hti : t = i + 1
    · subst hti; exact absurd ⟨hm, rfl⟩ hn1
    · exact ⟨t, by omega, ht2, Or.inl ⟨hm, rfl⟩⟩
  · by_cases hti : t = i + 1
    · subst hti; exact absurd ⟨hm, rfl⟩ hn2
    · exact ⟨t, by omega, ht2, Or.inr ⟨hm, rfl⟩⟩

end Proofs.LazySegApplyLoop
