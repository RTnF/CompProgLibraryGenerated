import Proofs.Cpp.Gen.TreeFullDp
import Proofs.Cpp.Lib.Basic
import Proofs.TreeDpMath

/-! # `tree_full_dp` (library/tree/tree_full_dp.hpp)

Rerooting DP for any policy `P` whose static members compute a commutative monoid `M` (`Proofs.TreeDpAlg.CM`)
with one tick each. The bottom-up pass keeps `P1` (inner loops `I2`, `I3`), the top-down pass `P2` (inner loop
`I5`); `final_facts` turns them into the premises of `dp_deriv`, `up_deriv` and `full_deriv` of
`Proofs.TreeDpMath`. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.TreeDpAlg Proofs.TreeDpSpec Proofs.TreeDpMath

namespace Proofs.Cpp.TreeFullDp

/-- The C++ arrays as the lists of `Proofs.TreeDpMath`. -/
def NL (a : Array Int) : List Nat := a.toList.map Int.toNat

theorem NL_getD (a : Array Int) (i : Nat) : (NL a).getD i 0 = a[i]!.toNat := by
  unfold NL
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]; simp [h]
  · rw [getElem!_neg a i h]; simp [h]

theorem L_getD (a : Array Int) (i : Nat) : a.toList.getD i 0 = a[i]! := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]; simp [h]
  · rw [getElem!_neg a i h]; simp [h]

/-- `filter (· < p)` of an interval of naturals. -/
theorem range'_filter_lt (a L p : Nat) (h1 : a ≤ p) (h2 : p ≤ a + L) :
    (List.range' a L).filter (fun q => decide (q < p)) = List.range' a (p - a) := by
  induction L generalizing a with
  | zero => have : p = a := by omega
            subst this; simp
  | succ L ih =>
    rw [List.range'_succ, List.filter_cons]
    by_cases hp : a < p
    · simp only [hp, decide_true, ite_true]
      rw [ih (a + 1) (by omega) (by omega)]
      have : p - a = (p - (a + 1)) + 1 := by omega
      rw [this, List.range'_succ]
    · have : p = a := by omega
      subst this
      simp only [Nat.lt_irrefl, decide_false, Nat.sub_self]
      simp only [List.range'_zero]
      apply List.filter_eq_nil_iff.mpr
      intro x hx; simp [List.mem_range'] at hx ⊢; omega

theorem range'_filter_gt (a L p : Nat) (h1 : a ≤ p) (h2 : p < a + L) :
    (List.range' a L).filter (fun q => decide (p < q)) = List.range' (p + 1) (a + L - p - 1) := by
  induction L generalizing a with
  | zero => omega
  | succ L ih =>
    rw [List.range'_succ, List.filter_cons]
    by_cases hp : p < a
    · omega
    · simp only [hp, decide_false]
      by_cases he : p = a
      · subst he
        simp only [decide_false, Bool.false_eq_true, ite_false]
        rw [List.filter_eq_self.mpr (fun x hx => by simp [List.mem_range'] at hx; simp; omega)]
        congr 1; omega
      · simp only [decide_false, Bool.false_eq_true, ite_false]
        rw [ih (a + 1) (by omega) (by omega)]; congr 1; omega


section
variable (head target parent : Array Int)

/-- The arcs of `v` are `[A v, B v)`. -/
def A (v : Nat) : Nat := head[v]!.toNat
def B (v : Nat) : Nat := head[v + 1]!.toNat
/-- Arc `q` leads to a child of `v`. -/
def kid (v q : Nat) : Bool := decide (parent[target[q]!.toNat]! = (v : Int))
/-- The DP value at the head of arc `q`. -/
def dpv (dp : Array Int) (q : Nat) : Int := dp[target[q]!.toNat]!

/-- The children's values through the arcs in `[a, a + len)`. -/
def KS (dp : Array Int) (v a len : Nat) : List Int :=
  ((List.range' a len).filter (kid target parent v)).map (dpv target dp)

end

theorem KS_succ (target parent dp : Array Int) (v a len : Nat) :
    KS target parent dp v a (len + 1) =
      KS target parent dp v a len ++ (if kid target parent v (a + len) then [dpv target dp (a + len)] else []) := by
  unfold KS
  rw [List.range'_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  have e : a + 1 * len = a + len := by omega
  rw [e]; split <;> simp_all

theorem fold_snoc (M : CM) (xs : List Int) (x : Int) : fold M (xs ++ [x]) = M.op (fold M xs) x := by
  simp [fold, List.foldl_append]

/-- The first inner loop of the bottom-up pass after the arcs `[a, a + j)` of `v`. -/
def I2 (target parent dp pre0 : Array Int) (M : CM) (v a j : Nat) (pre : Array Int) (acc : Int) : Prop :=
  pre.size = pre0.size ∧ acc = fold M (KS target parent dp v a j) ∧
    (∀ q, a ≤ q → q < a + j → kid target parent v q = true → pre[q]! = fold M (KS target parent dp v a (q - a))) ∧
    (∀ q, ¬(a ≤ q ∧ q < a + j ∧ kid target parent v q = true) → pre[q]! = pre0[q]!)

theorem I2_step (target parent dp pre0 : Array Int) (M : CM) (v a j : Nat) (pre : Array Int) (acc : Int)
    (H : I2 target parent dp pre0 M v a j pre acc) (hp : a + j < pre0.size) :
    (if parent[target[a + j]!.toNat]! = (v : Int) then
      I2 target parent dp pre0 M v a (j + 1) (set pre ((a + j : Nat) : Int) acc)
        (M.op acc dp[target[a + j]!.toNat]!)
    else I2 target parent dp pre0 M v a (j + 1) pre acc) := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  split
  · rename_i hk
    have hkid : kid target parent v (a + j) = true := by simp [kid, hk]
    have hg : ∀ q, (set pre ((a + j : Nat) : Int) acc)[q]! = if q = a + j then acc else pre[q]! := by
      intro q; rw [getElemBang_set _ _ _ _ (by simp; omega)]
      have e : ((a : Int) + (j : Int)).toNat = a + j := by omega
      simp [e]
    refine ⟨by simp [h1], ?_, fun q hq1 hq2 hk' => ?_, fun q hq => ?_⟩
    · rw [KS_succ, if_pos hkid, fold_snoc, h2]; rfl
    · rw [hg]
      split
      · rename_i he; subst he; rw [h2]; congr 2; omega
      · exact h3 q hq1 (by omega) hk'
    · rw [hg, if_neg (fun (he : q = a + j) => hq ⟨by omega, by omega, he ▸ hkid⟩)]
      exact h4 q (fun ⟨x1, x2, x3⟩ => hq ⟨x1, by omega, x3⟩)
  · rename_i hk
    have hkid : kid target parent v (a + j) = false := by simp [kid, hk]
    refine ⟨h1, ?_, fun q hq1 hq2 hk' => ?_, fun q hq => ?_⟩
    · rw [KS_succ, hkid]; simpa using h2
    · rcases Nat.lt_succ_iff_lt_or_eq.mp (show q < a + j + 1 by omega) with h | h
      · exact h3 q hq1 h hk'
      · subst h; rw [hkid] at hk'; exact absurd hk' (by simp)
    · exact h4 q (fun ⟨x1, x2, x3⟩ => hq ⟨x1, by omega, x3⟩)

theorem KS_cons (target parent dp : Array Int) (v p len : Nat) :
    KS target parent dp v p (len + 1) =
      (if kid target parent v p then [dpv target dp p] else []) ++ KS target parent dp v (p + 1) len := by
  unfold KS
  rw [List.range'_succ, List.filter_cons]
  split <;> simp_all

theorem KS_V (target parent dp : Array Int) (M : CM) (n : Nat) (hV : ∀ x, x < n → M.V dp[x]!)
    (ht : ∀ q, q < target.size → target[q]!.toNat < n) (v a len : Nat) (hlen : a + len ≤ target.size) :
    ∀ y ∈ KS target parent dp v a len, M.V y := by
  intro y hy
  unfold KS at hy
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  have hq' := (List.mem_filter.mp hq).1
  simp [List.mem_range'] at hq'
  exact hV _ (ht q (by omega))

/-- The second inner loop (arcs in decreasing order) after the arcs `[b - j, b)` of `v`. -/
def I3 (target parent dp suf0 : Array Int) (M : CM) (v b j : Nat) (suf : Array Int) (back : Int) : Prop :=
  suf.size = suf0.size ∧ back = fold M (KS target parent dp v (b - j) j) ∧
    (∀ q, b - j ≤ q → q < b → kid target parent v q = true →
      suf[q]! = fold M (KS target parent dp v (q + 1) (b - q - 1))) ∧
    (∀ q, ¬(b - j ≤ q ∧ q < b ∧ kid target parent v q = true) → suf[q]! = suf0[q]!)

theorem I3_step (target parent dp suf0 : Array Int) (M : CM) (n : Nat) (hV : ∀ x, x < n → M.V dp[x]!)
    (ht : ∀ q, q < target.size → target[q]!.toNat < n) (v b j : Nat) (suf : Array Int) (back : Int)
    (H : I3 target parent dp suf0 M v b j suf back) (hj : j < b) (hb : b ≤ target.size) (hs : b ≤ suf0.size) :
    (if parent[target[b - 1 - j]!.toNat]! = (v : Int) then
      I3 target parent dp suf0 M v b (j + 1) (set suf ((b - 1 - j : Nat) : Int) back)
        (M.op back dp[target[b - 1 - j]!.toNat]!)
    else I3 target parent dp suf0 M v b (j + 1) suf back) := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  have hp : b - (j + 1) = b - 1 - j := by omega
  have hks : KS target parent dp v (b - (j + 1)) (j + 1) =
      (if kid target parent v (b - 1 - j) then [dpv target dp (b - 1 - j)] else []) ++
        KS target parent dp v (b - j) j := by
    rw [hp, KS_cons]; congr 2; omega
  have hVks := KS_V target parent dp M n hV ht v (b - j) j (by omega)
  split
  · rename_i hk
    have hkid : kid target parent v (b - 1 - j) = true := by simp [kid, hk]
    have hg : ∀ q, (set suf ((b - 1 - j : Nat) : Int) back)[q]! = if q = b - 1 - j then back else suf[q]! := by
      intro q; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
    have hVx : M.V (dpv target dp (b - 1 - j)) := hV _ (ht _ (by omega))
    refine ⟨by simp [h1], ?_, fun q hq1 hq2 hk' => ?_, fun q hq => ?_⟩
    · rw [hks, if_pos hkid, List.singleton_append, fold_cons M _ _ hVx hVks, h2,
        M.comm _ _ hVx (fold_V M _ hVks)]
      rfl
    · rw [hg]
      split
      · rename_i he; subst he; rw [h2]; congr 2 <;> omega
      · exact h3 q (by omega) hq2 hk'
    · rw [hg, if_neg (fun (he : q = b - 1 - j) => hq ⟨by omega, by omega, he ▸ hkid⟩)]
      exact h4 q (fun ⟨x1, x2, x3⟩ => hq ⟨by omega, x2, x3⟩)
  · rename_i hk
    have hkid : kid target parent v (b - 1 - j) = false := by simp [kid, hk]
    refine ⟨h1, ?_, fun q hq1 hq2 hk' => ?_, fun q hq => ?_⟩
    · rw [hks, hkid]; simpa using h2
    · by_cases he : q = b - 1 - j
      · subst he; rw [hkid] at hk'; exact absurd hk' (by simp)
      · exact h3 q (by omega) hq2 hk'
    · exact h4 q (fun ⟨x1, x2, x3⟩ => hq ⟨by omega, x2, x3⟩)

/-- The fold over all the children of `v`. -/
def FK (head target parent dp : Array Int) (M : CM) (v : Nat) : Int :=
  fold M (KS target parent dp v (A head v) (B head v - A head v))

theorem KS_congr (target parent dp dp' : Array Int) (v a len : Nat)
    (h : ∀ q, a ≤ q → q < a + len → kid target parent v q = true → dp'[target[q]!.toNat]! = dp[target[q]!.toNat]!) :
    KS target parent dp' v a len = KS target parent dp v a len := by
  unfold KS
  apply List.map_congr_left
  intro q hq
  have := List.mem_filter.mp hq
  simp [List.mem_range'] at this
  exact h q (by omega) (by omega) this.2

/-- The bottom-up pass after the vertices of position at least `m` (`pos` is the position in `ord`). -/
def P1 (head target parent : Array Int) (M : CM) (n : Nat) (pos : Nat → Nat) (dp pre suf full : Array Int)
    (m : Nat) : Prop :=
  (∀ x, x < n → M.V dp[x]!) ∧
  ∀ u, u < n → m ≤ pos u →
    dp[u]! = M.su (FK head target parent dp M u) ∧ full[u]! = FK head target parent dp M u ∧
    ∀ q, A head u ≤ q → q < B head u → kid target parent u q = true →
      pre[q]! = fold M (KS target parent dp u (A head u) (q - A head u)) ∧
      suf[q]! = fold M (KS target parent dp u (q + 1) (B head u - q - 1))

theorem P1_step (head target parent : Array Int) (M : CM) (n : Nat) (pos : Nat → Nat)
    (dp pre suf full pre' suf' : Array Int) (acc back : Int) (m v : Nat)
    (H : P1 head target parent M n pos dp pre suf full m) (hv : v < n) (hpv : pos v + 1 = m)
    (hdps : dp.size = n) (hfs : full.size = n)
    (ht : ∀ q, q < target.size → target[q]!.toNat < n) (hBt : B head v ≤ target.size) (hAB : A head v ≤ B head v)
    (hABu : ∀ u, u < n → A head u ≤ B head u) (hinj : ∀ u, u < n → u ≠ v → pos u ≠ pos v)
    (F1 : ∀ q, A head v ≤ q → q < B head v → kid target parent v q = true → m ≤ pos (target[q]!.toNat))
    (F2 : ∀ u, u < n → m ≤ pos u → ∀ q, A head u ≤ q → q < B head u → kid target parent u q = true →
      target[q]!.toNat ≠ v)
    (F3 : ∀ u, u < n → u ≠ v → ∀ q, A head u ≤ q → q < B head u → ¬(A head v ≤ q ∧ q < B head v))
    (H2 : I2 target parent dp pre M v (A head v) (B head v - A head v) pre' acc)
    (H3 : I3 target parent (set dp (v : Int) (M.su acc)) suf M v (B head v) (B head v - A head v) suf' back) :
    P1 head target parent M n pos (set dp (v : Int) (M.su acc)) pre' suf' (set full (v : Int) acc) (m - 1) := by
  obtain ⟨hV, hP⟩ := H
  obtain ⟨a1, a2, a3, a4⟩ := H2
  obtain ⟨b1, b2, b3, b4⟩ := H3
  have gdp : ∀ x, (set dp (v : Int) (M.su acc))[x]! = if x = v then M.su acc else dp[x]! := by
    intro x; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
  have gfull : ∀ x, (set full (v : Int) acc)[x]! = if x = v then acc else full[x]! := by
    intro x; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
  -- the children of `v` are processed, so their values are final
  have kidsv : ∀ q, A head v ≤ q → q < A head v + (B head v - A head v) → kid target parent v q = true →
      (set dp (v : Int) (M.su acc))[target[q]!.toNat]! = dp[target[q]!.toNat]! := by
    intro q h1 h2 hk
    have := F1 q h1 (by omega) hk
    rw [gdp, if_neg (fun he => by rw [he] at this; omega)]
  have hKSv : ∀ a len, A head v ≤ a → a + len ≤ B head v →
      KS target parent (set dp (v : Int) (M.su acc)) v a len = KS target parent dp v a len := by
    intro a len h1 h2
    exact KS_congr _ _ _ _ _ _ _ (fun q q1 q2 hk => kidsv q (by omega) (by omega) hk)
  have hacc : acc = FK head target parent dp M v := by rw [a2]; rfl
  have hVacc : M.V acc := by
    rw [a2]; exact fold_V M _ (KS_V target parent dp M n hV ht v _ _ (by omega))
  refine ⟨fun x hx => ?_, fun u hu hmu => ?_⟩
  · rw [gdp]; split
    · exact M.suV _ hVacc
    · exact hV x hx
  · by_cases huv : u = v
    · subst huv
      have hFK : FK head target parent (set dp (u : Int) (M.su acc)) M u = FK head target parent dp M u := by
        unfold FK; rw [hKSv _ _ (Nat.le_refl _) (by omega)]
      refine ⟨by rw [gdp, if_pos rfl, hFK, hacc], by rw [gfull, if_pos rfl, hFK, hacc], fun q hq1 hq2 hk => ?_⟩
      refine ⟨?_, ?_⟩
      · rw [a3 q hq1 (by omega) hk, hKSv _ _ (Nat.le_refl _) (by omega)]
      · have e : B head u - (B head u - A head u) = A head u := by omega
        rw [b3 q (by omega) hq2 hk, hKSv _ _ (by omega) (by omega)]
    · have hmu' : m ≤ pos u := by
        rcases Nat.lt_or_ge (pos u) m with h | h
        · exfalso; exact hinj u hu huv (by omega)
        · exact h
      obtain ⟨c1, c2, c3⟩ := hP u hu hmu'
      have kidsu : ∀ q, A head u ≤ q → q < B head u → kid target parent u q = true →
          (set dp (v : Int) (M.su acc))[target[q]!.toNat]! = dp[target[q]!.toNat]! := by
        intro q h1 h2 hk; rw [gdp, if_neg (F2 u hu hmu' q h1 h2 hk)]
      have hKSu : ∀ a len, A head u ≤ a → a + len ≤ B head u →
          KS target parent (set dp (v : Int) (M.su acc)) u a len = KS target parent dp u a len := by
        intro a len h1 h2
        exact KS_congr _ _ _ _ _ _ _ (fun q q1 q2 hk => kidsu q (by omega) (by omega) hk)
      have hFK : FK head target parent (set dp (v : Int) (M.su acc)) M u = FK head target parent dp M u := by
        unfold FK; rw [hKSu _ _ (Nat.le_refl _) (by have := hABu u hu; omega)]
      refine ⟨by rw [gdp, if_neg huv, hFK]; exact c1, by rw [gfull, if_neg huv, hFK]; exact c2, fun q hq1 hq2 hk => ?_⟩
      have hd := F3 u hu huv q hq1 hq2
      obtain ⟨d1, d2⟩ := c3 q hq1 hq2 hk
      refine ⟨?_, ?_⟩
      · rw [a4 q (fun ⟨x1, x2, _⟩ => hd ⟨x1, by omega⟩), d1, hKSu _ _ (Nat.le_refl _) (by omega)]
      · rw [b4 q (fun ⟨x1, x2, _⟩ => hd ⟨by omega, x2⟩), d2, hKSu _ _ (by omega) (by omega)]

/-- The value written to `up` at the head of the child arc `q` of `v`. -/
def upv (M : CM) (pre suf : Array Int) (upv0 : Int) (q : Nat) : Int := M.su (M.op (M.op upv0 pre[q]!) suf[q]!)

/-- The inner loop of the top-down pass after the arcs `[a, a + j)` of `v`. -/
def I5 (target parent pre suf up0 : Array Int) (M : CM) (v a j : Nat) (up : Array Int) : Prop :=
  up.size = up0.size ∧
    (∀ q, a ≤ q → q < a + j → kid target parent v q = true → up[target[q]!.toNat]! = upv M pre suf up0[v]! q) ∧
    (∀ x, (∀ q, a ≤ q → q < a + j → kid target parent v q = true → target[q]!.toNat ≠ x) → up[x]! = up0[x]!)

theorem I5_step (target parent pre suf up0 : Array Int) (M : CM) (n v a j : Nat) (up : Array Int)
    (H : I5 target parent pre suf up0 M v a j up) (hs : up0.size = n)
    (ht : ∀ q, a ≤ q → q ≤ a + j → kid target parent v q = true → target[q]!.toNat < n ∧ target[q]!.toNat ≠ v)
    (hd : ∀ q, a ≤ q → q < a + j → kid target parent v q = true → kid target parent v (a + j) = true →
      target[q]!.toNat ≠ target[a + j]!.toNat) :
    (if parent[target[a + j]!.toNat]! = (v : Int) then
      I5 target parent pre suf up0 M v a (j + 1)
        (set up (target[a + j]!.toNat : Int) (M.su (M.op (M.op up[v]! pre[a + j]!) suf[a + j]!)))
    else I5 target parent pre suf up0 M v a (j + 1) up) := by
  obtain ⟨h1, h2, h3⟩ := H
  have huv : up[v]! = up0[v]! := h3 v (fun q q1 q2 hk' => (ht q q1 (by omega) hk').2)
  split
  · rename_i hk
    have hkid : kid target parent v (a + j) = true := by simp [kid, hk]
    obtain ⟨t1, t2⟩ := ht (a + j) (by omega) (Nat.le_refl _) hkid
    have hg : ∀ x, (set up (target[a + j]!.toNat : Int) (M.su (M.op (M.op up[v]! pre[a + j]!) suf[a + j]!)))[x]! =
        if x = target[a + j]!.toNat then M.su (M.op (M.op up[v]! pre[a + j]!) suf[a + j]!) else up[x]! := by
      intro x; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp only [Int.toNat_natCast]
    refine ⟨by simp [h1], fun q q1 q2 hk' => ?_, fun x hx => ?_⟩
    · rw [hg]
      by_cases he : q = a + j
      · subst he; rw [if_pos rfl, huv]; rfl
      · rw [if_neg (hd q q1 (by omega) hk' hkid)]; exact h2 q q1 (by omega) hk'
    · rw [hg, if_neg (fun he => hx (a + j) (by omega) (by omega) hkid he.symm)]
      exact h3 x (fun q q1 q2 hk' => hx q q1 (by omega) hk')
  · rename_i hk
    have hkid : kid target parent v (a + j) = false := by simp [kid, hk]
    refine ⟨h1, fun q q1 q2 hk' => ?_, fun x hx => h3 x (fun q q1 q2 hk' => hx q q1 (by omega) hk')⟩
    by_cases he : q = a + j
    · subst he; rw [hkid] at hk'; exact absurd hk' (by simp)
    · exact h2 q q1 (by omega) hk'

/-- The top-down pass after the vertices of position below `m`. -/
def P2 (head target parent dp pre suf : Array Int) (M : CM) (n root : Nat) (pos : Nat → Nat) (up full : Array Int)
    (m : Nat) : Prop :=
  up[root]! = M.e ∧ (∀ x, x < n → M.V up[x]!) ∧
  (∀ u, u < n → pos u < m →
    full[u]! = M.su (M.op up[u]! (FK head target parent dp M u)) ∧
    ∀ q, A head u ≤ q → q < B head u → kid target parent u q = true →
      up[target[q]!.toNat]! = upv M pre suf up[u]! q) ∧
  (∀ u, u < n → m ≤ pos u → full[u]! = FK head target parent dp M u)

theorem P2_step (head target parent dp pre suf : Array Int) (M : CM) (n root : Nat) (pos : Nat → Nat)
    (up full up' : Array Int) (m v : Nat) (H : P2 head target parent dp pre suf M n root pos up full m)
    (hv : v < n) (hpv : pos v = m) (hups : up.size = n) (hfs : full.size = n)
    (hinj : ∀ u, u < n → u ≠ v → pos u ≠ pos v)
    (G1 : ∀ q, A head v ≤ q → q < B head v → kid target parent v q = true →
      target[q]!.toNat < n ∧ target[q]!.toNat ≠ v ∧ m < pos (target[q]!.toNat) ∧ target[q]!.toNat ≠ root)
    (hAB : A head v ≤ B head v)
    (hVps : ∀ q, A head v ≤ q → q < B head v → kid target parent v q = true → M.V pre[q]! ∧ M.V suf[q]!)
    (H5 : I5 target parent pre suf up M v (A head v) (B head v - A head v) up') :
    P2 head target parent dp pre suf M n root pos up'
      (set full (v : Int) (M.su (M.op up[v]! full[v]!))) (m + 1) := by
  obtain ⟨p1, p2, p3, p4⟩ := H
  obtain ⟨i1, i2, i3⟩ := H5
  have gfull : ∀ x, (set full (v : Int) (M.su (M.op up[v]! full[v]!)))[x]! =
      if x = v then M.su (M.op up[v]! full[v]!) else full[x]! := by
    intro x; rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp
  -- vertices that are not heads of child arcs of `v` keep their `up`
  have keep : ∀ x, (∀ q, A head v ≤ q → q < B head v → kid target parent v q = true → target[q]!.toNat ≠ x) →
      up'[x]! = up[x]! := fun x hx => i3 x (fun q q1 q2 hk => hx q q1 (by omega) hk)
  have keep_old : ∀ u, u < n → pos u ≤ m → up'[u]! = up[u]! := by
    intro u hu hpu
    exact keep u (fun q q1 q2 hk he => by have := (G1 q q1 q2 hk).2.2.1; rw [he] at this; omega)
  refine ⟨?_, fun x hx => ?_, fun u hu hpu => ?_, fun u hu hpu => ?_⟩
  · rw [keep root (fun q q1 q2 hk => (G1 q q1 q2 hk).2.2.2)]; exact p1
  · by_cases hx' : ∃ q, A head v ≤ q ∧ q < B head v ∧ kid target parent v q = true ∧ target[q]!.toNat = x
    · obtain ⟨q, q1, q2, hk, he⟩ := hx'
      rw [← he, i2 q q1 (by omega) hk]
      exact M.suV _ (M.closed _ _ (M.closed _ _ (p2 v hv) (hVps q q1 q2 hk).1) (hVps q q1 q2 hk).2)
    · rw [keep x (fun q q1 q2 hk he => hx' ⟨q, q1, q2, hk, he⟩)]; exact p2 x hx
  · by_cases huv : u = v
    · subst huv
      refine ⟨?_, fun q q1 q2 hk => ?_⟩
      · rw [gfull, if_pos rfl, keep_old u hu (by omega), p4 u hu (by omega)]
      · rw [i2 q q1 (by omega) hk, keep_old u hu (by omega)]
    · have hlt : pos u < m := by have := hinj u hu huv; omega
      obtain ⟨c1, c2⟩ := p3 u hu hlt
      refine ⟨?_, fun q q1 q2 hk => ?_⟩
      · rw [gfull, if_neg huv, keep_old u hu (by omega)]; exact c1
      · rw [keep_old u hu (by omega), keep (target[q]!.toNat) (fun q' q1' q2' hk' he => by
          simp only [kid, decide_eq_true_eq] at hk hk'
          rw [he] at hk'
          have : (u : Int) = v := by rw [← hk, ← hk']
          omega)]
        exact c2 q q1 q2 hk
  · have huv : u ≠ v := fun h => by subst h; omega
    rw [gfull, if_neg huv]; exact p4 u hu (by omega)

theorem arcs_eq (head : Array Int) (v : Nat) : arcs (NL head) v = List.range' (A head v) (B head v - A head v) := by
  unfold arcs A B; rw [NL_getD, NL_getD]

theorem tgt_eq (target : Array Int) (q : Nat) : tgt (NL target) q = target[q]!.toNat := NL_getD target q

theorem kidArcs_eq (head target parent : Array Int) (v : Nat) :
    kidArcs (NL head) (NL target) parent.toList v =
      (List.range' (A head v) (B head v - A head v)).filter (kid target parent v) := by
  unfold kidArcs
  rw [arcs_eq]
  congr 1
  funext q
  simp only [kid, tgt_eq, L_getD]

theorem kid_facts' (head target parent ord : Array Int) (n root : Nat)
    (T : TS (NL head) (NL target) parent.toList (NL ord) n root) (v : Nat) (hv : v < n) (q : Nat)
    (h1 : A head v ≤ q) (h2 : q < B head v) (hk : kid target parent v q = true) :
    target[q]!.toNat < n ∧ target[q]!.toNat ≠ root ∧ pos (NL ord) v < pos (NL ord) (target[q]!.toNat) := by
  have hm : q ∈ kidArcs (NL head) (NL target) parent.toList v := by
    rw [kidArcs_eq]; exact List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨h1, by omega⟩, hk⟩
  obtain ⟨_, a2, a3, _, _, a6⟩ := T.kid_facts v hv q hm
  rw [tgt_eq] at a2 a3 a6
  exact ⟨a2, a3, a6⟩

theorem pos_inj (ord : Array Int) (n : Nat) (hl : (NL ord).length = n) (hmem : ∀ x, x < n → x ∈ NL ord)
    (u v : Nat) (hu : u < n) (hv : v < n) (h : pos (NL ord) u = pos (NL ord) v) : u = v := by
  have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem u hu))
  have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem v hv))
  unfold pos at h
  simp only [h] at e1
  exact e1.symm.trans e2

theorem B_le_A (head : Array Int) (n : Nat) (hmono : ∀ x, x < n → A head x ≤ B head x) :
    ∀ u v, u < v → v < n → B head u ≤ A head v := by
  intro u v huv hv
  induction v with
  | zero => omega
  | succ v ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp huv with h | h
    · have := ih h (by omega); have := hmono v (by omega); unfold A B at *; omega
    · subst h; unfold A B; simp

theorem arcs_disjoint (head : Array Int) (n : Nat) (hmono : ∀ x, x < n → A head x ≤ B head x)
    (u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) (q : Nat) (h1 : A head u ≤ q) (h2 : q < B head u) :
    ¬(A head v ≤ q ∧ q < B head v) := by
  rintro ⟨h3, h4⟩
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have := B_le_A head n hmono u v h hv; omega
  · have := B_le_A head n hmono v u h hu; omega

theorem KS_mem (target parent dp : Array Int) (v a len : Nat) :
    ((((List.range' a len).filter (kid target parent v)).map (tgt (NL target))).map fun x => dp.toList.getD x 0) =
      KS target parent dp v a len := by
  unfold KS
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp, tgt_eq, L_getD, dpv]

theorem kidT_KS (head target parent dp : Array Int) (v : Nat) :
    (kidT (NL head) (NL target) parent.toList v).map (fun x => dp.toList.getD x 0) =
      KS target parent dp v (A head v) (B head v - A head v) := by
  unfold kidT; rw [kidArcs_eq, KS_mem]

theorem filter_swap (l : List Nat) (f g : Nat → Bool) : (l.filter f).filter g = (l.filter g).filter f := by
  rw [List.filter_filter, List.filter_filter]
  congr 1; funext x; exact Bool.and_comm _ _

theorem kb_KS (head target parent dp : Array Int) (v p : Nat) (h1 : A head v ≤ p) (h2 : p < B head v) :
    (kb (NL head) (NL target) parent.toList v p).map (fun x => dp.toList.getD x 0) =
      KS target parent dp v (A head v) (p - A head v) := by
  unfold kb
  rw [kidArcs_eq, filter_swap, range'_filter_lt _ _ _ h1 (by omega), KS_mem]

theorem ka_KS (head target parent dp : Array Int) (v p : Nat) (h1 : A head v ≤ p) (h2 : p < B head v) :
    (ka (NL head) (NL target) parent.toList v p).map (fun x => dp.toList.getD x 0) =
      KS target parent dp v (p + 1) (B head v - p - 1) := by
  unfold ka
  rw [kidArcs_eq, filter_swap, range'_filter_gt _ _ _ h1 (by omega), KS_mem]
  congr 1; omega

theorem mem_kidArcs (head target parent : Array Int) (v q : Nat)
    (h : q ∈ kidArcs (NL head) (NL target) parent.toList v) :
    A head v ≤ q ∧ q < B head v ∧ kid target parent v q = true := by
  rw [kidArcs_eq] at h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  have := List.mem_range'_1.mp h1
  exact ⟨this.1, by omega, h2⟩

theorem final_facts (head target parent ord dp pre suf full0 up full : Array Int) (M : CM) (n root : Nat)
    (T : TS (NL head) (NL target) parent.toList (NL ord) n root)
    (ht : ∀ q, q < target.size → target[q]!.toNat < n) (hBt : ∀ v, v < n → B head v ≤ target.size)
    (h1 : P1 head target parent M n (pos (NL ord)) dp pre suf full0 0)
    (h2 : P2 head target parent dp pre suf M n root (pos (NL ord)) up full n) :
    (∀ v, v < n → ∃ f, Ef M (NL head) (NL target) f (pp parent.toList n root v) v = some dp[v]!) ∧
    (∀ w, w < n → w ≠ root → ∃ f, Ef M (NL head) (NL target) f w (par parent.toList w) = some up[w]!) ∧
    (∀ v, v < n → ∃ f, Ef M (NL head) (NL target) f n v = some full[v]!) := by
  obtain ⟨hV, hP⟩ := h1
  obtain ⟨u0, hVu, hQ, -⟩ := h2
  have hdp : ∀ v, v < n → dp.toList.getD v 0 =
      M.su (fold M ((kidT (NL head) (NL target) parent.toList v).map fun x => dp.toList.getD x 0)) := by
    intro v hv
    rw [kidT_KS, L_getD]; exact (hP v hv (Nat.zero_le _)).1
  have hVdp : ∀ x, x < n → M.V (dp.toList.getD x 0) := fun x hx => by rw [L_getD]; exact hV x hx
  have hVup : ∀ x, x < n → M.V (up.toList.getD x 0) := fun x hx => by rw [L_getD]; exact hVu x hx
  have hup0 : up.toList.getD root 0 = M.e := by rw [L_getD]; exact u0
  have hpre : ∀ v, v < n → ∀ p ∈ kidArcs (NL head) (NL target) parent.toList v,
      pre.toList.getD p 0 = fold M ((kb (NL head) (NL target) parent.toList v p).map fun x => dp.toList.getD x 0) := by
    intro v hv p hp
    obtain ⟨q1, q2, q3⟩ := mem_kidArcs head target parent v p hp
    rw [kb_KS _ _ _ _ _ _ q1 q2, L_getD]; exact ((hP v hv (Nat.zero_le _)).2.2 p q1 q2 q3).1
  have hsuf : ∀ v, v < n → ∀ p ∈ kidArcs (NL head) (NL target) parent.toList v,
      suf.toList.getD p 0 = fold M ((ka (NL head) (NL target) parent.toList v p).map fun x => dp.toList.getD x 0) := by
    intro v hv p hp
    obtain ⟨q1, q2, q3⟩ := mem_kidArcs head target parent v p hp
    rw [ka_KS _ _ _ _ _ _ q1 q2, L_getD]; exact ((hP v hv (Nat.zero_le _)).2.2 p q1 q2 q3).2
  have hupe : ∀ v, v < n → ∀ p ∈ kidArcs (NL head) (NL target) parent.toList v,
      up.toList.getD (tgt (NL target) p) 0 =
        M.su (M.op (M.op (up.toList.getD v 0) (pre.toList.getD p 0)) (suf.toList.getD p 0)) := by
    intro v hv p hp
    obtain ⟨q1, q2, q3⟩ := mem_kidArcs head target parent v p hp
    rw [tgt_eq, L_getD, L_getD, L_getD, L_getD]
    exact (hQ v hv (T.pos_lt v hv)).2 p q1 q2 q3
  have hderivUp := up_deriv M T dp.toList up.toList pre.toList suf.toList hdp hVdp hVup hup0 hpre hsuf hupe
  have hfull : ∀ v, v < n → full.toList.getD v 0 =
      M.su (M.op (up.toList.getD v 0) (fold M ((kidT (NL head) (NL target) parent.toList v).map
        fun x => dp.toList.getD x 0))) := by
    intro v hv
    rw [kidT_KS, L_getD, L_getD]; exact (hQ v hv (T.pos_lt v hv)).1
  have hD := dp_deriv M T dp.toList hdp
  have hF := full_deriv M T dp.toList up.toList full.toList hdp hVdp hVup hup0 hderivUp hfull
  refine ⟨fun v hv => ?_, fun w hw hr => ?_, fun v hv => ?_⟩
  · rw [← L_getD]; exact hD v hv
  · rw [← L_getD]; exact hderivUp w hw hr
  · rw [← L_getD]; exact hF v hv


theorem rangeDown_cursor {a b cur : Int} {pref suff : List Int} (h : rangeDown a b = pref ++ cur :: suff) :
    cur = b - pref.length ∧ pref.length < (b - a + 1).toNat := by
  have hl : pref.length < (rangeDown a b).length := by rw [h]; simp
  have e := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl pref.length), Nat.sub_self, List.getElem?_cons_zero] at e
  unfold rangeDown at e hl
  simp at hl
  obtain ⟨k, hk, hck⟩ := (by simpa using e : ∃ k, (List.range (b - a + 1).toNat)[pref.length]? = some k ∧ b - ↑k = cur)
  rw [List.getElem?_range (by omega)] at hk
  simp at hk; subst hk
  exact ⟨hck.symm, by omega⟩

/-- The work of the inner loops of `v`: its arcs. -/
def deg (head : Array Int) (v : Nat) : Nat := B head v - A head v

def Q1 (head target parent ord : Array Int) (M : CM) (n : Nat) (t0 j : Nat) (dp pre suf full : Array Int) (c : Nat) :
    Prop :=
  P1 head target parent M n (pos (NL ord)) dp pre suf full (n - j) ∧ dp.size = n ∧ pre.size = target.size ∧
    suf.size = target.size ∧ full.size = n ∧
    c ≤ t0 + 1 + 4 * j + 4 * (((NL ord).drop (n - j)).map (deg head)).sum

def Q4 (head target parent ord dp pre suf : Array Int) (M : CM) (n root : Nat) (s0 j : Nat) (up full : Array Int)
    (c : Nat) : Prop :=
  P2 head target parent dp pre suf M n root (pos (NL ord)) up full j ∧ up.size = n ∧ full.size = n ∧
    c ≤ s0 + 1 + 3 * j + 4 * (((NL ord).take j).map (deg head)).sum

/-- The preconditions on the input arrays (docs/tree_full_dp.md). -/
structure Pre (head target parent ord : Array Int) (n root : Int) : Prop where
  n0 : 0 ≤ n
  hs : head.size = n.toNat + 1
  hhead : ∀ x, x ≤ n.toNat → 0 ≤ head[x]!
  hmono : ∀ x, x < n.toNat → head[x]! ≤ head[x + 1]!
  hlast : head[n.toNat]! ≤ target.size
  htgt : ∀ q, q < target.size → 0 ≤ target[q]! ∧ target[q]! < n
  hord : ∀ k, k < n.toNat → 0 ≤ ord[k]! ∧ ord[k]! < n
  r0 : 0 ≤ root ∧ root < n
  T : TS (NL head) (NL target) parent.toList (NL ord) n.toNat root.toNat

theorem Pre.AB {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (v : Nat) (hv : v < n.toNat) : A head v ≤ B head v := by
  have := P.hmono v hv; have := P.hhead v (by omega); unfold A B; omega

theorem Pre.B_last {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (v : Nat) (hv : v < n.toNat) : B head v ≤ target.size := by
  have key : ∀ d, v + 1 + d ≤ n.toNat → B head v ≤ (head[v + 1 + d]!).toNat := by
    intro d
    induction d with
    | zero => intro _; unfold B; simp
    | succ d ih =>
      intro h
      have := ih (by omega); have := P.hmono (v + 1 + d) (by omega); have := P.hhead (v + 1 + d) (by omega)
      have e : v + 1 + (d + 1) = v + 1 + d + 1 := by omega
      rw [e]; omega
  have := key (n.toNat - v - 1) (by omega)
  have e : v + 1 + (n.toNat - v - 1) = n.toNat := by omega
  rw [e] at this
  have := P.hlast; have := P.hhead n.toNat (Nat.le_refl _); omega

/-- The vertex at position `k` of `ord`. -/
theorem Pre.vtx {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) :
    ord[k]!.toNat < n.toNat ∧ ord[k]! = ((ord[k]!.toNat : Nat) : Int) ∧
      get head ord[k]! = (A head ord[k]!.toNat : Int) ∧ get head (ord[k]! + 1) = (B head ord[k]!.toNat : Int) := by
  have h := P.hord k hk
  have hv : ord[k]!.toNat < n.toNat := by omega
  have h1 := P.hhead _ (show ord[k]!.toNat ≤ n.toNat by omega)
  have h2 := P.hhead (ord[k]!.toNat + 1) (by omega)
  refine ⟨hv, by omega, ?_, ?_⟩
  · simp only [get, A]; omega
  · have e : (ord[k]! + 1).toNat = ord[k]!.toNat + 1 := by omega
    simp only [get, B, e]; omega

theorem outer_cur {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1) :
    cur1.toNat < n.toNat ∧ get ord cur1 = ord[cur1.toNat]! ∧ cur1.toNat + pref1.length + 1 = n.toNat := by
  obtain ⟨e1, l1⟩ := rangeDown_cursor hr1
  have := P.n0
  refine ⟨by omega, rfl, by omega⟩

theorem inner_cur {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) {pref suff : List Int} {cur : Int}
    (hr : range (get head ord[k]!) (get head (ord[k]! + 1)) = pref ++ cur :: suff) :
    cur = ((A head ord[k]!.toNat + pref.length : Nat) : Int) ∧ A head ord[k]!.toNat + pref.length < B head ord[k]!.toNat := by
  obtain ⟨_, _, h3, h4⟩ := P.vtx k hk
  rw [h3, h4] at hr
  have e := range_cursor hr
  have hl := congrArg List.length hr
  simp [range_length] at hl
  refine ⟨by rw [e]; push_cast; ring, by omega⟩

theorem i2_vc {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1)
    {pref suff : List Int} {cur : Int}
    (hr : range (get head (get ord cur1)) (get head (get ord cur1 + 1)) = pref ++ cur :: suff)
    (dp pre0 pre : Array Int) (acc : Int) (hps : pre0.size = target.size)
    (H : I2 target parent dp pre0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) pref.length pre acc) :
    (get parent (get target cur) = get ord cur1 →
      I2 target parent dp pre0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) (pref.length + 1)
        (set pre cur acc) (M.op acc (get dp (get target cur)))) ∧
    (¬get parent (get target cur) = get ord cur1 →
      I2 target parent dp pre0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) (pref.length + 1) pre acc) := by
  obtain ⟨hk, hg, -⟩ := outer_cur P hr1
  rw [hg] at hr ⊢
  obtain ⟨hv, hov, -, -⟩ := P.vtx _ hk
  obtain ⟨hc, hlt⟩ := inner_cur P _ hk hr
  have hB := P.B_last _ hv
  have hstep := I2_step target parent dp pre0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) pref.length
    pre acc H (by omega)
  have gt : get target cur = target[A head ord[cur1.toNat]!.toNat + pref.length]! := by
    simp only [get, hc, Int.toNat_natCast]
  rw [gt]
  have gp : get parent target[A head ord[cur1.toNat]!.toNat + pref.length]! =
      parent[target[A head ord[cur1.toNat]!.toNat + pref.length]!.toNat]! := rfl
  rw [gp]
  conv at hstep => rw [← hov]
  rw [← hc] at hstep
  constructor
  · intro h; rw [if_pos h] at hstep; exact hstep
  · intro h; rw [if_neg h] at hstep; exact hstep

theorem Pre.ht {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) :
    ∀ q, q < target.size → target[q]!.toNat < n.toNat := fun q hq => by have := P.htgt q hq; omega

theorem inner_cur_down {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) {pref suff : List Int} {cur : Int}
    (hr : rangeDown (get head ord[k]!) (get head (ord[k]! + 1) - 1) = pref ++ cur :: suff) :
    cur = ((B head ord[k]!.toNat - 1 - pref.length : Nat) : Int) ∧ pref.length < B head ord[k]!.toNat - A head ord[k]!.toNat := by
  obtain ⟨hv, _, h3, h4⟩ := P.vtx k hk
  rw [h3, h4] at hr
  obtain ⟨e, l⟩ := rangeDown_cursor hr
  have := P.AB _ hv
  refine ⟨by rw [e]; omega, by omega⟩

theorem i3_vc {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1)
    {pref suff : List Int} {cur : Int}
    (hr : rangeDown (get head (get ord cur1)) (get head (get ord cur1 + 1) - 1) = pref ++ cur :: suff)
    (dp suf0 suf : Array Int) (back : Int) (hss : suf0.size = target.size)
    (hVd : ∀ x, x < n.toNat → M.V dp[x]!)
    (H : I3 target parent dp suf0 M ord[cur1.toNat]!.toNat (B head ord[cur1.toNat]!.toNat) pref.length suf back) :
    (get parent (get target cur) = get ord cur1 →
      I3 target parent dp suf0 M ord[cur1.toNat]!.toNat (B head ord[cur1.toNat]!.toNat) (pref.length + 1)
        (set suf cur back) (M.op back (get dp (get target cur)))) ∧
    (¬get parent (get target cur) = get ord cur1 →
      I3 target parent dp suf0 M ord[cur1.toNat]!.toNat (B head ord[cur1.toNat]!.toNat) (pref.length + 1) suf back) := by
  obtain ⟨hk, hg, -⟩ := outer_cur P hr1
  rw [hg] at hr ⊢
  obtain ⟨hv, hov, -, -⟩ := P.vtx _ hk
  obtain ⟨hc, hlt⟩ := inner_cur_down P _ hk hr
  have hB := P.B_last _ hv
  have hstep := I3_step target parent dp suf0 M n.toNat hVd P.ht ord[cur1.toNat]!.toNat
    (B head ord[cur1.toNat]!.toNat) pref.length suf back H (by omega) hB (by omega)
  have gt : get target cur = target[B head ord[cur1.toNat]!.toNat - 1 - pref.length]! := by
    simp only [get, hc, Int.toNat_natCast]
  rw [gt]
  have gp : get parent target[B head ord[cur1.toNat]!.toNat - 1 - pref.length]! =
      parent[target[B head ord[cur1.toNat]!.toNat - 1 - pref.length]!.toNat]! := rfl
  rw [gp]
  conv at hstep => rw [← hov]
  rw [← hc] at hstep
  constructor
  · intro h; rw [if_pos h] at hstep; exact hstep
  · intro h; rw [if_neg h] at hstep; exact hstep

theorem I2_zero (target parent dp pre0 : Array Int) (M : CM) (v a : Nat) : I2 target parent dp pre0 M v a 0 pre0 M.e :=
  ⟨rfl, by simp [KS, fold], fun q h1 h2 => absurd h2 (by omega), fun q _ => rfl⟩

theorem I3_zero (target parent dp suf0 : Array Int) (M : CM) (v b : Nat) : I3 target parent dp suf0 M v b 0 suf0 M.e :=
  ⟨rfl, by simp [KS, fold], fun q h1 h2 => absurd h1 (by omega), fun q _ => rfl⟩

theorem I5_zero (target parent pre suf up0 : Array Int) (M : CM) (v a : Nat) : I5 target parent pre suf up0 M v a 0 up0 :=
  ⟨rfl, fun q h1 h2 => absurd h2 (by omega), fun x _ => rfl⟩

theorem V_dp' (target parent dp pre0 pre : Array Int) (M : CM) (n : Nat) (ht : ∀ q, q < target.size → target[q]!.toNat < n)
    (hV : ∀ x, x < n → M.V dp[x]!) (v a j : Nat) (acc : Int) (H : I2 target parent dp pre0 M v a j pre acc)
    (hj : a + j ≤ target.size) (vi : Int) :
    ∀ x, x < n → M.V (set dp vi (M.su acc))[x]! := by
  have hacc : M.V acc := by rw [H.2.1]; exact fold_V M _ (KS_V target parent dp M n hV ht v a j hj)
  intro x hx
  by_cases h : vi.toNat < dp.size
  · rw [getElemBang_set _ _ _ _ h]; split
    · exact M.suV _ hacc
    · exact hV x hx
  · simp only [set, Array.set!, Array.setIfInBounds, h, dite_false]; exact hV x hx

theorem range_len {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1) :
    (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length =
      B head ord[cur1.toNat]!.toNat - A head ord[cur1.toNat]!.toNat ∧
    (rangeDown (get head (get ord cur1)) (get head (get ord cur1 + 1) - 1)).length =
      B head ord[cur1.toNat]!.toNat - A head ord[cur1.toNat]!.toNat := by
  obtain ⟨hk, hg, -⟩ := outer_cur P hr1
  obtain ⟨hv, -, h3, h4⟩ := P.vtx _ hk
  rw [hg, h3, h4]
  simp [range_length, rangeDown]
  omega

theorem i3_vc' {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1)
    {pref suff : List Int} {cur : Int}
    (hr : rangeDown (get head (get ord cur1)) (get head (get ord cur1 + 1) - 1) = pref ++ cur :: suff)
    (dp0 pre0 pre suf0 suf : Array Int) (acc back : Int) (hss : suf0.size = target.size)
    (hV0 : ∀ x, x < n.toNat → M.V dp0[x]!)
    (H2 : I2 target parent dp0 pre0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat)
      (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length pre acc)
    (H : I3 target parent (set dp0 (get ord cur1) (M.su acc)) suf0 M ord[cur1.toNat]!.toNat
      (B head ord[cur1.toNat]!.toNat) pref.length suf back) :
    (get parent (get target cur) = get ord cur1 →
      I3 target parent (set dp0 (get ord cur1) (M.su acc)) suf0 M ord[cur1.toNat]!.toNat (B head ord[cur1.toNat]!.toNat)
        (pref.length + 1) (set suf cur back) (M.op back (get (set dp0 (get ord cur1) (M.su acc)) (get target cur)))) ∧
    (¬get parent (get target cur) = get ord cur1 →
      I3 target parent (set dp0 (get ord cur1) (M.su acc)) suf0 M ord[cur1.toNat]!.toNat
        (B head ord[cur1.toNat]!.toNat) (pref.length + 1) suf back) := by
  obtain ⟨hk, -, -⟩ := outer_cur P hr1
  obtain ⟨hv, -, -, -⟩ := P.vtx _ hk
  rw [(range_len P hr1).1] at H2
  have hVd := V_dp' _ _ _ _ _ M n.toNat P.ht hV0 _ _ _ _ H2 (by have := P.B_last _ hv; have := P.AB _ hv; omega)
    (get ord cur1)
  exact i3_vc P M hr1 hr _ _ _ _ hss hVd H

theorem pos_at {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) : pos (NL ord) (ord[k]!.toNat) = k := by
  have hl := P.T.ordlen
  have hk' : k < (NL ord).length := by omega
  have e : (NL ord)[k] = ord[k]!.toNat := by
    have := NL_getD ord k; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] at this; simpa using this
  rw [← e]; exact P.T.ordnd.idxOf_getElem k hk'

theorem deg_sum_drop {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) :
    (((NL ord).drop k).map (deg head)).sum = deg head ord[k]!.toNat + (((NL ord).drop (k + 1)).map (deg head)).sum := by
  have hl := P.T.ordlen
  have hk' : k < (NL ord).length := by omega
  rw [List.drop_eq_getElem_cons hk']
  have e : (NL ord)[k] = ord[k]!.toNat := by
    have := NL_getD ord k; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] at this; simpa using this
  simp [e]

theorem q1_step {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    (t0 : Nat) {pref1 suff1 : List Int} {cur1 : Int} (hr1 : rangeDown 0 (n - 1) = pref1 ++ cur1 :: suff1)
    (dp pre suf full pre' suf' : Array Int) (acc back : Int) (s2 s1 s : Nat)
    (hQ : Q1 head target parent ord M n.toNat t0 pref1.length dp pre suf full s2)
    (H2 : I2 target parent dp pre M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat)
      (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length pre' acc)
    (hc1 : s1 ≤ s2 + 2 + 2 * (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length)
    (H3 : I3 target parent (set dp (get ord cur1) (M.su acc)) suf M ord[cur1.toNat]!.toNat
      (B head ord[cur1.toNat]!.toNat) (rangeDown (get head (get ord cur1)) (get head (get ord cur1 + 1) - 1)).length
      suf' back)
    (hc : s ≤ s1 + 2 + 2 * (rangeDown (get head (get ord cur1)) (get head (get ord cur1 + 1) - 1)).length) :
    Q1 head target parent ord M n.toNat t0 (pref1.length + 1) (set dp (get ord cur1) (M.su acc)) pre' suf'
      (set full (get ord cur1) acc) s := by
  obtain ⟨hk, hg, hsum⟩ := outer_cur P hr1
  obtain ⟨hv, hov, -, -⟩ := P.vtx _ hk
  obtain ⟨l1, l2⟩ := range_len P hr1
  rw [l1] at H2 hc1
  rw [l2] at H3 hc
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hQ
  have hpos := pos_at P _ hk
  generalize hvN : ord[cur1.toNat]!.toNat = v at *
  rw [hg, hov] at H3 ⊢
  have T := P.T
  have hm : n.toNat - (pref1.length + 1) = cur1.toNat := by omega
  have hm' : n.toNat - pref1.length = cur1.toNat + 1 := by omega
  unfold Q1
  rw [hm]
  rw [hm'] at q1 q6
  have hAB : ∀ u, u < n.toNat → A head u ≤ B head u := P.AB
  refine ⟨?_, by simp [q2], by rw [H2.1, q3], by rw [H3.1, q4], by simp [q5], ?_⟩
  · refine P1_step head target parent M n.toNat (pos (NL ord)) dp pre suf full pre' suf' acc back (cur1.toNat + 1) v
      q1 hv (by rw [hpos]) q2 q5 P.ht (P.B_last v hv) (hAB v hv) hAB
      (fun u hu huv h => huv (pos_inj ord n.toNat T.ordlen T.ordmem u v hu hv h))
      (fun q h1 h2 hk => by have := (kid_facts' head target parent ord _ _ T v hv q h1 h2 hk).2.2; omega)
      (fun u hu hmu q h1 h2 hk he => by
        have := (kid_facts' head target parent ord _ _ T u hu q h1 h2 hk).2.2; rw [he] at this; omega)
      (fun u hu huv q h1 h2 => arcs_disjoint head n.toNat hAB u v hu hv huv q h1 h2) H2 H3
  · rw [deg_sum_drop P _ hk, ← hvN] at *
    unfold deg at *
    omega

theorem outer_cur2 {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : range 0 n = pref1 ++ cur1 :: suff1) :
    cur1.toNat < n.toNat ∧ get ord cur1 = ord[cur1.toNat]! ∧ cur1.toNat = pref1.length := by
  have e := range_cursor hr1
  have hl := congrArg List.length hr1
  simp [range_length] at hl e
  refine ⟨by omega, rfl, by omega⟩

theorem tgt_distinct {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (v : Nat) (hv : v < n.toNat) (q q' : Nat) (h1 : A head v ≤ q) (h2 : q < B head v) (h1' : A head v ≤ q')
    (h2' : q' < B head v) (hne : q ≠ q') : target[q]!.toNat ≠ target[q']!.toNat := by
  have hnd := P.T.nodup v hv
  unfold nbs at hnd
  rw [arcs_eq] at hnd
  have hp := List.pairwise_map.mp hnd
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := List.pairwise_iff_getElem.mp hp (q - A head v) (q' - A head v) (by simp; omega) (by simp; omega) (by omega)
    simp [List.getElem_range', tgt_eq] at this
    have e1 : A head v + (q - A head v) = q := by omega
    have e2 : A head v + (q' - A head v) = q' := by omega
    rw [e1, e2] at this; exact this
  · have := List.pairwise_iff_getElem.mp hp (q' - A head v) (q - A head v) (by simp; omega) (by simp; omega) (by omega)
    simp [List.getElem_range', tgt_eq] at this
    have e1 : A head v + (q - A head v) = q := by omega
    have e2 : A head v + (q' - A head v) = q' := by omega
    rw [e1, e2] at this; exact fun h => this h.symm

theorem i5_vc {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    {pref1 suff1 : List Int} {cur1 : Int} (hr1 : range 0 n = pref1 ++ cur1 :: suff1)
    {pref suff : List Int} {cur : Int}
    (hr : range (get head (get ord cur1)) (get head (get ord cur1 + 1)) = pref ++ cur :: suff)
    (pre suf up0 up : Array Int) (hus : up0.size = n.toNat)
    (H : I5 target parent pre suf up0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) pref.length up) :
    (get parent (get target cur) = get ord cur1 →
      I5 target parent pre suf up0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) (pref.length + 1)
        (set up (get target cur) (M.su (M.op (M.op (get up (get ord cur1)) (get pre cur)) (get suf cur))))) ∧
    (¬get parent (get target cur) = get ord cur1 →
      I5 target parent pre suf up0 M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat) (pref.length + 1) up) := by
  obtain ⟨hk, hg, -⟩ := outer_cur2 P hr1
  rw [hg] at hr ⊢
  obtain ⟨hv, hov, -, -⟩ := P.vtx _ hk
  obtain ⟨hc, hlt⟩ := inner_cur P _ hk hr
  have T := P.T
  have hstep := I5_step target parent pre suf up0 M n.toNat ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat)
    pref.length up H hus
    (fun q h1 h2 hkd => by
      have := kid_facts' head target parent ord _ _ T _ hv q h1 (by omega) hkd
      exact ⟨this.1, fun he => by rw [he] at this; omega⟩)
    (fun q h1 h2 _ _ => tgt_distinct P _ hv q _ h1 (by omega) (by omega) hlt (by omega))
  have ht0 : 0 ≤ target[A head ord[cur1.toNat]!.toNat + pref.length]! :=
    (P.htgt _ (by have := P.B_last _ hv; omega)).1
  have gt : get target cur = ((target[A head ord[cur1.toNat]!.toNat + pref.length]!.toNat : Nat) : Int) := by
    simp only [get, hc, Int.toNat_natCast]; omega
  have gp : get parent (get target cur) = parent[target[A head ord[cur1.toNat]!.toNat + pref.length]!.toNat]! := by
    simp only [get, hc, Int.toNat_natCast]
  have gu : get up ord[cur1.toNat]! = up[ord[cur1.toNat]!.toNat]! := rfl
  have gpre : get pre cur = pre[A head ord[cur1.toNat]!.toNat + pref.length]! := by simp only [get, hc, Int.toNat_natCast]
  have gsuf : get suf cur = suf[A head ord[cur1.toNat]!.toNat + pref.length]! := by simp only [get, hc, Int.toNat_natCast]
  rw [gp, gt, gu, gpre, gsuf]
  conv at hstep => rw [← hov]
  constructor
  · intro h; rw [if_pos h] at hstep; exact hstep
  · intro h; rw [if_neg h] at hstep; exact hstep

theorem deg_sum_take {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root)
    (k : Nat) (hk : k < n.toNat) :
    (((NL ord).take (k + 1)).map (deg head)).sum = (((NL ord).take k).map (deg head)).sum + deg head ord[k]!.toNat := by
  have hl := P.T.ordlen
  have hk' : k < (NL ord).length := by omega
  rw [List.take_succ, List.getElem?_eq_getElem hk']
  have e : (NL ord)[k] = ord[k]!.toNat := by
    have := NL_getD ord k; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] at this; simpa using this
  simp [e]

theorem q4_step {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) (M : CM)
    (t0 s0 : Nat) {pref1 suff1 : List Int} {cur1 : Int} (hr1 : range 0 n = pref1 ++ cur1 :: suff1)
    (dp pre suf full0 up full up' : Array Int) (s2 s1 s : Nat)
    (hQ : Q1 head target parent ord M n.toNat t0 (rangeDown 0 (n - 1)).length dp pre suf full0 s2)
    (hQ4 : Q4 head target parent ord dp pre suf M n.toNat root.toNat s0 pref1.length up full s1)
    (H5 : I5 target parent pre suf up M ord[cur1.toNat]!.toNat (A head ord[cur1.toNat]!.toNat)
      (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length up')
    (hc : s ≤ s1 + 3 + 4 * (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length) :
    Q4 head target parent ord dp pre suf M n.toNat root.toNat s0 (pref1.length + 1) up'
      (set full (get ord cur1) (M.su (M.op (get up (get ord cur1)) (get full (get ord cur1))))) s := by
  obtain ⟨hk, hg, hcur⟩ := outer_cur2 P hr1
  obtain ⟨hv, hov, h3, h4⟩ := P.vtx _ hk
  have hlen : (range (get head (get ord cur1)) (get head (get ord cur1 + 1))).length =
      B head ord[cur1.toNat]!.toNat - A head ord[cur1.toNat]!.toNat := by
    rw [hg, h3, h4]; simp [range_length]
  rw [hlen] at H5 hc
  obtain ⟨⟨hV, hP1⟩, -, -, -, -, -⟩ := hQ
  have hl : (rangeDown 0 (n - 1)).length = n.toNat := by simp [rangeDown]
  rw [hl, Nat.sub_self] at hP1
  obtain ⟨p2, ups, fs, cst⟩ := hQ4
  have hpos := pos_at P _ hk
  have T := P.T
  rw [hg, hov]
  simp only [get, Int.toNat_natCast]
  generalize hvN : ord[cur1.toNat]!.toNat = v at *
  rw [hcur] at hpos
  have hAB : ∀ u, u < n.toNat → A head u ≤ B head u := P.AB
  refine ⟨P2_step head target parent dp pre suf M n.toNat root.toNat (pos (NL ord)) up full up' pref1.length v p2 hv
      hpos ups fs (fun u hu huv h => huv (pos_inj ord n.toNat T.ordlen T.ordmem u v hu hv h))
      (fun q h1 h2 hkd => by
        have := kid_facts' head target parent ord _ _ T v hv q h1 h2 hkd
        exact ⟨this.1, fun he => by rw [he] at this; omega, by omega, this.2.1⟩)
      (hAB v hv)
      (fun q h1 h2 hkd => by
        obtain ⟨-, -, c3⟩ := hP1 v hv (Nat.zero_le _)
        obtain ⟨d1, d2⟩ := c3 q h1 h2 hkd
        have hB := P.B_last v hv
        refine ⟨?_, ?_⟩
        · rw [d1]; exact fold_V M _ (KS_V target parent dp M n.toNat hV P.ht v _ _ (by omega))
        · rw [d2]; exact fold_V M _ (KS_V target parent dp M n.toNat hV P.ht v _ _ (by omega)))
      H5, by rw [H5.1, ups], by simp [fs], ?_⟩
  rw [← hcur] at cst ⊢
  rw [deg_sum_take P _ hk, hvN]
  have : deg head v = B head v - A head v := rfl
  omega

theorem deg_total {head target parent ord : Array Int} {n root : Int} (P : Pre head target parent ord n root) :
    ((NL ord).map (deg head)).sum ≤ target.size := by
  have T := P.T
  have hperm : (NL ord).Perm (List.range n.toNat) :=
    (List.subperm_of_subset T.ordnd (fun x hx => List.mem_range.mpr (T.ordlt x hx))).perm_of_length_le
      (by simp [T.ordlen])
  rw [(hperm.map (deg head)).sum_nat]
  have tele : ∀ k, k ≤ n.toNat → ((List.range k).map (deg head)).sum + head[0]!.toNat = head[k]!.toNat := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.sum_append]
      have := ih (by omega); have := P.hmono k (by omega); have := P.hhead k (by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, deg, A, B]
      omega
  have := tele n.toNat (Nat.le_refl _)
  have := P.hlast; have := P.hhead n.toNat (Nat.le_refl _)
  omega

theorem tree_full_dp_spec (pol : cp.tree_full_dp.Policy_P Int) (M : CM)
    (hE : ∀ {Q : PostCond Int PS}, ⦃fun t => Q.1 M.e (t + 1)⦄ pol.e ⦃Q⦄)
    (hOp : ∀ a b, ∀ {Q : PostCond Int PS}, ⦃fun t => Q.1 (M.op a b) (t + 1)⦄ pol.op a b ⦃Q⦄)
    (hSu : ∀ a, ∀ {Q : PostCond Int PS}, ⦃fun t => Q.1 (M.su a) (t + 1)⦄ pol.sum_up a ⦃Q⦄)
    (head target parent ord dp pre suf up full : Array Int) (root n : Int)
    (hP : Pre head target parent ord n root)
    (hdps : dp.size = n.toNat) (hups : up.size = n.toNat) (hfs : full.size = n.toNat)
    (hpres : pre.size = target.size) (hsufs : suf.size = target.size)
    (hVdp : ∀ x, x < n.toNat → M.V dp[x]!) (hVup : ∀ x, x < n.toNat → M.V up[x]!) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_full_dp pol head target parent ord dp pre suf up full root n
    ⦃⇓ r c => ⌜(∀ v, v < n.toNat →
        ∃ f, Ef M (NL head) (NL target) f (pp parent.toList n.toNat root.toNat v) v = some r.1[v]!) ∧
      (∀ w, w < n.toNat → w ≠ root.toNat →
        ∃ f, Ef M (NL head) (NL target) f w (par parent.toList w) = some r.2.2.2.1[w]!) ∧
      (∀ v, v < n.toNat → ∃ f, Ef M (NL head) (NL target) f n.toNat v = some r.2.2.2.2[v]!) ∧
      c ≤ t0 + 2 + 7 * n.toNat + 8 * target.size⌝⦄ := by
  mvcgen [cp.tree_full_dp, hE, hOp, hSu]
  case inv1 => exact ⇓⟨xs, dp, pre, suf, full⟩ c => ⌜Q1 head target parent ord M n.toNat t0 xs.prefix.length dp pre suf full c⌝
  case inv2 =>
    rename_i _ cur _ _ b _ _ _ _ _ _ s _ _ _
    exact ⇓⟨xs, pre, acc⟩ c => ⌜I2 target parent b.1 b.2.1 M (ord[cur.toNat]!.toNat)
      (A head (ord[cur.toNat]!.toNat)) xs.prefix.length pre acc ∧ c ≤ s + 2 + 2 * xs.prefix.length⌝
  case inv3 =>
    rename_i _ cur _ _ b _ _ _ _ _ _ _ _ _ _ r _ _ _ s _ _ _
    exact ⇓⟨xs, suf, back⟩ c => ⌜I3 target parent (set b.1 (get ord cur) (M.su r.2)) b.2.2.1 M (ord[cur.toNat]!.toNat)
      (B head (ord[cur.toNat]!.toNat)) xs.prefix.length suf back ∧ c ≤ s + 2 + 2 * xs.prefix.length⌝
  case inv4 =>
    rename_i r _ _ _ _ _ _ s _ _
    exact ⇓⟨xs, up, full⟩ c => ⌜Q4 head target parent ord r.1 r.2.1 r.2.2.1 M n.toNat root.toNat s
      xs.prefix.length up full c⌝
  case inv5 =>
    rename_i r _ _ _ _ _ _ _ _ _ _ cur _ _ b _ _ s _ _ _ _
    exact ⇓⟨xs, up⟩ c => ⌜I5 target parent r.2.1 r.2.2.1 b.1 M (ord[cur.toNat]!.toNat)
      (A head (ord[cur.toNat]!.toNat)) xs.prefix.length up ∧ c ≤ s + 3 + 4 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  case vc1.step.isTrue =>
    obtain ⟨H, hc⟩ := ‹I2 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    exact ⟨(i2_vc hP M ‹rangeDown 0 (n - 1) = _› ‹range _ _ = _› _ _ _ _ hQ.2.2.1 H).1 ‹_›, by omega⟩
  case vc2.step.isFalse =>
    obtain ⟨H, hc⟩ := ‹I2 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    exact ⟨(i2_vc hP M ‹rangeDown 0 (n - 1) = _› ‹range _ _ = _› _ _ _ _ hQ.2.2.1 H).2 ‹_›, by omega⟩
  case vc3.step.pre => exact I2_zero _ _ _ _ _ _ _
  case vc6.step.post.success.pre => exact I3_zero _ _ _ _ _ _ _
  case vc13.step.pre => exact I5_zero _ _ _ _ _ _ _ _
  case vc4.step.isTrue =>
    obtain ⟨H, hc⟩ := ‹I3 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    obtain ⟨H2, -⟩ := ‹I2 _ _ _ _ _ _ _ _ _ _ ∧ _›
    exact ⟨(i3_vc' hP M ‹rangeDown 0 (n - 1) = _› ‹rangeDown _ _ = _› _ _ _ _ _ _ _ hQ.2.2.2.1 hQ.1.1 H2 H).1 ‹_›,
      by omega⟩
  case vc5.step.isFalse =>
    obtain ⟨H, hc⟩ := ‹I3 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    obtain ⟨H2, -⟩ := ‹I2 _ _ _ _ _ _ _ _ _ _ ∧ _›
    exact ⟨(i3_vc' hP M ‹rangeDown 0 (n - 1) = _› ‹rangeDown _ _ = _› _ _ _ _ _ _ _ hQ.2.2.2.1 hQ.1.1 H2 H).2 ‹_›,
      by omega⟩
  case vc7.step.post.success.post.success =>
    obtain ⟨H2, hc1⟩ := ‹I2 _ _ _ _ _ _ _ _ _ _ ∧ _›
    obtain ⟨H3, hc⟩ := ‹I3 _ _ _ _ _ _ _ _ _ _ ∧ _›
    exact q1_step hP M t0 ‹rangeDown 0 (n - 1) = _› _ _ _ _ _ _ _ _ _ _ _ ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _› H2 hc1 H3 hc
  case vc11.step.isTrue =>
    obtain ⟨H, hc⟩ := ‹I5 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _›
    exact ⟨(i5_vc hP M ‹range 0 n = _› ‹range (get head _) _ = _› _ _ _ _ hQ.2.1 H).1 ‹_›, by omega⟩
  case vc12.step.isFalse =>
    obtain ⟨H, hc⟩ := ‹I5 _ _ _ _ _ _ _ _ _ _ ∧ _›
    have hQ := ‹Q4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _›
    exact ⟨(i5_vc hP M ‹range 0 n = _› ‹range (get head _) _ = _› _ _ _ _ hQ.2.1 H).2 ‹_›, by omega⟩
  case vc10.pre =>
    refine ⟨⟨fun x hx => hVdp x (by omega), fun u hu hmu => absurd (hP.T.pos_lt u hu) (by omega)⟩, hdps, hpres, hsufs,
      hfs, by simp; omega⟩
  case vc16.post.success.pre =>
    obtain ⟨⟨q0, q1⟩, -, -, -, q5, -⟩ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    have hroot : root.toNat < up.size := by have := hP.r0; omega
    have gup : ∀ x, (set up root M.e)[x]! = if x = root.toNat then M.e else up[x]! := by
      intro x; rw [getElemBang_set _ _ _ _ hroot]
    refine ⟨⟨?_, fun x hx => ?_, fun u hu h => absurd h (Nat.not_lt_zero _), fun u hu _ => ?_⟩,
      by simp [hups], q5, by simp⟩
    · rw [gup]; simp
    · rw [gup]; split
      · exact M.he
      · exact hVup x (by omega)
    · have : (rangeDown 0 (n - 1)).length = n.toNat := by simp [rangeDown]
      rw [this, Nat.sub_self] at q1
      exact (q1 u hu (Nat.zero_le _)).2.1
  case vc14.step.post.success =>
    obtain ⟨H5, hc⟩ := ‹I5 _ _ _ _ _ _ _ _ _ _ ∧ _›
    exact q4_step hP M t0 _ ‹range 0 n = _› _ _ _ _ _ _ _ _ _ _ ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
      ‹Q4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _› H5 hc
  case vc17.post.success.post.success =>
    obtain ⟨q1, -, -, -, -, qc⟩ := ‹Q1 _ _ _ _ _ _ _ _ _ _ _ _ _›
    obtain ⟨p2, -, -, pc⟩ := ‹Q4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _›
    have hl1 : (rangeDown 0 (n - 1)).length = n.toNat := by simp [rangeDown]
    have hl2 : (range 0 n).length = n.toNat := by simp [range_length]
    rw [hl1, Nat.sub_self] at q1 qc
    rw [hl2] at p2 pc
    have T := hP.T
    obtain ⟨f1, f2, f3⟩ := final_facts head target parent ord _ _ _ _ _ _ M n.toNat root.toNat T hP.ht
      (fun v hv => hP.B_last v hv) q1 p2
    have hd := deg_total hP
    have htake : (NL ord).take n.toNat = NL ord := List.take_of_length_le (by rw [T.ordlen])
    rw [List.drop_zero] at qc
    rw [htake] at pc
    exact ⟨fun v hv => f1 v (by omega), fun w hw hr => f2 w (by omega) hr, fun v hv => f3 v (by omega), by omega⟩

/-- The monoid of `DpHeight<long long>`: `max` on the non-negative integers, `sum_up(x) = x + 1`. -/
def heightCM : CM where
  V x := 0 ≤ x
  op a b := max a b
  e := 0
  su x := x + 1
  he := Int.le_refl 0
  closed a b ha _ := le_max_of_le_left ha
  suV a ha := by omega
  assoc a b c _ _ _ := max_assoc a b c
  comm a b _ _ := max_comm a b
  lid a ha := max_eq_right ha

/-- The policy value of `DpHeight<long long>`. -/
def heightPolicy : cp.tree_full_dp.Policy_P Int :=
  { e := cp.DpHeight.e, op := cp.DpHeight.op, sum_up := cp.DpHeight.sum_up }

theorem height_e {Q : PostCond Int PS} : ⦃fun t => Q.1 heightCM.e (t + 1)⦄ heightPolicy.e ⦃Q⦄ := by
  mvcgen [heightPolicy, cp.DpHeight.e, heightCM]

theorem height_op (a b : Int) {Q : PostCond Int PS} :
    ⦃fun t => Q.1 (heightCM.op a b) (t + 1)⦄ heightPolicy.op a b ⦃Q⦄ := by
  mvcgen [heightPolicy, cp.DpHeight.op]
  all_goals simp only [heightCM, max_def] at *
  · rename_i hc hq
    simp only [decide_eq_true_eq] at hc; rwa [if_pos (by omega)] at hq
  · rename_i hc hq
    simp only [decide_eq_true_eq, not_lt] at hc
    by_cases h : a ≤ b
    · have : a = b := by omega
      subst this; rwa [if_pos h] at hq
    · rwa [if_neg h] at hq

theorem height_sum_up (a : Int) {Q : PostCond Int PS} :
    ⦃fun t => Q.1 (heightCM.su a) (t + 1)⦄ heightPolicy.sum_up a ⦃Q⦄ := by
  mvcgen [heightPolicy, cp.DpHeight.sum_up, heightCM]

end Proofs.Cpp.TreeFullDp