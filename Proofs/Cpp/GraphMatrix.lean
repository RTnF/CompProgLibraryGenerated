import Proofs.Cpp.Gen.GraphMatrix
import Proofs.Cpp.Lib.Basic
import Proofs.Math.GraphMatrixMath

/-! # `MatrixGraph<Cost>` (library/graph/graph_matrix.hpp)

Proved for `Cost = long long` (the carrier `Int`, `UNREACHABLE = 2^61 - 1`). The matrices are `Array`s of `n` rows
of length `n` (`Rep`). `warshall_floyd` runs the in-place loop `fwK` of `Proofs.GraphMatrixMath` from the weights
`mat` and the initial parents `P0`, then replaces the entries `> UNREACHABLE / 2` by `UNREACHABLE` and records
whether a diagonal entry is negative. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.GraphMatrixMath

namespace Proofs.Cpp.GraphMatrix

/-- `std::numeric_limits<long long>`. -/
local instance : Cpp.NumericTraits "Cost" Int := Cpp.intNumericTraits "Cost" 64 true

/-- `MatrixGraph<long long>::UNREACHABLE`. -/
def U : Int := 2 ^ 61 - 1

theorem unr_val : Cpp.ShiftInt.shr (Cpp.NumericTraits.maximum (tag := "Cost") (α := Int)) 2 = U := by
  decide

@[spec] theorem unr_spec {Q : PostCond Int PS} :
    ⦃fun t => Q.1 U (t + 1)⦄ (cp.MatrixGraph.UNREACHABLE (Cost := Int)) ⦃Q⦄ := by
  mvcgen [cp.MatrixGraph.UNREACHABLE]

/-- `a[p][q]`. -/
def G (a : Array (Array Int)) (p q : Nat) : Int := (a[p]!)[q]!

/-- `a` is the `n × n` matrix `F`. -/
def Rep (n : Nat) (a : Array (Array Int)) (F : Nat → Nat → Int) : Prop :=
  a.size = n ∧ (∀ p, p < n → (a[p]!).size = n) ∧ ∀ p q, p < n → q < n → G a p q = F p q

theorem rep_set (n : Nat) (a : Array (Array Int)) (F : Nat → Nat → Int) (h : Rep n a F) (i j : Nat) (hi : i < n)
    (hj : j < n) (v : Int) :
    Rep n (Cpp.set a (i : Int) (Cpp.set (Cpp.get a (i : Int)) (j : Int) v)) (upd F i j v) := by
  obtain ⟨hs, hr, he⟩ := h
  refine ⟨by simp [hs], fun p hp => ?_, fun p q hp hq => ?_⟩
  · rw [getElemBang_set _ _ _ _ (by simp; omega)]
    split
    · rename_i e; simp at e; subst e; simp [get_eq, hr _ hp]
    · exact hr p hp
  · unfold G upd
    rw [getElemBang_set _ _ _ _ (by simp; omega)]
    by_cases hpi : p = i
    · subst hpi
      simp only [Int.toNat_natCast, ite_true, get_eq]
      rw [getElemBang_set _ _ _ _ (by simp; rw [hr _ hp]; omega)]
      by_cases hqj : q = j
      · subst hqj; simp
      · simp only [Int.toNat_natCast, hqj, ite_false, and_false]; exact he p q hp hq
    · simp only [Int.toNat_natCast, hpi, ite_false, false_and]; exact he p q hp hq

theorem rep_get (n : Nat) (a : Array (Array Int)) (F : Nat → Nat → Int) (h : Rep n a F) (p q : Nat) (hp : p < n)
    (hq : q < n) : Cpp.get (Cpp.get a (p : Int)) (q : Int) = F p q := by
  rw [← h.2.2 p q hp hq]; rfl

/-- The weights. -/
def Wt (g : cp.MatrixGraph Int) : Nat → Nat → Int := G g.mat

/-- The parents before the rounds: `i` for an edge `i → j` (`mat[i][j] < UNREACHABLE`) and on the diagonal. -/
def P0 (W : Nat → Nat → Int) : Nat → Nat → Int := fun p q => if W p q < U ∨ p = q then (p : Int) else -1

/-- The distances and parents after the rounds. -/
def FW (n : Nat) (W : Nat → Nat → Int) : St := fwK n n ⟨W, P0 W⟩

/-- The final distances: entries `> UNREACHABLE / 2` become `UNREACHABLE`. -/
def norm (x : Int) : Int := if U / 2 < x then U else x

/-- The parent initialisation loop: the entries before `(i, j)` hold `P0`, the others `-1`. -/
def Q0 (W : Nat → Nat → Int) (i j : Nat) : Nat → Nat → Int := fun p q => if done i j p q then P0 W p q else -1

/-- The normalisation loop. -/
def N0 (D : Nat → Nat → Int) (i j : Nat) : Nat → Nat → Int := fun p q => if done i j p q then norm (D p q) else D p q

theorem cur_of {n cur : Int} {pref suff : List Int} (h : range 0 n = pref ++ cur :: suff) :
    cur = (pref.length : Int) ∧ pref.length < n.toNat := by
  have h1 := range_cursor h
  have h2 := range_prefix_length h
  exact ⟨by omega, by simpa using h2⟩

theorem rep_ext {n : Nat} {a : Array (Array Int)} {F F' : Nat → Nat → Int} (h : Rep n a F)
    (e : ∀ p q, p < n → q < n → F p q = F' p q) : Rep n a F' :=
  ⟨h.1, h.2.1, fun p q hp hq => (h.2.2 p q hp hq).trans (e p q hp hq)⟩

theorem rep_replicate (n : Int) (hn : 0 ≤ n) (x : Int) :
    Rep n.toNat (Cpp.replicate n (Cpp.replicate n x)) (fun _ _ => x) := by
  refine ⟨by simp [replicate], fun p hp => ?_, fun p q hp hq => ?_⟩
  · simp only [replicate]; rw [getElem!_pos _ _ (by simpa using hp)]; simp
  · simp only [G, replicate]
    rw [getElem!_pos (Array.replicate n.toNat (Array.replicate n.toNat x)) p (by simpa using hp),
      Array.getElem_replicate, getElem!_pos (Array.replicate n.toNat x) q (by simpa using hq), Array.getElem_replicate]

theorem q0_set (W : Nat → Nat → Int) (i j : Nat) (hc : W i j < U ∨ i = j) (p q : Nat) :
    upd (Q0 W i j) i j (i : Int) p q = Q0 W i (j + 1) p q := by
  unfold upd Q0 P0
  by_cases e : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := e; rw [if_pos ⟨rfl, rfl⟩, if_pos (Or.inr ⟨rfl, by omega⟩), if_pos hc]
  · rw [if_neg e]
    have : done i (j + 1) p q ↔ done i j p q := by simp only [done]; omega
    exact (if_congr this rfl rfl).symm

theorem q0_keep (W : Nat → Nat → Int) (i j : Nat) (hc : ¬ (W i j < U ∨ i = j)) (p q : Nat) :
    Q0 W i j p q = Q0 W i (j + 1) p q := by
  unfold Q0 P0
  by_cases e : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := e; rw [if_neg (by simp [done]), if_pos (Or.inr ⟨rfl, by omega⟩), if_neg hc]
  · have : done i (j + 1) p q ↔ done i j p q := by simp only [done]; omega
    exact (if_congr this rfl rfl).symm

theorem q0_row (W : Nat → Nat → Int) (n i p q : Nat) (hq : q < n) : Q0 W i n p q = Q0 W (i + 1) 0 p q := by
  unfold Q0
  have : done (i + 1) 0 p q ↔ done i n p q := by simp only [done]; omega
  exact (if_congr this rfl rfl).symm

theorem q0_end (W : Nat → Nat → Int) (n p q : Nat) (hp : p < n) : Q0 W n 0 p q = P0 W p q := by
  unfold Q0; rw [if_pos (Or.inl hp)]

theorem n0_set (D : Nat → Nat → Int) (i j : Nat) (hc : U / 2 < D i j) (p q : Nat) :
    upd (N0 D i j) i j U p q = N0 D i (j + 1) p q := by
  unfold upd N0 norm
  by_cases e : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := e; rw [if_pos ⟨rfl, rfl⟩, if_pos (Or.inr ⟨rfl, by omega⟩), if_pos hc]
  · rw [if_neg e]
    have : done i (j + 1) p q ↔ done i j p q := by simp only [done]; omega
    exact (if_congr this rfl rfl).symm

theorem n0_keep (D : Nat → Nat → Int) (i j : Nat) (hc : D i j ≤ U / 2) (p q : Nat) :
    N0 D i j p q = N0 D i (j + 1) p q := by
  unfold N0 norm
  by_cases e : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := e; rw [if_neg (by simp [done]), if_pos (Or.inr ⟨rfl, by omega⟩), if_neg (by omega)]
  · have : done i (j + 1) p q ↔ done i j p q := by simp only [done]; omega
    exact (if_congr this rfl rfl).symm

theorem n0_here (D : Nat → Nat → Int) (i j : Nat) : N0 D i j i j = D i j := by
  unfold N0; rw [if_neg (by simp [done])]

theorem n0_row (D : Nat → Nat → Int) (n i p q : Nat) (hq : q < n) : N0 D i n p q = N0 D (i + 1) 0 p q := by
  unfold N0
  have : done (i + 1) 0 p q ↔ done i n p q := by simp only [done]; omega
  exact (if_congr this rfl rfl).symm

theorem n0_start (D : Nat → Nat → Int) (p q : Nat) : D p q = N0 D 0 0 p q := by
  unfold N0; rw [if_neg (by simp [done])]

theorem n0_end (D : Nat → Nat → Int) (n p q : Nat) (hp : p < n) : N0 D n 0 p q = norm (D p q) := by
  unfold N0; rw [if_pos (Or.inl hp)]

theorem norm_neg (x : Int) : norm x < 0 ↔ x < 0 := by
  unfold norm U; split <;> omega

/-- One step of the triple loop on the arrays. -/
theorem fw_vc (N k i j : Nat) (hk : k < N) (hi : i < N) (hj : j < N) (c : St) (d p : Array (Array Int))
    (hd : Rep N d c.D) (hp : Rep N p c.P) :
    (Cpp.get (Cpp.get d (i : Int)) (k : Int) + Cpp.get (Cpp.get d (k : Int)) (j : Int) <
        Cpp.get (Cpp.get d (i : Int)) (j : Int) →
      Rep N (Cpp.set d (i : Int) (Cpp.set (Cpp.get d (i : Int)) (j : Int)
          (Cpp.get (Cpp.get d (i : Int)) (k : Int) + Cpp.get (Cpp.get d (k : Int)) (j : Int)))) (step k i j c).D ∧
      Rep N (Cpp.set p (i : Int) (Cpp.set (Cpp.get p (i : Int)) (j : Int) (Cpp.get (Cpp.get p (k : Int)) (j : Int))))
        (step k i j c).P) ∧
    (Cpp.get (Cpp.get d (i : Int)) (j : Int) ≤
        Cpp.get (Cpp.get d (i : Int)) (k : Int) + Cpp.get (Cpp.get d (k : Int)) (j : Int) →
      Rep N d (step k i j c).D ∧ Rep N p (step k i j c).P) := by
  rw [rep_get N d _ hd i k hi hk, rep_get N d _ hd k j hk hj, rep_get N d _ hd i j hi hj,
    rep_get N p _ hp k j hk hj]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold step; rw [if_pos h]
    exact ⟨rep_set N d _ hd i j hi hj _, rep_set N p _ hp i j hi hj _⟩
  · unfold step; rw [if_neg (by omega)]; exact ⟨hd, hp⟩

theorem cost_bound (N : Nat) :
    1 + N + N + N * (N + 1) + N * (1 + 2 * N) + N * (1 + N * (1 + N)) + N * (1 + 3 * N) + N ≤ 8 * (N + 1) ^ 3 := by
  nlinarith [Nat.zero_le (N * N), Nat.zero_le (N * N * N)]

theorem warshall_floyd_spec (g : cp.MatrixGraph Int) (hn : 0 ≤ g.n) (hW : Rep g.n.toNat g.mat (Wt g))
    (hd : g.shortest_path_dist.size = 0) (hc : g.negative_cycle = false) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.MatrixGraph.warshall_floyd g
    ⦃⇓ r c => ⌜r.n = g.n ∧ r.m = g.m ∧ r.mat = g.mat ∧
      Rep g.n.toNat r.shortest_path_dist (fun p q => norm ((FW g.n.toNat (Wt g)).D p q)) ∧
      Rep g.n.toNat r.shortest_path_parent (FW g.n.toNat (Wt g)).P ∧
      (r.negative_cycle = true ↔ ∃ v, v < g.n.toNat ∧ (FW g.n.toNat (Wt g)).D v v < 0) ∧
      c ≤ t0 + 8 * (g.n.toNat + 1) ^ 3⌝⦄ := by
  have hN := hW.1
  mvcgen [cp.MatrixGraph.warshall_floyd]
  case inv1 =>
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b (Q0 (Wt g) xs.prefix.length 0) ∧
    c = t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + xs.prefix.length * (1 + 2 * g.n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b (Q0 (Wt g) pi.length xs.prefix.length) ∧
        c = t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + pi.length * (1 + 2 * g.n.toNat) + 1 +
          xs.prefix.length * 2⌝
  case inv3 =>
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b.1 (fwK g.n.toNat xs.prefix.length ⟨Wt g, P0 (Wt g)⟩).D ∧
      Rep g.n.toNat b.2 (fwK g.n.toNat xs.prefix.length ⟨Wt g, P0 (Wt g)⟩).P ∧
      c = t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
        xs.prefix.length * (1 + g.n.toNat * (1 + g.n.toNat))⌝
  case inv4 =>
    rename_i pk _ _ _ _ _ _ _ _
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b.1 (roundI g.n.toNat pk.length xs.prefix.length (fwK g.n.toNat pk.length ⟨Wt g, P0 (Wt g)⟩)).D ∧
        Rep g.n.toNat b.2 (roundI g.n.toNat pk.length xs.prefix.length (fwK g.n.toNat pk.length ⟨Wt g, P0 (Wt g)⟩)).P ∧
        c = t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
          pk.length * (1 + g.n.toNat * (1 + g.n.toNat)) + 1 + xs.prefix.length * (1 + g.n.toNat)⌝
  case inv5 =>
    rename_i pk _ _ _ _ _ _ _ _ pi _ _ _ _ _ _ _ _
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b.1 (rowJ pk.length pi.length xs.prefix.length
          (roundI g.n.toNat pk.length pi.length (fwK g.n.toNat pk.length ⟨Wt g, P0 (Wt g)⟩))).D ∧
        Rep g.n.toNat b.2 (rowJ pk.length pi.length xs.prefix.length
          (roundI g.n.toNat pk.length pi.length (fwK g.n.toNat pk.length ⟨Wt g, P0 (Wt g)⟩))).P ∧
        c = t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
          pk.length * (1 + g.n.toNat * (1 + g.n.toNat)) + 1 + pi.length * (1 + g.n.toNat) + 1 + xs.prefix.length⌝
  case inv6 =>
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b (N0 (FW g.n.toNat (Wt g)).D xs.prefix.length 0) ∧
      c ≤ t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
        g.n.toNat * (1 + g.n.toNat * (1 + g.n.toNat)) + xs.prefix.length * (1 + 3 * g.n.toNat)⌝
  case inv7 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, b⟩ c => ⌜Rep g.n.toNat b (N0 (FW g.n.toNat (Wt g)).D pi.length xs.prefix.length) ∧
        c ≤ t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
          g.n.toNat * (1 + g.n.toNat * (1 + g.n.toNat)) + pi.length * (1 + 3 * g.n.toNat) + 1 + 3 * xs.prefix.length⌝
  case inv8 =>
    exact ⇓⟨xs, b⟩ c => ⌜((b = true ∧ ∃ v, v < g.n.toNat ∧ (FW g.n.toNat (Wt g)).D v v < 0) ∨
        (b = false ∧ ∀ v, v < xs.prefix.length → 0 ≤ (FW g.n.toNat (Wt g)).D v v)) ∧
      c ≤ t0 + 1 + g.n.toNat + g.n.toNat + g.n.toNat * (g.n.toNat + 1) + g.n.toNat * (1 + 2 * g.n.toNat) +
        g.n.toNat * (1 + g.n.toNat * (1 + g.n.toNat)) + g.n.toNat * (1 + 3 * g.n.toNat) + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.isTrue => rename_i h0; simp [hd, size] at h0
  case vc2.step.isTrue =>
    rename_i s2 h6 n0 m0 mat0 sd0 sp2 nc0 t30 sp1 pref1 cur1 suff1 h5 b1 s1 h4 pref0 cur0 suff0 h3 b0 s0 h2 sp0 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h5
    obtain ⟨rfl, hj⟩ := cur_of h3
    rw [rep_get _ _ _ hW _ _ hi hj] at h0
    exact ⟨rep_ext (rep_set _ _ _ h2.1 _ _ hi hj _) (fun p q _ _ => q0_set _ _ _ (by exact_mod_cast h0) p q),
      by omega⟩
  case vc3.step.isFalse =>
    rename_i s2 h6 n0 m0 mat0 sd0 sp1 nc0 t30 sp0 pref1 cur1 suff1 h5 b1 s1 h4 pref0 cur0 suff0 h3 b0 s0 h2 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h5
    obtain ⟨rfl, hj⟩ := cur_of h3
    rw [rep_get _ _ _ hW _ _ hi hj] at h0
    exact ⟨rep_ext h2.1 (fun p q _ _ => q0_keep _ _ _ (by
      intro h; rcases h with h | h
      · exact absurd h (not_lt.mpr h0.1)
      · exact h0.2 (by exact_mod_cast h)) p q), by omega⟩
  case vc4.step.pre =>
    rename_i s1 h3 n0 m0 mat0 sd0 sp1 nc0 t30 sp0 pref0 cur0 suff0 h2 b0 s0 h1 h0
    exact ⟨h1.1, by omega⟩
  case vc5.step.post.success =>
    rename_i s2 h4 n0 m0 mat0 sd0 sp1 nc0 t30 sp0 pref0 cur0 suff0 h3 b0 s1 h2 r0 s0 h1 h0
    exact ⟨rep_ext h0.1 (fun p q _ hq => q0_row _ _ _ p q hq), by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc7.isFalse.pre =>
    rename_i s0 h1 n0 m0 mat0 sd0 sp1 nc0 t30 sp0 h0
    refine ⟨rep_ext (rep_replicate g.n hn (-1)) (fun p q _ _ => by simp [Q0, done]), ?_⟩
    simp [replicate, hN]; omega
  case vc8.step.isTrue =>
    rename_i s4 h9 n0 m0 mat0 sd4 sp5 nc0 t30 sp4 r0 s3 pref2 cur2 suff2 h8 b2 sd3 sp3 s2 h7 pref1 cur1 suff1 h6 b1 sd2 sp2 s1 h5 pref0 cur0 suff0 h4 b0 sd1 sp1 s0 h3 sd0 sp0 h2 h1 h0
    obtain ⟨rfl, hk⟩ := cur_of h8
    obtain ⟨rfl, hi⟩ := cur_of h6
    obtain ⟨rfl, hj⟩ := cur_of h4
    have := (fw_vc _ _ _ _ hk hi hj _ _ _ h3.1 h3.2.1).1 h0
    exact ⟨this.1, this.2, by omega⟩
  case vc9.step.isFalse =>
    rename_i s4 h9 n0 m0 mat0 sd3 sp4 nc0 t30 sp3 r0 s3 pref2 cur2 suff2 h8 b2 sd2 sp2 s2 h7 pref1 cur1 suff1 h6 b1 sd1 sp1 s1 h5 pref0 cur0 suff0 h4 b0 sd0 sp0 s0 h3 h2 h1 h0
    obtain ⟨rfl, hk⟩ := cur_of h8
    obtain ⟨rfl, hi⟩ := cur_of h6
    obtain ⟨rfl, hj⟩ := cur_of h4
    have := (fw_vc _ _ _ _ hk hi hj _ _ _ h3.1 h3.2.1).2 h0
    exact ⟨this.1, this.2, by omega⟩
  case vc10.step.pre =>
    rename_i s3 h6 n0 m0 mat0 sd2 sp3 nc0 t30 sp2 r0 s2 pref1 cur1 suff1 h5 b1 sd1 sp1 s1 h4 pref0 cur0 suff0 h3 b0 sd0 sp0 s0 h2 h1 h0
    exact ⟨h2.1, h2.2.1, by omega⟩
  case vc11.step.post.success =>
    rename_i s4 h7 n0 m0 mat0 sd3 sp4 nc0 t30 sp3 r1 s3 pref1 cur1 suff1 h6 b1 sd2 sp2 s2 h5 pref0 cur0 suff0 h4 b0 sd1 sp1 s1 h3 r0 sd0 sp0 s0 h2 h1 h0
    exact ⟨h0.1, h0.2.1, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc13.step.pre =>
    rename_i s2 h4 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r0 s1 pref0 cur0 suff0 h3 b0 sd0 sp0 s0 h2 h1 h0
    exact ⟨h2.1, h2.2.1, by omega⟩
  case vc14.step.post.success =>
    rename_i s3 h5 n0 m0 mat0 sd2 sp3 nc0 t30 sp2 r1 s2 pref0 cur0 suff0 h4 b0 sd1 sp1 s1 h3 r0 sd0 sp0 s0 h2 h1 h0
    exact ⟨h0.1, h0.2.1, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc16.isFalse.post.success.pre =>
    rename_i s1 h2 n0 m0 mat0 sd0 sp1 nc0 t30 sp0 r0 s0 h1 h0
    exact ⟨hW, rep_ext h0.1 (fun p q hp _ => q0_end _ _ p q hp), by omega⟩
  case vc17.step.isTrue =>
    rename_i s4 h8 n0 m0 mat0 sd2 sp2 nc0 t30 sp1 r1 s3 r0 sd1 sp0 s2 pref1 cur1 suff1 h7 b1 s1 h6 pref0 cur0 suff0 h5 b0 s0 h4 sd0 h3 h2 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h7
    obtain ⟨rfl, hj⟩ := cur_of h5
    rw [rep_get _ _ _ h4.1 _ _ hi hj, n0_here] at h0
    exact ⟨rep_ext (rep_set _ _ _ h4.1 _ _ hi hj _) (fun p q _ _ => n0_set _ _ _ h0 p q), by omega⟩
  case vc18.step.isFalse =>
    rename_i s4 h8 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r1 s3 r0 sd0 sp0 s2 pref1 cur1 suff1 h7 b1 s1 h6 pref0 cur0 suff0 h5 b0 s0 h4 h3 h2 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h7
    obtain ⟨rfl, hj⟩ := cur_of h5
    rw [rep_get _ _ _ h4.1 _ _ hi hj, n0_here] at h0
    exact ⟨rep_ext h4.1 (fun p q _ _ => n0_keep _ _ _ h0 p q), by omega⟩
  case vc19.step.pre =>
    rename_i s3 h5 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r1 s2 r0 sd0 sp0 s1 pref0 cur0 suff0 h4 b0 s0 h3 h2 h1 h0
    exact ⟨h3.1, by omega⟩
  case vc20.step.post.success =>
    rename_i s4 h6 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r2 s3 r1 sd0 sp0 s2 pref0 cur0 suff0 h5 b0 s1 h4 r0 s0 h3 h2 h1 h0
    exact ⟨rep_ext h0.1 (fun p q _ hq => n0_row _ _ _ p q hq), by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc22.isFalse.post.success.post.success.pre =>
    rename_i s2 h3 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r1 s1 r0 sd0 sp0 s0 h2 h1 h0
    exact ⟨rep_ext h0.1 (fun p q _ _ => n0_start _ p q), by omega⟩
  case vc23.step.isTrue =>
    rename_i s4 h7 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r2 s3 r1 sd0 sp0 s2 r0 s1 pref0 cur0 suff0 h6 b0 s0 h5 h4 h3 h2 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h6
    rw [rep_get _ _ _ h2.1 _ _ hi hi, n0_end _ _ _ _ hi, norm_neg] at h0
    have hn0 : n0 = g.n := rfl
    exact ⟨⟨pref0.length, by omega, h0⟩, by have := h1.2; omega⟩
  case vc24.step.isFalse =>
    rename_i s4 h7 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r2 s3 r1 sd0 sp0 s2 r0 s1 pref0 cur0 suff0 h6 b0 s0 h5 h4 h3 h2 h1 h0
    obtain ⟨rfl, hi⟩ := cur_of h6
    rw [rep_get _ _ _ h2.1 _ _ hi hi, n0_end _ _ _ _ hi] at h0
    have hn0 : n0 = g.n := rfl
    have h0' : 0 ≤ (FW g.n.toNat (Wt g)).D pref0.length pref0.length := by
      have := (norm_neg ((FW g.n.toNat (Wt g)).D pref0.length pref0.length)).not.mp (by omega); omega
    refine ⟨?_, by have := h1.2; omega⟩
    rcases h1.1 with h | ⟨hb, hv⟩
    · exact Or.inl h
    · refine Or.inr ⟨hb, fun v hv' => ?_⟩
      by_cases e : v = pref0.length
      · subst e; exact h0'
      · exact hv v (by omega)
  case vc25.isFalse.post.success.post.success.post.success.pre =>
    rename_i s3 h4 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r2 s2 r1 sd0 sp0 s1 r0 s0 h3 h2 h1 h0
    exact ⟨Or.inr hc, by omega⟩
  case vc26.isFalse.post.success.post.success.post.success.post.success =>
    rename_i s4 h5 n0 m0 mat0 sd1 sp2 nc0 t30 sp1 r3 s3 r2 sd0 sp0 s2 r1 s1 r0 s0 h4 h3 h2 h1 h0
    refine ⟨rep_ext h1.1 (fun p q hp _ => n0_end _ _ _ _ hp), h2.2.1, ?_, ?_⟩
    · rcases h0.1 with ⟨h, hv⟩ | ⟨h, hv⟩
      · exact Iff.intro (fun _ => hv) (fun _ => h)
      · refine ⟨fun e => (by rw [h] at e; cases e), fun hh => ?_⟩
        obtain ⟨v, hv1, hv2⟩ := hh
        have := hv v hv1; omega
    · have := cost_bound g.n.toNat
      have := h0.2
      omega

/-! ## `get_shortest_path` -/

/-- The measure of the loop: the bounded rank of the current vertex (`0` at `-1` and at the source). -/
def meas (r : Nat → Nat) (N src : Nat) (cur : Int) : Nat := if cur < 0 ∨ cur = src then 0 else nrank r N cur.toNat + 1

/-- The vertices `L` pushed so far (from `dst`) and the current vertex `cur`: the parent of the last one; the
entry of the last one plus the walk back to `dst` is at most the entry of `dst`. -/
def Ch (W : Nat → Nat → Int) (S : St) (N src dst : Nat) (L : List Nat) (cur : Int) : Prop :=
  (∀ y ∈ L, y < N ∧ y ≠ src) ∧ ((L = [] ∧ cur = dst) ∨
    (L.head? = some dst ∧ ∃ x L', L = L' ++ [x] ∧ cur = S.P src x ∧ S.D src x + ww W L.reverse ≤ S.D src dst))

theorem ch_step (W : Nat → Nat → Int) (S : St) (N src dst : Nat) (hI : PInv W N N S) (hs : src < N) (hd : dst < N)
    (r : Nat → Nat) (hr : ∀ j p : Nat, j < N → j ≠ src → S.P src j = p → p ≠ src → r p < r j)
    (L : List Nat) (cur : Int) (h : Ch W S N src dst L cur) (h1 : cur ≠ src) (h2 : cur ≠ -1) :
    0 ≤ cur ∧ cur.toNat < N ∧ Ch W S N src dst (L ++ [cur.toNat]) (S.P src cur.toNat) ∧
      meas r N src (S.P src cur.toNat) < meas r N src cur := by
  obtain ⟨hL, hc⟩ := h
  -- the current vertex is a vertex `p < N`
  obtain ⟨p, rfl, hp⟩ : ∃ p : Nat, cur = p ∧ p < N := by
    rcases hc with ⟨_, rfl⟩ | ⟨_, x, L', rfl, rfl, _⟩
    · exact ⟨dst, rfl, hd⟩
    · have hx := hL x (by simp)
      rcases hI.par src x hs hx.1 hx.2 with e | ⟨q, e, hq, _⟩
      · exact absurd e h2
      · exact ⟨q, e, hq⟩
  have hps : p ≠ src := fun e => h1 (by rw [e])
  simp only [Int.toNat_natCast]
  refine ⟨by omega, hp, ⟨fun y hy => ?_, Or.inr ⟨?_, p, L, rfl, rfl, ?_⟩⟩, ?_⟩
  · rcases List.mem_append.mp hy with hy | hy
    · exact hL y hy
    · simp at hy; subst hy; exact ⟨hp, hps⟩
  · rcases hc with ⟨rfl, e⟩ | ⟨e, _⟩
    · simp at e ⊢; omega
    · cases L with
      | nil => simp at e
      | cons a l => simpa using e
  · rcases hc with ⟨rfl, e⟩ | ⟨_, x, L', rfl, e, hb⟩
    · have : p = dst := by exact_mod_cast e
      subst this; simp [ww]
    · rcases hI.par src x hs (hL x (by simp)).1 (hL x (by simp)).2 with e' | ⟨q, e', _, _, h4⟩
      · rw [← e] at e'; omega
      · have : q = p := by rw [← e] at e'; exact_mod_cast e'.symm
        subst this
        have := (h4 hps).1
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hb ⊢
        simp only [ww] at hb ⊢
        omega
  · have hm : meas r N src (p : Int) = nrank r N p + 1 := by
      unfold meas; rw [if_neg (by omega)]; simp
    rw [hm]
    unfold meas
    by_cases e : S.P src p < 0 ∨ S.P src p = src
    · rw [if_pos e]; omega
    · rw [if_neg e]
      rcases hI.par src p hs hp hps with e' | ⟨q, e', hq, _, _⟩
      · omega
      · have hqs : q ≠ src := fun e'' => e (Or.inr (by rw [e', e'']))
        rw [e', Int.toNat_natCast]
        have := nrank_lt r N p q hq (hr p q hp hps e' hqs)
        omega

theorem ch_exit (W : Nat → Nat → Int) (S : St) (N src dst : Nat) (hI : PInv W N N S) (hs : src < N)
    (L : List Nat) (h : Ch W S N src dst L src) (hne : src ≠ dst) :
    L.reverse.getLast? = some dst ∧ (∀ y ∈ L.reverse, y < N) ∧ ww W (src :: L.reverse) ≤ S.D src dst := by
  obtain ⟨hL, hc⟩ := h
  rcases hc with ⟨_, e⟩ | ⟨hh, x, L', rfl, e, hb⟩
  · exact absurd (by exact_mod_cast e) hne
  · refine ⟨by rw [List.getLast?_reverse]; exact hh, fun y hy => (hL y (by simp at hy ⊢; tauto)).1, ?_⟩
    have hx := hL x (by simp)
    rcases hI.par src x hs hx.1 hx.2 with e' | ⟨q, e', _, h3, _⟩
    · rw [← e] at e'; omega
    · have : q = src := by rw [← e] at e'; exact_mod_cast e'.symm
      have := h3 this
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hb ⊢
      simp only [ww] at hb ⊢
      omega

theorem get_shortest_path_spec (g : cp.MatrixGraph Int) (W : Nat → Nat → Int) (S : St) (hn : 0 ≤ g.n)
    (hsmall : g.n < 2 ^ 31) (hP : Rep g.n.toNat g.shortest_path_parent S.P) (hI : PInv W g.n.toNat g.n.toNat S)
    (src dst : Nat) (hs : src < g.n.toNat) (hd : dst < g.n.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.MatrixGraph.get_shortest_path g src dst
    ⦃⇓ r c => ⌜r.2 = g ∧ (src = dst → r.1.toList = [(src : Int)]) ∧
      (src ≠ dst → r.1 = ([] : List Int).toArray ∨ ∃ R : List Nat, r.1.toList = (src :: R).map (fun v : Nat => (v : Int)) ∧
        R.getLast? = some dst ∧ (∀ y ∈ R, y < g.n.toNat) ∧ ww W (src :: R) ≤ S.D src dst) ∧
      c ≤ t0 + 4 * g.n.toNat + 10⌝⦄ := by
  obtain ⟨r, hr⟩ := hI.rank src hs
  mvcgen [cp.MatrixGraph.get_shortest_path]
  case vc1.inv =>
    exact ⟨fun ⟨o, path, cur⟩ c => ⌜o = none ∧ ∃ L : List Nat, path.toList = L.map (fun v : Nat => (v : Int)) ∧
             Ch W S g.n.toNat src dst L cur ∧ L.length + meas r g.n.toNat src cur ≤ g.n.toNat + 1 ∧
             c = t0 + 1 + 2 * L.length⌝,
           fun ⟨o, path, cur⟩ c => ⌜(o = none ∧ cur = src ∧ ∃ L : List Nat,
               path.toList = L.map (fun v : Nat => (v : Int)) ∧ Ch W S g.n.toNat src dst L cur ∧
               L.length ≤ g.n.toNat + 1 ∧ c = t0 + 2 + 2 * L.length) ∨
             (o = some (([] : List Int).toArray, g) ∧ src ≠ dst ∧ c ≤ t0 + 2 * g.n.toNat + 6)⌝,
           fun ⟨_, _, cur⟩ => meas r g.n.toNat src cur⟩
  all_goals simp +zetaDelta [fuel] at *
  case vc2.step.isTrue =>
    rename_i s1 h2 n0 m0 mat0 sd0 sp0 nc0 path1 cur1 b0 us0 path0 cur0 s0 h1 h0
    obtain ⟨-, L, hp, hch, hlen, hc⟩ := h1
    exact ⟨h0, L, hp, hch, by omega, by omega⟩
  case vc3.step.isFalse.isTrue =>
    rename_i s1 h3 n0 m0 mat0 sd0 sp0 nc0 path2 cur1 b0 us0 path1 cur0 s0 h2 path0 h1 h0
    obtain ⟨-, L, hp, ⟨hL, hc'⟩, hlen, hc⟩ := h2
    rcases hc' with ⟨_, e⟩ | ⟨hh, _⟩
    · rw [h0] at e; omega
    · refine ⟨fun e => ?_, by omega⟩
      cases L with
      | nil => simp at hh
      | cons a l =>
        simp at hh; subst hh
        exact (hL a (by simp)).2 e.symm
  case vc4.step.isFalse.isFalse =>
    rename_i s1 h3 n0 m0 mat0 sd0 sp0 nc0 path2 cur2 b0 us0 path1 cur1 s0 h2 path0 cur0 h1 h0
    obtain ⟨-, L, hp, hch, hlen, hc⟩ := h2
    have hs' : src < g.n.toNat := by omega
    have hd' : dst < g.n.toNat := by omega
    obtain ⟨h0c, hlt, hch', hm⟩ := ch_step W S _ src dst hI hs' hd' r
      (fun j p hj hjs e hps => hr j p (by omega) hjs e hps) L b0.2.2 hch h1 h0
    have hget : get g.shortest_path_parent[src]! b0.2.2 = S.P src b0.2.2.toNat := by
      rw [← hP.2.2 src _ hs' hlt]; rfl
    rw [hget]
    have hlen' : (L ++ [b0.2.2.toNat]).length + meas r g.n.toNat src (S.P src b0.2.2.toNat) ≤ g.n.toNat + 1 := by
      rw [List.length_append, List.length_singleton]
      have hlen2 : L.length + meas r g.n.toNat src b0.2.2 ≤ g.n.toNat + 1 := hlen
      omega
    refine ⟨⟨L ++ [b0.2.2.toNat], by rw [hp]; simp; omega, hch', hlen',
      by rw [List.length_append, List.length_singleton]; omega⟩, hm⟩
  case vc5.pre =>
    have := nrank_le r g.n.toNat dst
    refine ⟨⟨⟨fun y hy => by simp at hy, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩, ?_⟩ <;>
      (unfold meas; simp only [Int.toNat_natCast]; split <;> omega)
  case vc6.post.success.h_1 =>
    rename_i s1 h1 n0 m0 mat0 sd0 sp0 nc0 path1 cur0 r0 ur0 us0 path0 a0 x0 s0 h0
    rcases h0 with ⟨e, _⟩ | ⟨e, hne, hc⟩
    · rw [x0] at e; cases e
    · rw [x0] at e; cases e
      exact ⟨rfl, fun e => absurd e hne, fun _ => Or.inl rfl, by omega⟩
  case vc7.post.success.h_2 =>
    rename_i s1 h1 n0 m0 mat0 sd0 sp0 nc0 path3 cur0 r0 ur0 us0 path2 x0 s0 h0 path1 path0
    rcases h0 with ⟨-, hcur, L, hp, hch, hlen, hc⟩ | ⟨e, _⟩
    · rw [hcur] at hch
      have hsz : r0.2.1.size = L.length := by rw [← Array.length_toList, hp]; simp
      refine ⟨fun e => ?_, fun hne => ?_, by omega⟩
      · subst e
        cases L with
        | nil => exact Array.toList_eq_nil_iff.mp (by simpa using hp)
        | cons a l =>
          obtain ⟨hL, hc'⟩ := hch
          rcases hc' with ⟨e, _⟩ | ⟨hh, _⟩
          · cases e
          · simp at hh; subst hh; exact absurd rfl (hL a (by simp)).2
      · obtain ⟨h1', h2', h3'⟩ := ch_exit W S _ src dst hI (by omega) L hch hne
        refine ⟨L.reverse, by rw [hp, List.map_reverse], h1', fun y hy => by have := h2' y hy; omega, h3'⟩
    · rw [x0] at e; cases e

/-! ## The other members -/

/-- The diagonal loop of the constructor: the first `k` diagonal entries are `0`, the rest `UNREACHABLE`. -/
def I0 (k : Nat) : Nat → Nat → Int := fun p q => if p = q ∧ p < k then 0 else U

/-- `MatrixGraph(n)`: `mat` is `0` on the diagonal and `UNREACHABLE` elsewhere, no edge, nothing computed;
`3 + n (n + 3)` steps. -/
theorem init_spec (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.MatrixGraph.init (Cost := Int) n)
    ⦃⇓ r c => ⌜r.n = n ∧ r.m = 0 ∧ Rep n.toNat r.mat (fun p q => if p = q then 0 else U) ∧
      r.shortest_path_dist = ([] : List (Array Int)).toArray ∧ r.shortest_path_parent = ([] : List (Array Int)).toArray ∧ r.negative_cycle = false ∧
      c = t0 + 2 + n.toNat + n.toNat * (n.toNat + 1) + n.toNat⌝⦄ := by
  mvcgen [cp.MatrixGraph.init]
  case inv1 =>
    exact ⇓⟨xs, b⟩ c => ⌜Rep n.toNat b (I0 xs.prefix.length) ∧
      c = t0 + 2 + n.toNat + n.toNat * (n.toNat + 1) + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.step =>
    rename_i pref cur suff h b s hinv m'
    obtain ⟨rfl, hi⟩ := cur_of h
    refine ⟨rep_ext (rep_set _ _ _ hinv.1 _ _ hi hi _) (fun p q _ _ => ?_), by omega⟩
    unfold upd I0
    by_cases e : p = pref.length ∧ q = pref.length
    · obtain ⟨rfl, rfl⟩ := e; simp
    · rw [if_neg e]
      by_cases e2 : p = q
      · subst e2
        have : p ≠ pref.length := fun e' => e ⟨e', e'⟩
        simp only [true_and]; split <;> split <;> omega
      · simp [e2]
  case vc2.pre =>
    rename_i s h
    refine ⟨rep_ext (rep_replicate n hn U) (fun p q _ _ => by simp [I0]), by simp [replicate]; omega⟩
  case vc3.post.success =>
    rename_i r s h
    refine ⟨rep_ext h.1 (fun p q hp _ => ?_), by omega⟩
    unfold I0
    by_cases e : p = q
    · subst e; rw [if_pos ⟨rfl, hp⟩, if_pos rfl]
    · rw [if_neg (fun h' => e h'.1), if_neg e]

/-- `add_edge(from, to, cost)` sets `mat[from][to] = cost` and counts the edge; one step. -/
theorem add_edge_spec (g : cp.MatrixGraph Int) (W : Nat → Nat → Int) (hW : Rep g.n.toNat g.mat W) (src dst : Nat)
    (hs : src < g.n.toNat) (hd : dst < g.n.toNat) (cost : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.MatrixGraph.add_edge g src dst cost
    ⦃⇓ r c => ⌜r.n = g.n ∧ r.m = g.m + 1 ∧ Rep g.n.toNat r.mat (upd W src dst cost) ∧
      r.shortest_path_dist = g.shortest_path_dist ∧ r.shortest_path_parent = g.shortest_path_parent ∧
      r.negative_cycle = g.negative_cycle ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.MatrixGraph.add_edge]
  simp +zetaDelta at *
  exact ⟨rep_set _ _ _ hW _ _ (by omega) (by omega) _, by omega⟩

/-- `distance(from, to)` reads `shortest_path_dist[from][to]`; one step. -/
theorem distance_spec (g : cp.MatrixGraph Int) (src dst : Nat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.MatrixGraph.distance g src dst
    ⦃⇓ r c => ⌜r.1 = G g.shortest_path_dist src dst ∧ r.2 = g ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.MatrixGraph.distance]
  simp +zetaDelta [G, get_eq] at *
  omega

/-- `has_negative_cycle()` returns the flag; one step. -/
theorem has_negative_cycle_spec (g : cp.MatrixGraph Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.MatrixGraph.has_negative_cycle g
    ⦃⇓ r c => ⌜r = g.negative_cycle ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.MatrixGraph.has_negative_cycle]
  simp +zetaDelta at *
  omega

/-! ## What the results mean -/

/-- The distances after `warshall_floyd` (before replacing the large entries): each is the weight of a walk through
vertices `< n`; it is at most every walk with distinct vertices; without a negative closed walk it is at most every
walk (so it is the shortest walk weight); a diagonal entry is negative iff some closed walk is negative; and without
a negative closed walk the parents satisfy `PInv` (used by `get_shortest_path_spec`). -/
theorem fw_correct (N : Nat) (W : Nat → Nat → Int) :
    (∀ p q, p < N → q < N → ∃ l, Below N l ∧ (FW N W).D p q = wt W p l q) ∧
    (∀ p q, p < N → q < N → ∀ l, Below N l → l.Nodup → p ∉ l → q ∉ l → (FW N W).D p q ≤ wt W p l q) ∧
    (NoNeg W N → ∀ p q, p < N → q < N → ∀ l, Below N l → (FW N W).D p q ≤ wt W p l q) ∧
    ((∃ v, v < N ∧ (FW N W).D v v < 0) ↔ ¬ NoNeg W N) ∧
    (NoNeg W N → PInv W N N (FW N W)) := by
  refine ⟨fw_walk W N _, fw_le_simple W N _, fun hN => fw_le W N _ hN, neg_iff W N _, fun hN => ?_⟩
  refine pinv_fw W N _ hN (fun i j _ _ hji => ?_) N le_rfl
  unfold P0; split
  · rename_i h; exact Or.inr rfl
  · exact Or.inl rfl

/-- Without a negative closed walk, a nonempty result of `get_shortest_path` after `warshall_floyd` is a shortest
walk: `src → l → dst` with vertices `< n` and weight the distance (`fw_correct`). -/
theorem shortest_path_weight (N : Nat) (W : Nat → Nat → Int) (hN : NoNeg W N) (src dst : Nat) (hs : src < N)
    (hd : dst < N) (R : List Nat) (hR : R.getLast? = some dst) (hb : ∀ y ∈ R, y < N)
    (hw : ww W (src :: R) ≤ (FW N W).D src dst) :
    ∃ l, R = l ++ [dst] ∧ Below N l ∧ wt W src l dst = (FW N W).D src dst := by
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.mp hR
  have hl : Below N l := fun y hy => hb y (by simp [hy])
  rw [ww_wt] at hw
  exact ⟨l, rfl, hl, le_antisymm hw (fw_le W N _ hN src dst hs hd l hl)⟩

end Proofs.Cpp.GraphMatrix
