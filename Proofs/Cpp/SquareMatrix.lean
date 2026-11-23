import Proofs.Cpp.Gen.SquareMatrix
import Proofs.Cpp.Lib.Basic
import Proofs.Cpp.Lib.SquareMatrixMath

/-! # `SquareMatrix<T, n>` (library/number/square_matrix.hpp)

The C array `mat` is an `Array` of `n` rows of length `n` (`Wf`); `G m i j` is `mat[i][j]`. The element loops are
proved with the invariant `Fill` (entries before the cursor hold the new values, the others the old ones), the
product with partial sums `Sum k`, and `pow` with `R * Y^e` constant (`Proofs.Cpp.SquareMatrixMath`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.Cpp.SquareMatrixMath

namespace Proofs.Cpp.SquareMatrix

variable {T : Type}

/-- `a[i][j]`. -/
def G' [Inhabited T] (a : Array (Array T)) (i j : Nat) : T := (a[i]!)[j]!

/-- The entries of a matrix. -/
def G {n : Int} [Inhabited T] (m : cp.SquareMatrix T n) : Nat → Nat → T := G' m.mat

/-- `n` rows of length `n`. -/
def Wf (N : Nat) (a : Array (Array T)) : Prop := a.size = N ∧ ∀ i, i < N → (a[i]!).size = N

/-- `a[i][j] = v`. -/
def set2 (a : Array (Array T)) (i j : Int) (v : T) [Inhabited T] : Array (Array T) := Cpp.set a i (Cpp.set (Cpp.get a i) j v)

theorem set2_get [Inhabited T] (N : Nat) (a : Array (Array T)) (h : Wf N a) (i j : Int) (hi0 : 0 ≤ i) (hi : i.toNat < N)
    (hj0 : 0 ≤ j) (hj : j.toNat < N) (v : T) (p q : Nat) :
    G' (set2 a i j v) p q = if p = i.toNat ∧ q = j.toNat then v else G' a p q := by
  unfold G' set2
  rw [getElemBang_set _ _ _ _ (by rw [h.1]; exact hi)]
  by_cases hp : p = i.toNat
  · subst hp
    simp only [ite_true, get_eq]
    rw [getElemBang_set _ _ _ _ (by rw [h.2 _ hi]; exact hj)]
    by_cases hq : q = j.toNat <;> simp [hq]
  · simp [hp]

theorem set2_wf [Inhabited T] (N : Nat) (a : Array (Array T)) (h : Wf N a) (i j : Int) (hi0 : 0 ≤ i) (hi : i.toNat < N)
    (v : T) : Wf N (set2 a i j v) := by
  refine ⟨by simp [set2, h.1], fun p hp => ?_⟩
  unfold set2
  rw [getElemBang_set _ _ _ _ (by rw [h.1]; exact hi)]
  split
  · rename_i e; subst e; simp [get_eq, h.2 _ hi]
  · exact h.2 p hp

/-- The element loop: the entries before `(pi, pj)` (row by row) hold `f`, the others are those of `a0`. -/
def Fill [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat) : Prop :=
  Wf N a ∧ ∀ i j, i < N → j < N → G' a i j = if i < pi ∨ (i = pi ∧ j < pj) then f i j else G' a0 i j

theorem fill_start [Inhabited T] (N : Nat) (a0 : Array (Array T)) (h : Wf N a0) (f : Nat → Nat → T) :
    Fill N a0 a0 f 0 0 := ⟨h, fun i j _ _ => by simp⟩

theorem fill_step [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat)
    (h : Fill N a0 a f pi pj) (hi : pi < N) (hj : pj < N) :
    Fill N a0 (set2 a pi pj (f pi pj)) f pi (pj + 1) := by
  refine ⟨set2_wf N a h.1 pi pj (by omega) (by simpa using hi) _, fun i j hi' hj' => ?_⟩
  rw [set2_get N a h.1 pi pj (by omega) (by simpa using hi) (by omega) (by simpa using hj)]
  simp only [Int.toNat_natCast]
  by_cases e : i = pi ∧ j = pj
  · obtain ⟨rfl, rfl⟩ := e; simp
  · rw [if_neg e, h.2 i j hi' hj']
    by_cases h1 : i < pi ∨ i = pi ∧ j < pj
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem fill_row [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi : Nat)
    (h : Fill N a0 a f pi N) : Fill N a0 a f (pi + 1) 0 := by
  refine ⟨h.1, fun i j hi hj => ?_⟩
  rw [h.2 i j hi hj]
  by_cases h1 : i < pi ∨ i = pi ∧ j < N
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

theorem fill_done [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (h : Fill N a0 a f N 0) :
    Wf N a ∧ ∀ i j, i < N → j < N → G' a i j = f i j :=
  ⟨h.1, fun i j hi hj => by rw [h.2 i j hi hj, if_pos (by omega)]⟩

/-- A value read before it is written is the old one. -/
theorem fill_cur [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat)
    (h : Fill N a0 a f pi pj) (hi : pi < N) (hj : pj < N) : G' a pi pj = G' a0 pi pj := by
  rw [h.2 pi pj hi hj, if_neg (by omega)]

theorem cursor_len (n : Int) (pre suf : List Int) (c : Int) (h : range 0 n = pre ++ c :: suf) :
    c = pre.length ∧ pre.length < n.toNat := by
  have e := range_cursor h
  have hl := congrArg List.length h
  rw [range_length] at hl
  simp at hl e
  exact ⟨e, by omega⟩

theorem fill_vc [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (po so pi si : List Int)
    (co ci : Int) (ho : range 0 n = po ++ co :: so) (hi : range 0 n = pi ++ ci :: si)
    (h : Fill n.toNat a0 a f po.length pi.length) (v : T) (hv : v = f po.length pi.length) :
    Fill n.toNat a0 (Cpp.set a co (Cpp.set (Cpp.get a co) ci v)) f po.length (pi.length + 1) := by
  obtain ⟨e1, l1⟩ := cursor_len n po so co ho
  obtain ⟨e2, l2⟩ := cursor_len n pi si ci hi
  subst e1 e2 hv
  exact fill_step n.toNat a0 a f _ _ h l1 l2

theorem fill_cur_vc [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (po so pi si : List Int)
    (co ci : Int) (ho : range 0 n = po ++ co :: so) (hi : range 0 n = pi ++ ci :: si)
    (h : Fill n.toNat a0 a f po.length pi.length) : get (get a co) ci = G' a0 po.length pi.length := by
  obtain ⟨e1, l1⟩ := cursor_len n po so co ho
  obtain ⟨e2, l2⟩ := cursor_len n pi si ci hi
  subst e1 e2
  rw [← fill_cur n.toNat a0 a f _ _ h l1 l2]
  rfl

theorem get2_vc [Inhabited T] (n : Int) (a : Array (Array T)) (po so pi si : List Int)
    (co ci : Int) (ho : range 0 n = po ++ co :: so) (hi : range 0 n = pi ++ ci :: si) :
    get (get a co) ci = G' a po.length pi.length := by
  obtain ⟨e1, -⟩ := cursor_len n po so co ho
  obtain ⟨e2, -⟩ := cursor_len n pi si ci hi
  subst e1 e2
  rfl

theorem add_assign_spec [Inhabited T] [Add T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_add_assign a b
    ⦃⇓ r c => ⌜r.1 = r.2 ∧ Wf n.toNat r.2.mat ∧
      (∀ i j, i < n.toNat → j < n.toNat → G r.2 i j = G a i j + G b i j) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  mvcgen [cp.SquareMatrix.op_add_assign]
  case inv1 => exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (fun i j => G a i j + G b i j) xs.prefix.length 0 ∧
    c = t0 + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (fun i j => G a i j + G b i j) pi.length xs.prefix.length ∧
      c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi m _ H _
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n a.mat m _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    rw [fill_cur_vc n a.mat m _ po so pi si co ci ho hi hF, get2_vc n b.mat po so pi si co ci ho hi]; rfl
  case vc2.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc3.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc5.pre => exact ⟨fill_start _ _ ha _, by omega⟩
  case vc6.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    obtain ⟨hW, hG⟩ := fill_done _ _ _ _ hF
    exact ⟨hW, fun i j hi hj => hG i j (by omega) (by omega), hc⟩

theorem sub_assign_spec [Inhabited T] [Sub T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_sub_assign a b
    ⦃⇓ r c => ⌜r.1 = r.2 ∧ Wf n.toNat r.2.mat ∧
      (∀ i j, i < n.toNat → j < n.toNat → G r.2 i j = G a i j - G b i j) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  mvcgen [cp.SquareMatrix.op_sub_assign]
  case inv1 => exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (fun i j => G a i j - G b i j) xs.prefix.length 0 ∧
    c = t0 + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (fun i j => G a i j - G b i j) pi.length xs.prefix.length ∧
      c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi m _ H _
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n a.mat m _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    rw [fill_cur_vc n a.mat m _ po so pi si co ci ho hi hF, get2_vc n b.mat po so pi si co ci ho hi]; rfl
  case vc2.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc3.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc5.pre => exact ⟨fill_start _ _ ha _, by omega⟩
  case vc6.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    obtain ⟨hW, hG⟩ := fill_done _ _ _ _ hF
    exact ⟨hW, fun i j hi hj => hG i j (by omega) (by omega), hc⟩

theorem replicate_wf [Inhabited T] (n : Int) (hn : 0 ≤ n) (x : T) :
    Wf n.toNat (Cpp.replicate n (Cpp.replicate n x)) := by
  refine ⟨by simp [replicate], fun i hi => ?_⟩
  simp only [replicate]
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

/-- The loops of `O()`, `I()` and unary `-`: the entries of a default-initialized matrix are written once each with
`f`, which does not read the target. -/
theorem fill_vc0 [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (po so pi si : List Int)
    (co ci : Int) (ho : range 0 n = po ++ co :: so) (hi : range 0 n = pi ++ ci :: si)
    (h : Fill n.toNat a0 a f po.length pi.length) (v : Int → Int → T) (hv : ∀ p q : Nat, v p q = f p q) :
    Fill n.toNat a0 (Cpp.set a co (Cpp.set (Cpp.get a co) ci (v co ci))) f po.length (pi.length + 1) := by
  obtain ⟨e1, -⟩ := cursor_len n po so co ho
  obtain ⟨e2, -⟩ := cursor_len n pi si ci hi
  have := fill_vc n a0 a f po so pi si co ci ho hi h (v co ci) (by rw [e1, e2, hv])
  exact this

theorem neg_spec [Inhabited T] [Neg T] (n : Int) (hn : 0 ≤ n) (a : cp.SquareMatrix T n) (ha : Wf n.toNat a.mat)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_sub a
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = -G a i j) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  have h0 := replicate_wf n hn (default : T)
  mvcgen [cp.SquareMatrix.op_sub]
  case inv1 =>
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun i j => -G a i j) xs.prefix.length 0 ∧
        c = t0 + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun i j => -G a i j) pi.length
          xs.prefix.length ∧ c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi m _ H _
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n _ m.mat _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    rw [get2_vc n a.mat po so pi si co ci ho hi]; rfl
  case vc2.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc3.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc5.pre => exact ⟨fill_start _ _ h0 _, by omega⟩
  case vc6.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    obtain ⟨hW, hG⟩ := fill_done _ _ _ _ hF
    exact ⟨hW, fun i j hi hj => hG i j (by omega) (by omega), hc⟩

theorem zero_spec [Inhabited T] [Zero T] (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.SquareMatrix.O (n := n) : Cpp.M (cp.SquareMatrix T n))
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = 0) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  have h0 := replicate_wf n hn (default : T)
  mvcgen [cp.SquareMatrix.O]
  case inv1 =>
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun _ _ => (0 : T)) xs.prefix.length 0 ∧
        c = t0 + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun _ _ => (0 : T)) pi.length
          xs.prefix.length ∧ c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  all_goals simp +zetaDelta [range_length] at *
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi m _ H _
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n _ m.mat _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    rfl
  case vc2.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc3.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc5.pre => exact ⟨fill_start _ _ h0 _, by omega⟩
  case vc6.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    obtain ⟨hW, hG⟩ := fill_done _ _ _ _ hF
    exact ⟨hW, fun i j hi hj => hG i j (by omega) (by omega), hc⟩

theorem one_spec [Inhabited T] [IntCast T] (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.SquareMatrix.I (n := n) : Cpp.M (cp.SquareMatrix T n))
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = ((if i = j then 1 else 0 : Int) : T)) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  have h0 := replicate_wf n hn (default : T)
  mvcgen [cp.SquareMatrix.I]
  case inv1 =>
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun i j => ((if i = j then 1 else 0 : Int) : T)) xs.prefix.length 0 ∧
        c = t0 + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c =>
      ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) m.mat (fun i j => ((if i = j then 1 else 0 : Int) : T)) pi.length
          xs.prefix.length ∧ c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi m _ H _
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n _ m.mat _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    obtain ⟨e1, -⟩ := cursor_len n po so co ho
    obtain ⟨e2, -⟩ := cursor_len n pi si ci hi
    subst e1 e2
    simp
  all_goals simp +zetaDelta [range_length] at *
  case vc2.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc3.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc5.pre => exact ⟨fill_start _ _ h0 _, by omega⟩
  case vc6.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    obtain ⟨hW, hG⟩ := fill_done _ _ _ _ hF
    exact ⟨hW, fun i j hi hj => hG i j (by omega) (by omega), hc⟩

/-- `Fill` with the cell `(pi, pj)` holding `s` (the partial sum of the product). -/
def FillK [Inhabited T] (N : Nat) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat) (s : T) : Prop :=
  Wf N a ∧ ∀ i j, i < N → j < N →
    G' a i j = if i = pi ∧ j = pj then s else if i < pi ∨ (i = pi ∧ j < pj) then f i j else G' a0 i j

theorem fillk_start [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (po so pi si : List Int)
    (co ci : Int) (ho : range 0 n = po ++ co :: so) (hi : range 0 n = pi ++ ci :: si)
    (h : Fill n.toNat a0 a f po.length pi.length) (z : T) :
    FillK n.toNat a0 (Cpp.set a co (Cpp.set (Cpp.get a co) ci z)) f po.length pi.length z := by
  obtain ⟨e1, l1⟩ := cursor_len n po so co ho
  obtain ⟨e2, l2⟩ := cursor_len n pi si ci hi
  subst e1 e2
  refine ⟨set2_wf _ a h.1 _ _ (by omega) (by simpa using l1) z, fun i j hi' hj' => ?_⟩
  have := set2_get _ a h.1 po.length pi.length (by omega) (by simpa using l1) (by omega) (by simpa using l2) z i j
  simp only [Int.toNat_natCast] at this
  unfold set2 at this
  rw [this]
  by_cases e : i = po.length ∧ j = pi.length
  · simp only [e, and_self, ite_true]
  · simp only [e, ite_false]
    exact h.2 i j hi' hj'

theorem fillk_step [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat) (s v : T)
    (hp : pi < n.toNat) (hq : pj < n.toNat) (h : FillK n.toNat a0 a f pi pj s) :
    FillK n.toNat a0 (Cpp.set a pi (Cpp.set (Cpp.get a pi) pj v)) f pi pj v := by
  refine ⟨set2_wf _ a h.1 _ _ (by omega) (by simpa using hp) v, fun i j hi' hj' => ?_⟩
  have := set2_get _ a h.1 pi pj (by omega) (by simpa using hp) (by omega) (by simpa using hq) v i j
  simp only [Int.toNat_natCast] at this
  unfold set2 at this
  rw [this]
  by_cases e : i = pi ∧ j = pj
  · simp only [e, and_self, ite_true]
  · simp only [e, ite_false]
    rw [h.2 i j hi' hj']
    simp only [e, ite_false]

theorem fillk_cur [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat) (s : T)
    (hp : pi < n.toNat) (hq : pj < n.toNat) (h : FillK n.toNat a0 a f pi pj s) : G' a pi pj = s := by
  rw [h.2 pi pj hp hq, if_pos ⟨rfl, rfl⟩]

theorem fillk_done [Inhabited T] (n : Int) (a0 a : Array (Array T)) (f : Nat → Nat → T) (pi pj : Nat)
    (h : FillK n.toNat a0 a f pi pj (f pi pj)) : Fill n.toNat a0 a f pi (pj + 1) := by
  refine ⟨h.1, fun i j hi hj => ?_⟩
  rw [h.2 i j hi hj]
  by_cases e : i = pi ∧ j = pj
  · obtain ⟨rfl, rfl⟩ := e; simp
  · rw [if_neg e]
    by_cases h1 : i < pi ∨ i = pi ∧ j < pj
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem fillk_vc [Inhabited T] [Zero T] [Add T] [Mul T] (n : Int) (a0 a A B : Array (Array T)) (f : Nat → Nat → T)
    (po so pi si pk sk : List Int) (co ci ck : Int) (ho : range 0 n = po ++ co :: so)
    (hi : range 0 n = pi ++ ci :: si) (hk : range 0 n = pk ++ ck :: sk)
    (h : FillK n.toNat a0 a f po.length pi.length (Sum pk.length (fun k => G' A po.length k * G' B k pi.length))) :
    FillK n.toNat a0 (Cpp.set a co (Cpp.set (Cpp.get a co) ci (get (get a co) ci + get (get A co) ck * get (get B ck) ci)))
      f po.length pi.length (Sum (pk.length + 1) (fun k => G' A po.length k * G' B k pi.length)) := by
  obtain ⟨e1, l1⟩ := cursor_len n po so co ho
  obtain ⟨e2, l2⟩ := cursor_len n pi si ci hi
  obtain ⟨e3, l3⟩ := cursor_len n pk sk ck hk
  subst e1 e2 e3
  have hc := fillk_cur n a0 a f _ _ _ l1 l2 h
  have hs : Sum (pk.length + 1) (fun k => G' A po.length k * G' B k pi.length) =
      get (get a (po.length : Int)) (pi.length : Int) +
        get (get A (po.length : Int)) (pk.length : Int) * get (get B (pk.length : Int)) (pi.length : Int) := by
    rw [Sum_succ, ← hc]; rfl
  rw [hs]
  exact fillk_step n a0 a f po.length pi.length _ _ l1 l2 h

theorem mul_assign_spec [Inhabited T] [Zero T] [Add T] [Mul T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_mul_assign a b
    ⦃⇓ r c => ⌜r.1 = r.2 ∧ Wf n.toNat r.2.mat ∧
      (∀ i j, i < n.toNat → j < n.toNat → G r.2 i j = mulF n.toNat (G a) (G b) i j) ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat * (1 + n.toNat)) + n.toNat * (1 + n.toNat)⌝⦄ := by
  have h0 := replicate_wf n hn (default : T)
  mvcgen [cp.SquareMatrix.op_mul_assign]
  case inv1 =>
    exact ⇓⟨xs, t⟩ c => ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) t.mat
      (mulF n.toNat (G a) (G b)) xs.prefix.length 0 ∧
      c = t0 + 1 + xs.prefix.length * (1 + n.toNat * (1 + n.toNat))⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, t⟩ c => ⌜Fill n.toNat (Cpp.replicate n (Cpp.replicate n default)) t.mat
      (mulF n.toNat (G a) (G b)) pi.length xs.prefix.length ∧
      c = t0 + 1 + pi.length * (1 + n.toNat * (1 + n.toNat)) + 1 + xs.prefix.length * (1 + n.toNat)⌝
  case inv3 =>
    rename_i pi _ _ _ _ _ _ pj _ _ _ _ _ _ _
    exact ⇓⟨xs, t⟩ c => ⌜FillK n.toNat (Cpp.replicate n (Cpp.replicate n default)) t.mat
      (mulF n.toNat (G a) (G b)) pi.length pj.length (Sum xs.prefix.length (fun k => G a pi.length k * G b k pj.length)) ∧
      c = t0 + 1 + pi.length * (1 + n.toNat * (1 + n.toNat)) + 1 + pj.length * (1 + n.toNat) + 1 +
        xs.prefix.length⌝
  case inv4 =>
    rename_i tt _ _
    exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (G' tt.mat) xs.prefix.length 0 ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat * (1 + n.toNat)) + xs.prefix.length * (1 + n.toNat)⌝
  case inv5 =>
    rename_i tt _ _ pi _ _ _ _ _ _
    exact ⇓⟨xs, m⟩ c => ⌜Fill n.toNat a.mat m (G' tt.mat) pi.length xs.prefix.length ∧
      c = t0 + 1 + n.toNat * (1 + n.toNat * (1 + n.toNat)) + pi.length * (1 + n.toNat) + 1 + xs.prefix.length⌝
  case vc1.step =>
    rename_i po co so ho _ _ _ pi ci si hi _ _ _ _ pk ck sk hk t _ H _
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨hF, hc⟩ := H
    exact ⟨fillk_vc n _ t.mat a.mat b.mat _ po so pi si pk sk co ci ck ho hi hk hF, by omega⟩
  case vc2.step.pre =>
    rename_i po co so ho _ _ _ pi ci si hi t _ H _
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨hF, hc⟩ := H
    refine ⟨fillk_start n _ t.mat _ po so pi si co ci ho hi hF 0, by omega⟩
  case vc3.step.post.success =>
    rename_i po co so ho _ _ _ pi ci si hi _ _ _ _ t _ H
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨hF, hc⟩ := H
    obtain ⟨-, l1⟩ := cursor_len n po so co ho
    obtain ⟨-, l2⟩ := cursor_len n pi si ci hi
    refine ⟨fillk_done n _ t.mat _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc9.step =>
    rename_i tt _ _ po co so ho _ _ _ pi ci si hi m _ H _
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨hF, hc⟩ := H
    refine ⟨fill_vc n a.mat m _ po so pi si co ci ho hi hF _ ?_, by omega⟩
    rw [get2_vc n tt.mat po so pi si co ci ho hi]
  all_goals simp +zetaDelta [range_length] at *
  case vc5.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc6.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc8.pre => exact ⟨fill_start _ _ h0 _, by omega⟩
  case vc10.step.pre => exact ⟨‹_ ∧ _›.1, by have := ‹_ ∧ _›.2; omega⟩
  case vc11.step.post.success =>
    obtain ⟨hF, hc⟩ := ‹Fill _ a.mat _ _ _ _ ∧ _›
    refine ⟨fill_row _ _ _ _ _ hF, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  case vc13.post.success.pre =>
    obtain ⟨-, hc⟩ := ‹Fill _ _ _ _ _ _ ∧ _›
    exact ⟨fill_start _ _ ha _, by omega⟩
  case vc14.post.success.post.success =>
    obtain ⟨hF2, hc⟩ := ‹Fill _ a.mat _ _ _ _ ∧ _›
    obtain ⟨hF1, -⟩ := ‹Fill _ (Cpp.replicate _ _) _ _ _ _ ∧ _›
    obtain ⟨hW2, hG2⟩ := fill_done _ _ _ _ hF2
    obtain ⟨-, hG1⟩ := fill_done _ _ _ _ hF1
    refine ⟨hW2, fun i j hi hj => ?_, hc⟩
    show G' _ i j = _
    rw [hG2 i j (by omega) (by omega), hG1 i j (by omega) (by omega)]

theorem add_spec [Inhabited T] [Add T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_add_SquareMatrix_SquareMatrix a b
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = G a i j + G b i j) ∧
      c = t0 + 2 + n.toNat * n.toNat + n.toNat * (1 + n.toNat)⌝⦄ := by
  have W := fun (Q : PostCond ((cp.SquareMatrix T n) × (cp.SquareMatrix T n)) PS) =>
    wp_of_triple (Q := Q) (fun t => add_assign_spec n hn a b ha hb t)
  mvcgen [cp.op_add_SquareMatrix_SquareMatrix, W]
  all_goals simp +zetaDelta at *
  intro r1 r2 c e h2 h3 hc
  subst e
  exact ⟨h2, h3, by omega⟩

theorem sub_spec [Inhabited T] [Sub T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_sub_SquareMatrix_SquareMatrix a b
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = G a i j - G b i j) ∧
      c = t0 + 2 + n.toNat * n.toNat + n.toNat * (1 + n.toNat)⌝⦄ := by
  have W := fun (Q : PostCond ((cp.SquareMatrix T n) × (cp.SquareMatrix T n)) PS) =>
    wp_of_triple (Q := Q) (fun t => sub_assign_spec n hn a b ha hb t)
  mvcgen [cp.op_sub_SquareMatrix_SquareMatrix, W]
  all_goals simp +zetaDelta at *
  intro r1 r2 c e h2 h3 hc
  subst e
  exact ⟨h2, h3, by omega⟩

theorem mul_spec [Inhabited T] [Zero T] [Add T] [Mul T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (hb : Wf n.toNat b.mat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_mul_SquareMatrix_SquareMatrix a b
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ (∀ i j, i < n.toNat → j < n.toNat → G r i j = mulF n.toNat (G a) (G b) i j) ∧
      c = t0 + 2 + n.toNat * n.toNat + n.toNat * (1 + n.toNat * (1 + n.toNat)) + n.toNat * (1 + n.toNat)⌝⦄ := by
  have W := fun (Q : PostCond ((cp.SquareMatrix T n) × (cp.SquareMatrix T n)) PS) =>
    wp_of_triple (Q := Q) (fun t => mul_assign_spec n hn a b ha hb t)
  mvcgen [cp.op_mul_SquareMatrix_SquareMatrix, W]
  all_goals simp +zetaDelta at *
  intro r1 r2 c e h2 h3 hc
  subst e
  exact ⟨h2, h3, by omega⟩

theorem pos_spec (n : Int) (a : cp.SquareMatrix T n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_add a ⦃⇓ r c => ⌜r = a ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.SquareMatrix.op_add]
  all_goals simp +zetaDelta at *
  all_goals omega

theorem index_spec [Inhabited T] (n : Int) (a : cp.SquareMatrix T n) (i : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_index_int a i ⦃⇓ r c => ⌜r.1 = a.mat[i.toNat]! ∧ r.2 = a ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.SquareMatrix.op_index_int]
  all_goals simp +zetaDelta [get] at *
  all_goals omega

theorem index_const_spec [Inhabited T] (n : Int) (a : cp.SquareMatrix T n) (i : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.op_index_int_const a i ⦃⇓ r c => ⌜r = a.mat[i.toNat]! ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.SquareMatrix.op_index_int_const]
  all_goals simp +zetaDelta [get] at *
  all_goals omega

theorem eq_spec [Inhabited T] [DecidableEq T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_eq_SquareMatrix_SquareMatrix a b
    ⦃⇓ r c => ⌜(r = true ↔ ∀ i j, i < n.toNat → j < n.toNat → G a i j = G b i j) ∧
      c ≤ t0 + 1 + n.toNat * (1 + n.toNat)⌝⦄ := by
  mvcgen [cp.op_eq_SquareMatrix_SquareMatrix]
  case inv1 =>
    exact ⇓⟨xs, r⟩ c => ⌜(r.1 = none ∧ (∀ i j, i < xs.prefix.length → j < n.toNat → G a i j = G b i j) ∧
        c = t0 + 1 + xs.prefix.length * (1 + n.toNat)) ∨
      (r.1 = some false ∧ xs.suffix = [] ∧ (∃ i j, i < n.toNat ∧ j < n.toNat ∧ G a i j ≠ G b i j) ∧
        c ≤ t0 + 1 + n.toNat * (1 + n.toNat))⌝
  case inv2 =>
    rename_i pi _ _ _ _ _ _
    exact ⇓⟨xs, r⟩ c => ⌜(r.1 = none ∧
        (∀ i j, (i < pi.length ∨ (i = pi.length ∧ j < xs.prefix.length)) → i < n.toNat → j < n.toNat →
          G a i j = G b i j) ∧
        c = t0 + 1 + pi.length * (1 + n.toNat) + 1 + xs.prefix.length) ∨
      (r.1 = some false ∧ xs.suffix = [] ∧ (∃ i j, i < n.toNat ∧ j < n.toNat ∧ G a i j ≠ G b i j) ∧
        c ≤ t0 + 1 + (pi.length + 1) * (1 + n.toNat))⌝
  case vc1.step.isTrue =>
    rename_i po co so ho _ _ _ pi ci si hi st s H hne
    simp +zetaDelta [range_length] at H hne ⊢
    obtain ⟨-, l1⟩ := cursor_len n po so co ho
    obtain ⟨-, l2⟩ := cursor_len n pi si ci hi
    rw [get2_vc n a.mat po so pi si co ci ho hi, get2_vc n b.mat po so pi si co ci ho hi] at hne
    refine ⟨⟨po.length, by omega, pi.length, by omega, hne⟩, ?_⟩
    obtain ⟨-, -, hc⟩ := H
    rw [Nat.add_mul, Nat.one_mul]; omega
  case vc2.step.isFalse =>
    rename_i po co so ho _ _ _ pi ci si hi st s H heq
    simp +zetaDelta [range_length] at H heq ⊢
    rw [get2_vc n a.mat po so pi si co ci ho hi, get2_vc n b.mat po so pi si co ci ho hi] at heq
    obtain ⟨-, hE, hc⟩ := H
    refine ⟨fun i j hij hi' hj' => ?_, by omega⟩
    by_cases e : i = po.length ∧ j = pi.length
    · obtain ⟨rfl, rfl⟩ := e; exact heq
    · exact hE i j (by omega) hi' hj'
  case vc3.step.pre =>
    rename_i po co so ho st s H
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨-, hE, hc⟩ := H
    exact ⟨fun i j hij hi' hj' => hE i j hij hj', by omega⟩
  case vc4.step.post.success.h_1 =>
    rename_i po co so ho _ _ _ r x hx s H
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨-, l1⟩ := cursor_len n po so co ho
    rcases H with ⟨hr, -⟩ | ⟨hr, hm, hc⟩
    · rw [hr] at hx; simp at hx
    · rw [hx] at hr
      simp at hr
      refine ⟨hr, hm, ?_⟩
      have : (po.length + 1) * (1 + n.toNat) ≤ n.toNat * (1 + n.toNat) := Nat.mul_le_mul_right _ (by omega)
      omega
  case vc5.step.post.success.h_2 =>
    rename_i po co so ho _ _ _ r hx s H
    simp +zetaDelta [range_length] at H ⊢
    obtain ⟨-, l1⟩ := cursor_len n po so co ho
    rcases H with ⟨-, hE, hc⟩ | ⟨hr, -⟩
    · refine ⟨fun i j hij hj' => hE i j (by omega) (by omega) hj', by rw [Nat.add_mul, Nat.one_mul]; omega⟩
    · rw [hx] at hr; simp at hr
  case vc8.post.success.h_1 =>
    rename_i r x hx s H
    simp +zetaDelta [range_length] at H ⊢
    rcases H with ⟨hr, -⟩ | ⟨hr, ⟨i, hi, j, hj, hm⟩, hc⟩
    · rw [hr] at hx; simp at hx
    · rw [hx] at hr
      simp at hr
      subst hr
      refine ⟨⟨fun h => absurd h (by simp), fun h => absurd (h i j hi hj) hm⟩, hc⟩
  case vc9.post.success.h_2 =>
    rename_i r hx s H
    simp +zetaDelta [range_length] at H ⊢
    rcases H with ⟨-, hE, hc⟩ | ⟨hr, -⟩
    · exact ⟨hE, by omega⟩
    · rw [hx] at hr; simp at hr
  all_goals simp_all

theorem ne_spec [Inhabited T] [DecidableEq T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_ne_SquareMatrix_SquareMatrix a b
    ⦃⇓ r c => ⌜(r = true ↔ ¬ ∀ i j, i < n.toNat → j < n.toNat → G a i j = G b i j) ∧
      c ≤ t0 + 2 + n.toNat * (1 + n.toNat)⌝⦄ := by
  have W := fun (Q : PostCond Bool PS) => wp_of_triple (Q := Q) (fun t => eq_spec n hn a b t)
  mvcgen [cp.op_ne_SquareMatrix_SquareMatrix, W]
  all_goals simp +zetaDelta at *
  refine ⟨fun c i hi j hj hm hc => ⟨⟨i, hi, j, hj, hm⟩, by omega⟩, fun c hE hc => ⟨fun i hi j hj => hE i j hi hj, by omega⟩⟩

theorem shr_one (x : Int) : shr x 1 = x / 2 := by simp [shr, Int.shiftRight_eq_div_pow]

theorem land_one (x : Int) (hx : 0 ≤ x) : land x 1 = x % 2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp [land]

theorem mul_assign_wp [Inhabited T] [Zero T] [Add T] [Mul T] (n : Int) (hn : 0 ≤ n) (a b : cp.SquareMatrix T n)
    {Q : PostCond ((cp.SquareMatrix T n) × (cp.SquareMatrix T n)) PS} :
    ⦃fun t => ⌜Wf n.toNat a.mat ∧ Wf n.toNat b.mat ∧ ∀ r c, (r.1 = r.2 ∧ Wf n.toNat r.2.mat ∧
      (∀ i j, i < n.toNat → j < n.toNat → G r.2 i j = mulF n.toNat (G a) (G b) i j) ∧
      c = t + 1 + n.toNat * (1 + n.toNat * (1 + n.toNat)) + n.toNat * (1 + n.toNat)) → (Q.1 r c).down⌝⦄
    cp.SquareMatrix.op_mul_assign a b ⦃Q⦄ := by
  apply Triple.iff.mpr
  intro t ht
  simp only [SPred.down_pure] at ht
  obtain ⟨ha, hb, hQ⟩ := ht
  obtain ⟨res, c, hrun, hp⟩ := run_of_triple (mul_assign_spec n hn a b ha hb t)
  simp [wp, hrun]
  exact hQ res c hp

theorem round_eq [Semiring T] (N : Nat) (R Y R' Y' : Nat → Nat → T) (e : Nat)
    (hR : EqOn N R' (if e % 2 = 1 then mulF N R Y else R)) (hY : e / 2 ≠ 0 → EqOn N Y' (mulF N Y Y)) :
    EqOn N (mulF N R' (PW N Y' (e / 2))) (mulF N R (PW N Y e)) := by
  have hP : EqOn N (PW N Y' (e / 2)) (PW N (mulF N Y Y) (e / 2)) := by
    by_cases h : e / 2 = 0
    · rw [h]; exact EqOn_refl N _
    · exact PW_congr N _ _ (hY h) _
  exact EqOn_trans (mulF_congr N _ _ _ _ hR hP) (pow_round N R Y e)

/-- The ticks of one `*=` on `n x n` matrices. -/
abbrev Kmul (N : Nat) : Nat := 1 + N * (1 + N * (1 + N)) + N * (1 + N)

theorem step_ok [Inhabited T] [Ring T] (n : Int) (a : cp.SquareMatrix T n) (e0 : Nat) (B : Nat) (E : Int)
    (Y R Y' R' : cp.SquareMatrix T n) (t t' : Nat) (hE : 0 ≤ E) (hne : E ≠ 0)
    (hinv : EqOn n.toNat (mulF n.toNat (G R) (PW n.toNat (G Y) E.toNat)) (PW n.toNat (G a) e0))
    (hc : t + bitWidth E.toNat * (1 + 2 * Kmul n.toNat) ≤ B)
    (hR' : EqOn n.toNat (G R') (if E.toNat % 2 = 1 then mulF n.toNat (G R) (G Y) else G R))
    (hY' : E.toNat / 2 ≠ 0 → EqOn n.toNat (G Y') (mulF n.toNat (G Y) (G Y)))
    (ht' : t' ≤ t + 1 + 2 * Kmul n.toNat) :
    0 ≤ E / 2 ∧ EqOn n.toNat (mulF n.toNat (G R') (PW n.toNat (G Y') (E / 2).toNat)) (PW n.toNat (G a) e0) ∧
      t' + bitWidth (E / 2).toNat * (1 + 2 * Kmul n.toNat) ≤ B ∧ E / 2 < E ∧ 0 < E := by
  have hd : (E / 2).toNat = E.toNat / 2 := by omega
  refine ⟨by omega, ?_, ?_, by omega, by omega⟩
  · rw [hd]
    exact EqOn_trans (round_eq n.toNat (G R) (G Y) (G R') (G Y') E.toNat hR' hY') hinv
  · rw [hd]
    have hb := bitWidth_div_two E.toNat (by omega)
    have : (bitWidth (E.toNat / 2) + 1) * (1 + 2 * Kmul n.toNat) = bitWidth E.toNat * (1 + 2 * Kmul n.toNat) := by
      rw [hb]
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem pow_spec [Inhabited T] [Ring T] (n : Int) (hn : 0 ≤ n) (a : cp.SquareMatrix T n)
    (ha : Wf n.toNat a.mat) (e : Int) (he : 0 ≤ e) (he' : e < 2 ^ 63) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.SquareMatrix.pow a e
    ⦃⇓ r c => ⌜Wf n.toNat r.mat ∧ EqOn n.toNat (G r) (PW n.toNat (G a) e.toNat) ∧
      c ≤ t0 + 3 + n.toNat * (1 + n.toNat) + bitWidth e.toNat * (1 + 2 * Kmul n.toNat)⌝⦄ := by
  have WI := fun (Q : PostCond (cp.SquareMatrix T n) PS) =>
    wp_of_triple (Q := Q) (fun t => one_spec (T := T) n hn t)
  have WM := fun (x y : cp.SquareMatrix T n) (Q : PostCond ((cp.SquareMatrix T n) × (cp.SquareMatrix T n)) PS) =>
    mul_assign_wp n hn x y (Q := Q)
  mvcgen [cp.SquareMatrix.pow, WI, WM]
  case vc1.isTrue =>
    intro r0 c0 hW0 hG0 hc0
    mvcgen [WM]
    case inv =>
      exact ⟨fun b t => ⌜0 ≤ b.1 ∧ Wf n.toNat b.2.1.mat ∧ Wf n.toNat b.2.2.mat ∧
          EqOn n.toNat (mulF n.toNat (G b.2.2) (PW n.toNat (G b.2.1) b.1.toNat)) (PW n.toNat (G a) e.toNat) ∧
          t + bitWidth b.1.toNat * (1 + 2 * Kmul n.toNat) ≤
            t0 + 2 + n.toNat * (1 + n.toNat) + bitWidth e.toNat * (1 + 2 * Kmul n.toNat)⌝,
        fun b t => ⌜Wf n.toNat b.2.2.mat ∧ EqOn n.toNat (G b.2.2) (PW n.toNat (G a) e.toNat) ∧
          t ≤ t0 + 3 + n.toNat * (1 + n.toNat) + bitWidth e.toNat * (1 + 2 * Kmul n.toNat)⌝,
        fun b => b.1.toNat⟩
    all_goals simp +zetaDelta at *
    case vc2.step.isTrue =>
      obtain ⟨⟨h0, hWy, hWr, hI, hc⟩, he0⟩ := And.intro ‹_ ∧ _ ∧ _ ∧ _ ∧ _› ‹_ = (0 : Int)›
      rw [he0] at hI
      refine ⟨hWr, EqOn_trans (EqOn_symm (mulF_one_right _ _)) hI, ?_⟩
      rw [he0] at hc; simp at hc; omega
    case vc6.pre =>
      refine ⟨⟨he, ha, hW0, ?_, by omega⟩, by simp only [fuel]; omega⟩
      have hI : EqOn n.toNat (G r0) Idm := fun i j hi hj => by
        rw [hG0 i j (by omega) (by omega)]; unfold Idm; split <;> simp
      exact EqOn_trans (mulF_congr _ _ _ _ _ hI (EqOn_refl _ _)) (mulF_one_left _ _)
    case vc7.post.success => exact ‹_ ∧ _ ∧ _›
    case vc5.step.isFalse.isFalse.isFalse =>
      exfalso
      obtain ⟨h0, -⟩ := ‹(0 : Int) ≤ _ ∧ Wf _ _ ∧ Wf _ _ ∧ _ ∧ _›
      have hl := ‹land _ 1 = 0›
      have hs := ‹shr _ 1 = 0›
      have hne := ‹¬ _ = (0 : Int)›
      rw [land_one _ h0] at hl
      rw [shr_one] at hs
      omega
    case vc4.step.isFalse.isFalse.isTrue =>
      rename_i st _ _ _ _ _ _
      obtain ⟨h0, hWy, hWr, hI, hc⟩ := ‹(0 : Int) ≤ _ ∧ Wf _ _ ∧ Wf _ _ ∧ _ ∧ _›
      have hl := ‹land _ 1 = 0›
      have hne : ¬ st.1 = 0 := ‹¬ st.1 = 0›
      rw [land_one _ h0] at hl
      refine ⟨hWy, fun x y' c hx hW hG hc' => ?_⟩
      subst hx
      have hpar : ¬ st.1.toNat % 2 = 1 := by omega
      obtain ⟨g1, g2, g3, g4, g5⟩ := step_ok n a e.toNat _ _ _ _ x _ _ c h0 hne hI hc
        (by rw [if_neg hpar]; exact EqOn_refl _ _) (fun _ i j hi hj => hG i j (by omega) (by omega))
        (by rw [hc']; simp only [Kmul]; omega)
      rw [shr_one]
      exact ⟨⟨g1, hW, hWr, g2, g3⟩, g4, g5⟩
    case vc3.step.isFalse.isTrue =>
      rename_i st _ _ _ _ _
      obtain ⟨h0, hWy, hWr, hI, hc⟩ := ‹(0 : Int) ≤ _ ∧ Wf _ _ ∧ Wf _ _ ∧ _ ∧ _›
      have hl := ‹¬ land _ 1 = 0›
      have hne : ¬ st.1 = 0 := ‹¬ st.1 = 0›
      rw [land_one _ h0] at hl
      have hpar : st.1.toNat % 2 = 1 := by omega
      refine ⟨hWr, hWy, fun x r1 c1 hx hW1 hG1 hc1 => ?_⟩
      subst hx
      have hR' : EqOn n.toNat (G x) (if st.1.toNat % 2 = 1 then mulF n.toNat (G st.2.2) (G st.2.1) else G st.2.2) := by
        rw [if_pos hpar]; exact fun i j hi hj => hG1 i j (by omega) (by omega)
      split
      · rename_i hs
        simp only [WP.pure]
        rw [shr_one] at hs ⊢
        obtain ⟨g1, g2, g3, g4, g5⟩ := step_ok n a e.toNat _ _ _ _ _ x _ c1 h0 hne hI hc hR'
          (fun h => absurd (by omega) h) (by rw [hc1]; simp only [Kmul]; omega)
        exact ⟨⟨g1, hWy, hW1, g2, g3⟩, g4, g5⟩
      · rename_i hs
        mvcgen [WM]
        all_goals simp +zetaDelta at *
        refine ⟨hWy, fun z y' c hz hW hG hc' => ?_⟩
        subst hz
        rw [shr_one] at hs ⊢
        obtain ⟨g1, g2, g3, g4, g5⟩ := step_ok n a e.toNat _ _ _ _ z x _ c h0 hne hI hc hR'
          (fun _ i j hi hj => hG i j (by omega) (by omega)) (by rw [hc', hc1]; simp only [Kmul]; omega)
        exact ⟨⟨g1, hW, hW1, g2, g3⟩, g4, g5⟩
  all_goals (exfalso; simp_all)

end Proofs.Cpp.SquareMatrix
