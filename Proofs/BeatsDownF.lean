import Proofs.BeatsStep
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)

/-- The side conditions of a descent step through an internal node with an add tag. -/
structure DownAdd (b : BS) (inf : Int) (W0 W1 W2 : Nat) : Prop where
  hmode : b.lval.getD W0 0 = inf
  hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int)
  hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)
  hZ3 : b.mxv.getD W0 0 ≠ inf
  hZ5 : b.mnv.getD W0 0 ≠ inf
  hlv1 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0 ≠ inf
  hlv2 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0 ≠ inf
  hint : b.len.getD W0 0 ≠ 1
  hS0 : s64.valid (b.mxv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS1 : b.smx.getD (2 * W0 + 1) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS2 : s64.valid (b.mnv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS3 : b.smn.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS4 : (b.lval.getD (2 * W0 + 1) 0 = inf ∧ b.len.getD (2 * W0 + 1) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS5 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true
  hS6 : s64.valid (b.mxv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true
  hS7 : b.smx.getD (2 * W0 + 2) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true
  hS8 : s64.valid (b.mnv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true
  hS9 : b.smn.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true
  hS10 : (b.lval.getD (2 * W0 + 2) 0 = inf ∧ b.len.getD (2 * W0 + 2) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true
  hS11 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true

theorem down_add_facts (inf : Int) (hinfI : inf = INF) (b : BS) (H : Heap) (hH : HRel inf b H) (nd : Nd) (tg : Tag) (l r : BT)
    (k lo hi : Nat) (ys : List Int) (hinv : Inv (.node nd tg l r) ys) (hag : Agree H (.node nd tg l r) k)
    (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hps : PushSafe (.node nd tg l r)) (htg : tg.lval = none) : DownAdd b inf k lo hi := by
  subst hinfI
  obtain ⟨hnd0, htag0⟩ := cell_of_agree INF b H hH _ k lo hi hag hsh hlen
  have hag2 := (agree_node H nd tg l r k).mp hag
  obtain ⟨hlo, hshl, hshr⟩ := hsh
  obtain ⟨hlenK, hlenl, hlenr⟩ := hlen
  obtain ⟨c1n, c1t⟩ := cell_of_agree INF b H hH l (2 * k + 1) lo ((lo + hi) / 2) hag2.2.1 hshl hlenl
  obtain ⟨c2n, c2t⟩ := cell_of_agree INF b H hH r (2 * k + 2) ((lo + hi) / 2) hi hag2.2.2 hshr hlenr
  have hla : b.ladd.getD k 0 = tg.ladd := by simpa [decTag, BT.ladd] using congrArg Tag.ladd htag0
  have hmode : b.lval.getD k 0 = INF := by
    have := congrArg Tag.lval htag0
    simp only [decTag, BT.lval, htg] at this
    by_contra h
    rw [if_neg h] at this
    cases this
  have hnd' : decNd b k = nd := hnd0
  have hdesc : Desc nd ys := hinv.desc
  have hrange : InRange ys := hinv.range
  have hne : ys ≠ [] := hinv.ne
  obtain ⟨m1, m2, _, _⟩ := desc_mem nd ys hdesc hrange hne
  have hmx : b.mxv.getD k 0 = nd.mx := by have := congrArg Nd.mx hnd'; simpa [decNd] using this
  have hmn : b.mnv.getD k 0 = nd.mn := by have := congrArg Nd.mn hnd'; simpa [decNd] using this
  have hhi : hi - lo ≠ 1 := by omega
  have hintZ : b.len.getD k 0 ≠ 1 := by
    rw [hlenK]; intro h; have : hi - lo = 1 := by exact_mod_cast h
    exact hhi this
  cases hinv with
  | node _ _ _ _ xl xr ys' hn hl' hr' =>
    have hra1 : ∀ w ∈ xl, -INF < w + b.ladd.getD k 0 ∧ w + b.ladd.getD k 0 < INF := by
      intro w hw; rw [hla]; exact hn.rnga htg w (List.mem_append.mpr (Or.inl hw))
    have hra2 : ∀ w ∈ xr, -INF < w + b.ladd.getD k 0 ∧ w + b.ladd.getD k 0 < INF := by
      intro w hw; rw [hla]; exact hn.rnga htg w (List.mem_append.mpr (Or.inr hw))
    obtain ⟨p1, p2, p3, p4⟩ := hps
    have s1 := child_cell_sums INF rfl b (2 * k + 1) l xl (b.ladd.getD k 0) hl' c1n c1t hra1
      (by rw [hla]; exact p1 htg) (by rw [hla]; exact p2 htg)
    have s2 := child_cell_sums INF rfl b (2 * k + 2) r xr (b.ladd.getD k 0) hr' c2n c2t hra2
      (by rw [hla]; exact p3 htg) (by rw [hla]; exact p4 htg)
    refine ⟨hmode, LenOK_root hlenl, LenOK_root hlenr, ?_, ?_, s1.2.2.2.2.2.2, s2.2.2.2.2.2.2, hintZ, s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1,
      s1.2.2.2.2.1, s1.2.2.2.2.2.1, s2.1, s2.2.1, s2.2.2.1, s2.2.2.2.1, s2.2.2.2.2.1, s2.2.2.2.2.2.1⟩
    · rw [hmx]; have := hrange _ m1; omega
    · rw [hmn]; have := hrange _ m2; omega

/-- The side conditions of a descent step through an internal node with an assignment tag. -/
structure DownSet (b : BS) (inf : Int) (W0 W1 W2 : Nat) : Prop where
  hmode : b.lval.getD W0 0 ≠ inf
  hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int)
  hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)
  hint : b.len.getD W0 0 ≠ 1

theorem down_set_facts (inf : Int) (hinfI : inf = INF) (b : BS) (H : Heap) (hH : HRel inf b H) (nd : Nd) (tg : Tag) (l r : BT)
    (k lo hi : Nat) (ys : List Int) (hinv : Inv (.node nd tg l r) ys) (hag : Agree H (.node nd tg l r) k)
    (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (v : Int) (htg : tg.lval = some v) : DownSet b inf k lo hi := by
  subst hinfI
  obtain ⟨hnd0, htag0⟩ := cell_of_agree INF b H hH _ k lo hi hag hsh hlen
  obtain ⟨hlo, hshl, hshr⟩ := hsh
  obtain ⟨hlenK, hlenl, hlenr⟩ := hlen
  have hhi : hi - lo ≠ 1 := by omega
  refine ⟨?_, LenOK_root hlenl, LenOK_root hlenr, ?_⟩
  · have := congrArg Tag.lval htag0
    simp only [decTag, BT.lval, htg] at this
    intro h
    rw [if_pos h] at this
    cases this
  · rw [hlenK]; intro h; have : hi - lo = 1 := by exact_mod_cast h
    exact hhi this

theorem node_lenK {b : BS} {nd : Nd} {tg : Tag} {l r : BT} {k lo hi : Nat} (hsh : Shape lo hi (BT.node nd tg l r).skel)
    (hlen : LenOK b (.node nd tg l r) k lo hi) : b.len.getD k 0 ≠ 1 := by
  obtain ⟨hlo, _, _⟩ := hsh
  have := hlen.1
  intro h; rw [h] at this; omega

end Proofs.BeatsRep
