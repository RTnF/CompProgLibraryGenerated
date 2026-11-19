import Proofs.Cpp.Gen.TreeOrder
import Proofs.Cpp.Lib.Basic
import Proofs.Math.TreeOrderMath

/-! # `tree_order` (library/tree/tree_order.hpp)

A breadth-first order of a rooted tree in CSR form. The translated loops keep `ord[0 .. cnt)` equal to the queue of
the pure model `qrun` of `Proofs.TreeOrderMath` (`OInv`, `IInv`), whose `order_spec` gives the order's properties;
the inner loop looks at the arcs of the visited vertices, at most all `m` arcs (`W_le`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.TreeOrderMath Proofs.TreeDpMath Proofs.TreeDpSpec

namespace Proofs.Cpp.TreeOrder

/-- The arrays as the lists of the pure model. -/
def natL (a : Array Int) : List Nat := a.toList.map Int.toNat

theorem natL_getD (a : Array Int) (k : Nat) : (natL a).getD k 0 = (a[k]!).toNat := by
  unfold natL
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

theorem intL_getD (a : Array Int) (k : Nat) : a.toList.getD k 0 = a[k]! := by
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

abbrev Q (head target parent : Array Int) (root : Nat) (i : Nat) : List Nat :=
  qrun (natL head) (natL target) parent.toList [root] i

/-- The entry `j` of a model list, as the value the C++ code stores. -/
def qat (q : List Nat) (j : Nat) : Int := (q.getD j 0 : Int)

/-- The children found among the first `k` arcs of `v`. -/
def kidPre (head target parent : Array Int) (v k : Nat) : List Nat :=
  (((arcs (natL head) v).take k).filter
    (fun p => decide (parent.toList.getD (tgt (natL target) p) 0 = (v : Int)))).map (tgt (natL target))

/-- The arcs looked at in the first `i` steps (the work of the inner loop). -/
def W (head target parent : Array Int) (root : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => W head target parent root j +
      if j < (Q head target parent root j).length
      then (arcs (natL head) ((Q head target parent root j).getD j 0)).length else 0

/-- The state of the outer loop after `L` steps. -/
def OInv (head target parent : Array Int) (root n L : Nat) (o : Array Int) (cnt : Int) : Prop :=
  o.size = n ∧ cnt = ((Q head target parent root L).length : Int) ∧
    ∀ j : Nat, j < (Q head target parent root L).length → o[j]! = qat (Q head target parent root L) j

/-- The state of the inner loop after `k` arcs of the vertex `V = Q[L]`. -/
def IInv (head target parent : Array Int) (root n L k : Nat) (o : Array Int) (cnt : Int) : Prop :=
  let q := Q head target parent root L ++ kidPre head target parent ((Q head target parent root L).getD L 0) k
  o.size = n ∧ cnt = (q.length : Int) ∧ ∀ j : Nat, j < q.length → o[j]! = qat q j

section
variable {head target parent : Array Int} {root n : Nat}

theorem Q_succ (L : Nat) (h : L < (Q head target parent root L).length) :
    Q head target parent root (L + 1) = Q head target parent root L ++
      kidT (natL head) (natL target) parent.toList ((Q head target parent root L).getD L 0) := by
  simp [Q, qrun, qstep, h]

theorem Q_skip (L : Nat) (h : ¬L < (Q head target parent root L).length) :
    Q head target parent root (L + 1) = Q head target parent root L := by
  simp [Q, qrun, qstep, h]

theorem Q_len (H : TO (natL head) (natL target) parent.toList n root) (L : Nat) :
    (Q head target parent root L).length ≤ n :=
  len_le_n _ (qrun_inv H L).nd (qrun_inv H L).lt

theorem kidPre_full (V : Nat) :
    kidPre head target parent V (arcs (natL head) V).length = kidT (natL head) (natL target) parent.toList V := by
  simp [kidPre, kidT, kidArcs]

theorem kidPre_len_le (V k : Nat) :
    (kidPre head target parent V k).length ≤ (kidT (natL head) (natL target) parent.toList V).length := by
  unfold kidPre kidT kidArcs
  simp only [List.length_map]
  exact ((List.take_sublist _ _).filter _).length_le

theorem arcs_get (V k : Nat) (hk : k < (arcs (natL head) V).length) :
    (arcs (natL head) V)[k] = (natL head).getD V 0 + k := by
  simp [arcs]

theorem kidPre_succ (V k : Nat) (hk : k < (arcs (natL head) V).length) :
    kidPre head target parent V (k + 1) = kidPre head target parent V k ++
      (if parent.toList.getD (tgt (natL target) ((natL head).getD V 0 + k)) 0 = (V : Int)
       then [tgt (natL target) ((natL head).getD V 0 + k)] else []) := by
  unfold kidPre
  rw [List.take_succ, List.getElem?_eq_getElem hk, arcs_get V k hk]
  simp only [Option.toList_some, List.filter_append, List.map_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem qat_append_left (q r : List Nat) (j : Nat) (h : j < q.length) : qat (q ++ r) j = qat q j := by
  simp [qat, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem qat_last (q : List Nat) (x : Nat) : qat (q ++ [x]) q.length = x := by
  simp [qat, List.getD_eq_getElem?_getD]

end

section
variable {head target parent : Array Int} {root n : Nat}

/-- The facts about the inner loop at the arc `cur` of the vertex `V = Q[L]`. -/
theorem inner_facts (H : TO (natL head) (natL target) parent.toList n root) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (L : Nat) (o0 : Array Int) (cnt0 : Int) (hO : OInv head target parent root n L o0 cnt0) (hlt : (L : Int) < cnt0)
    (pref suff : List Int) (cur : Int)
    (hr : range (get head (get o0 L)) (get head (get o0 L + 1)) = pref ++ cur :: suff) :
    let V := (Q head target parent root L).getD L 0
    L < (Q head target parent root L).length ∧ get o0 L = (V : Int) ∧
    pref.length < (arcs (natL head) V).length ∧ cur.toNat = (natL head).getD V 0 + pref.length ∧ 0 ≤ cur := by
  intro V
  obtain ⟨-, hc, he⟩ := hO
  have hL : L < (Q head target parent root L).length := by omega
  have hv : get o0 L = (V : Int) := by rw [get_eq, Int.toNat_natCast, he L hL]; rfl
  rw [hv] at hr
  have e := range_cursor hr
  have hl := range_prefix_length hr
  have a0 := hhead V
  have a1 := hhead (V + 1)
  have g0 := natL_getD head V
  have g1 := natL_getD head (V + 1)
  simp only [get_eq, Int.toNat_natCast, show ((V : Int) + 1).toNat = V + 1 by omega] at e hl
  refine ⟨hL, hv, ?_, ?_, ?_⟩
  · simp only [arcs, List.length_range', g0, g1]; omega
  · rw [e, g0]; omega
  · omega

theorem inner_child (H : TO (natL head) (natL target) parent.toList n root) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (L : Nat) (o0 : Array Int) (cnt0 : Int) (hO : OInv head target parent root n L o0 cnt0) (hlt : (L : Int) < cnt0)
    (pref suff : List Int) (cur : Int)
    (hr : range (get head (get o0 L)) (get head (get o0 L + 1)) = pref ++ cur :: suff)
    (o : Array Int) (cnt : Int) (hI : IInv head target parent root n L pref.length o cnt)
    (hpar : get parent (get target cur) = get o0 L) :
    IInv head target parent root n L (pref.length + 1) (set o cnt (get target cur)) (cnt + 1) := by
  obtain ⟨hL, hv, hk, hcur, -⟩ := inner_facts H hhead L o0 cnt0 hO hlt pref suff cur hr
  set V := (Q head target parent root L).getD L 0 with hVd
  have ht := htarget cur.toNat
  have gt := natL_getD target cur.toNat
  have hx : get target cur = ((tgt (natL target) ((natL head).getD V 0 + pref.length) : Nat) : Int) := by
    unfold tgt; rw [← hcur, gt, get_eq]; omega
  have hchild : parent.toList.getD (tgt (natL target) ((natL head).getD V 0 + pref.length)) 0 = (V : Int) := by
    rw [intL_getD, ← hv, ← hpar, hx, get_eq, Int.toNat_natCast]
  obtain ⟨hsz, hc, he⟩ := hI
  unfold IInv
  rw [kidPre_succ V pref.length hk, if_pos hchild, ← List.append_assoc]
  set q := Q head target parent root L ++ kidPre head target parent V pref.length
  have hbound : q.length + 1 ≤ n := by
    have h1 := Q_len H (L + 1)
    rw [Q_succ L hL, ← hVd] at h1
    have h2 := kidPre_len_le (head := head) (target := target) (parent := parent) V (pref.length + 1)
    rw [kidPre_succ V pref.length hk, if_pos hchild] at h2
    simp only [List.length_append, List.length_singleton] at h1 h2 ⊢
    simp only [q, List.length_append]; omega
  refine ⟨by simp [hsz], by simp; omega, fun j hj => ?_⟩
  simp only [List.length_append, List.length_singleton] at hj
  rw [getElemBang_set _ _ _ _ (by omega)]
  by_cases hjc : j = cnt.toNat
  · rw [if_pos hjc, hx, show j = q.length by omega, qat_last]
  · rw [if_neg hjc, qat_append_left _ _ _ (by omega)]; exact he j (by omega)

theorem inner_skip (H : TO (natL head) (natL target) parent.toList n root) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (L : Nat) (o0 : Array Int) (cnt0 : Int) (hO : OInv head target parent root n L o0 cnt0) (hlt : (L : Int) < cnt0)
    (pref suff : List Int) (cur : Int)
    (hr : range (get head (get o0 L)) (get head (get o0 L + 1)) = pref ++ cur :: suff)
    (o : Array Int) (cnt : Int) (hI : IInv head target parent root n L pref.length o cnt)
    (hpar : ¬get parent (get target cur) = get o0 L) :
    IInv head target parent root n L (pref.length + 1) o cnt := by
  obtain ⟨hL, hv, hk, hcur, -⟩ := inner_facts H hhead L o0 cnt0 hO hlt pref suff cur hr
  set V := (Q head target parent root L).getD L 0
  have ht := htarget cur.toNat
  have gt := natL_getD target cur.toNat
  have hx : get target cur = ((tgt (natL target) ((natL head).getD V 0 + pref.length) : Nat) : Int) := by
    unfold tgt; rw [← hcur, gt, get_eq]; omega
  have hchild : ¬parent.toList.getD (tgt (natL target) ((natL head).getD V 0 + pref.length)) 0 = (V : Int) := by
    rw [intL_getD, ← hv]; intro h; apply hpar; rw [hx, get_eq, Int.toNat_natCast]; exact h
  unfold IInv
  rw [kidPre_succ V pref.length hk, if_neg hchild, List.append_nil]
  exact hI

end

section
variable {head target parent : Array Int} {root n : Nat}

theorem inner_init (L : Nat) (o : Array Int) (cnt : Int) (hO : OInv head target parent root n L o cnt) :
    IInv head target parent root n L 0 o cnt := by
  unfold IInv; unfold OInv at hO; simpa [kidPre] using hO

theorem deg_eq (hhead : ∀ k : Nat, 0 ≤ head[k]!) (V : Nat) :
    (range (get head (V : Int)) (get head ((V : Int) + 1))).length = (arcs (natL head) V).length := by
  have a0 := hhead V
  have a1 := hhead (V + 1)
  rw [range_length]
  simp only [arcs, List.length_range', natL_getD, get_eq, Int.toNat_natCast,
    show ((V : Int) + 1).toNat = V + 1 by omega]
  omega

theorem W_succ (L : Nat) (h : L < (Q head target parent root L).length) :
    W head target parent root (L + 1) = W head target parent root L +
      (arcs (natL head) ((Q head target parent root L).getD L 0)).length := by
  simp [W, h]

theorem W_skip (L : Nat) (h : ¬L < (Q head target parent root L).length) :
    W head target parent root (L + 1) = W head target parent root L := by
  simp [W, h]

theorem inner_done (hhead : ∀ k : Nat, 0 ≤ head[k]!) (L : Nat) (o0 : Array Int) (cnt0 : Int)
    (hO : OInv head target parent root n L o0 cnt0) (hlt : (L : Int) < cnt0) (o : Array Int) (cnt : Int) (s t0 : Nat)
    (hI : IInv head target parent root n L (range (get head (get o0 L)) (get head (get o0 L + 1))).length o cnt ∧
      s = t0 + 1 + L + W head target parent root L + 1 +
        (range (get head (get o0 L)) (get head (get o0 L + 1))).length) :
    OInv head target parent root n (L + 1) o cnt ∧
      s = t0 + 1 + (L + 1) + W head target parent root (L + 1) := by
  obtain ⟨-, hc, he⟩ := hO
  have hL : L < (Q head target parent root L).length := by omega
  have hv : get o0 L = (((Q head target parent root L).getD L 0 : Nat) : Int) := by
    rw [get_eq, Int.toNat_natCast, he L hL]; rfl
  rw [hv, deg_eq hhead] at hI
  obtain ⟨hI, hs⟩ := hI
  unfold IInv at hI
  rw [kidPre_full] at hI
  refine ⟨?_, by rw [W_succ L hL]; omega⟩
  unfold OInv; rw [Q_succ L hL]; exact hI

theorem outer_skip (L : Nat) (o : Array Int) (cnt : Int) (hO : OInv head target parent root n L o cnt)
    (hge : cnt ≤ (L : Int)) :
    OInv head target parent root n (L + 1) o cnt ∧ W head target parent root (L + 1) = W head target parent root L := by
  have h : ¬L < (Q head target parent root L).length := by have := hO.2.1; omega
  unfold OInv; rw [Q_skip L h, W_skip L h]; exact ⟨hO, rfl⟩

theorem outer_init (H : TO (natL head) (natL target) parent.toList n root) (ord : Array Int) (hord : ord.size = n) :
    OInv head target parent root n 0 (set ord 0 root) 1 := by
  have := H.rootlt
  refine ⟨by simp [hord], by simp [Q, qrun], fun j hj => ?_⟩
  simp [Q, qrun] at hj
  subst hj
  rw [getElemBang_set _ _ _ _ (by simp; omega)]
  simp [qat, Q, qrun]

end

theorem tree_order_spec (head target parent ord : Array Int) (root n : Nat)
    (H : TO (natL head) (natL target) parent.toList n root)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hord : ord.size = n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_order head target parent ord root n
    ⦃⇓ r c => ⌜OInv head target parent root n n r (Q head target parent root n).length ∧
               c = t0 + 1 + n + W head target parent root n⌝⦄ := by
  mvcgen [cp.tree_order]
  case inv1 =>
    exact ⇓⟨xs, o, cnt⟩ c => ⌜OInv head target parent root n xs.prefix.length o cnt ∧
      c = t0 + 1 + xs.prefix.length + W head target parent root xs.prefix.length⌝
  case inv2 =>
    rename_i pref cur suff hr b _ _ s0 _ hI hlt
    exact ⇓⟨ys, o, cnt⟩ c => ⌜IInv head target parent root n pref.length ys.prefix.length o cnt ∧
      c = t0 + 1 + pref.length + W head target parent root pref.length + 1 + ys.prefix.length⌝
  all_goals simp +zetaDelta at *
  all_goals (try (have e := range_cursor ‹range 0 (n : Int) = _ ++ _ :: _›; simp at e; subst e))
  · exact ⟨inner_child H hhead htarget _ _ _ (‹OInv _ _ _ _ _ _ _ _ ∧ _›).1 ‹_› _ _ _ ‹_› _ _
      (‹IInv _ _ _ _ _ _ _ _ _ ∧ _›).1 ‹_›, by have := (‹IInv _ _ _ _ _ _ _ _ _ ∧ _›).2; omega⟩
  · exact ⟨inner_skip H hhead htarget _ _ _ (‹OInv _ _ _ _ _ _ _ _ ∧ _›).1 ‹_› _ _ _ ‹_› _ _
      (‹IInv _ _ _ _ _ _ _ _ _ ∧ _›).1 ‹_›, by have := (‹IInv _ _ _ _ _ _ _ _ _ ∧ _›).2; omega⟩
  · exact ⟨inner_init _ _ _ (‹OInv _ _ _ _ _ _ _ _ ∧ _›).1, (‹OInv _ _ _ _ _ _ _ _ ∧ _›).2⟩
  · exact inner_done hhead _ _ _ (‹OInv _ _ _ _ _ _ _ _ ∧ _›).1 ‹_› _ _ _ _ ‹_›
  · have hO := ‹OInv _ _ _ _ _ _ _ _ ∧ _›
    obtain ⟨h1, h2⟩ := outer_skip _ _ _ hO.1 ‹_›
    exact ⟨h1, by rw [h2]; omega⟩
  · exact ⟨outer_init H ord hord, by simp [W]; omega⟩
  · have hO := ‹OInv _ _ _ _ _ _ _ _ ∧ _›
    refine ⟨?_, hO.2⟩
    have := hO.1.2.1
    rw [← this]; exact hO.1

/-! ## The work: the arcs of the visited vertices, at most all arcs -/

/-- `f 0 + ... + f (n - 1)`. -/
def S (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).sum

theorem S_succ (n : Nat) (f : Nat → Nat) : S (n + 1) f = S n f + f n := by
  simp [S, List.range_succ]

theorem S_mono (n : Nat) (f g : Nat → Nat) (h : ∀ v, f v ≤ g v) : S n f ≤ S n g := by
  induction n with
  | zero => simp [S]
  | succ n ih => rw [S_succ, S_succ]; have := h n; omega

theorem S_add (n : Nat) (f g : Nat → Nat) : S n (fun v => f v + g v) = S n f + S n g := by
  induction n with
  | zero => simp [S]
  | succ n ih => rw [S_succ, S_succ, S_succ, ih]; omega

theorem S_single (n x : Nat) (g : Nat → Nat) :
    S n (fun v => if v = x then g v else 0) = if x < n then g x else 0 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S_succ, ih]
    by_cases h1 : x < n
    · simp [h1, show n ≠ x by omega, show x < n + 1 by omega]
    · by_cases h2 : x = n
      · subst h2; simp
      · simp [h1, h2, Ne.symm h2, show ¬x < n + 1 by omega]

theorem sum_nodup (g : Nat → Nat) (n : Nat) : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < n) →
    (l.map g).sum = S n (fun v => if v ∈ l then g v else 0) := by
  intro l
  induction l with
  | nil => intro _ _; simp [S]
  | cons x l ih =>
    intro hnd hlt
    rw [List.nodup_cons] at hnd
    have e : (fun v => if v ∈ x :: l then g v else 0) =
        (fun v => (if v = x then g v else 0) + (if v ∈ l then g v else 0)) := by
      funext v
      by_cases h1 : v = x
      · subst h1; simp [hnd.1]
      · simp [h1]
    rw [e, S_add, S_single, if_pos (hlt x (by simp)), ← ih hnd.2 (fun y hy => hlt y (by simp [hy]))]
    simp

theorem S_telescope (n : Nat) (h : Nat → Nat) (hm : ∀ v, v < n → h v ≤ h (v + 1)) :
    S n (fun v => h (v + 1) - h v) = h n - h 0 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S_succ, ih (fun v hv => hm v (by omega))]
    have h1 := hm n (by omega)
    have : h 0 ≤ h n := by
      clear ih h1
      induction n with
      | zero => exact Nat.le_refl _
      | succ k ihk => exact Nat.le_trans (ihk (fun v hv => hm v (by omega))) (hm k (by omega))
    omega

section
variable {head target parent : Array Int} {root n : Nat}

theorem W_eq (L : Nat) :
    W head target parent root L =
      (((Q head target parent root L).take L).map (fun v => (arcs (natL head) v).length)).sum := by
  induction L with
  | zero => simp [W]
  | succ L ih =>
    by_cases h : L < (Q head target parent root L).length
    · rw [W_succ L h, ih, Q_succ L h, List.take_succ, List.take_append_of_le_length (by omega),
        List.getElem?_append_left h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.take_succ]; simp [List.getElem?_eq_getElem h]
    · rw [W_skip L h, ih, Q_skip L h, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem W_le (H : TO (natL head) (natL target) parent.toList n root)
    (hmono : ∀ v : Nat, v < n → head[v]! ≤ head[v + 1]!) (hhead : ∀ k : Nat, 0 ≤ head[k]!) :
    W head target parent root n ≤ (head[n]!).toNat := by
  rw [W_eq, List.take_of_length_le (Q_len H n)]
  have hI := qrun_inv H n
  rw [sum_nodup _ n _ hI.nd hI.lt]
  have h1 := S_mono n (fun v => if v ∈ qrun (natL head) (natL target) parent.toList [root] n
      then (arcs (natL head) v).length else 0)
    (fun v => (natL head).getD (v + 1) 0 - (natL head).getD v 0)
    (fun v => by split <;> simp [arcs])
  have h2 := S_telescope n (fun v => (natL head).getD v 0) (fun v hv => by
    simp only [natL_getD]; have := hmono v hv; have := hhead v; omega)
  rw [h2] at h1
  have e1 := natL_getD head n
  have e0 := natL_getD head 0
  omega

end

/-- `tree_order(head, target, parent, ord, root, n)` on a tree in CSR form with the parent array of `tree_root`
(`TO`): `ord` becomes a permutation of `0, ..., n - 1` with `ord[0] = root` in which every other vertex comes after
its parent; at most `n + m + 1` steps for `m = head[n]` arcs. -/
theorem tree_order_correct (head target parent ord : Array Int) (root n : Nat)
    (H : TO (natL head) (natL target) parent.toList n root)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (hmono : ∀ v : Nat, v < n → head[v]! ≤ head[v + 1]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hord : ord.size = n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.tree_order head target parent ord root n
    ⦃⇓ r c => ⌜r.size = n ∧ (∀ j : Nat, j < n → 0 ≤ r[j]! ∧ r[j]! < n) ∧
               (∀ i j : Nat, i < n → j < n → r[i]! = r[j]! → i = j) ∧ r[0]! = root ∧
               (∀ j : Nat, 1 ≤ j → j < n → ∃ j', j' < j ∧ r[j']! = parent[(r[j]!).toNat]!) ∧
               c ≤ t0 + 1 + n + (head[n]!).toNat⌝⦄ := by
  have hspec := tree_order_spec head target parent ord root n H hhead htarget hord t0
  have hW := W_le H hmono hhead
  obtain ⟨hlen, hnd, hlt, h0, hpar⟩ := order_spec H
  obtain ⟨r, c, hrun, ⟨hsz, -, he⟩, hc⟩ := run_of_triple hspec
  apply triple_of_run r c hrun
  simp only [Q, qat] at he
  have hq : ∀ j : Nat, j < n → r[j]! = (((qrun (natL head) (natL target) parent.toList [root] n).getD j 0 : Nat) : Int) :=
    fun j hj => he j (by omega)
  have hmem : ∀ j : Nat, j < n → (qrun (natL head) (natL target) parent.toList [root] n).getD j 0 < n :=
    fun j hj => hlt _ (getD_mem_of_lt _ _ (by omega))
  refine ⟨hsz, fun j hj => ?_, fun i j hi hj hij => ?_, ?_, fun j h1 hj => ?_, by omega⟩
  · rw [hq j hj]; have := hmem j hj; omega
  · rw [hq i hi, hq j hj] at hij
    exact getD_inj _ hnd i j (by omega) (by omega) (by exact_mod_cast hij)
  · have := H.rootlt
    rw [hq 0 (by omega)]; exact congrArg _ h0
  · obtain ⟨j', hj', hp⟩ := hpar j h1 hj
    refine ⟨j', hj', ?_⟩
    rw [hq j' (by omega), hp, hq j hj, Int.toNat_natCast, ← intL_getD]
    have := (H.parv _ (hmem j hj)).1
    unfold par; omega

end Proofs.Cpp.TreeOrder
