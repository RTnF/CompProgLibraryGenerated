import Proofs.BeatsLoop8
import Proofs.BeatsExecL0
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)

instance : DecidableEq Cls := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

def clsOf (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Cls :=
  if op = 0 then clsMin qa qb x nd lo hi else if op = 1 then clsMax qa qb x nd lo hi else clsRange qa qb nd lo hi

/-- The stop condition of the traversal for operation `op`. -/
def stopP (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Prop :=
  (qb ≤ lo ∨ hi ≤ qa) ∨ (op = 0 ∧ nd.mx ≤ x) ∨ (op = 1 ∧ x ≤ nd.mn)

/-- The whole-node condition (given that the traversal does not stop). -/
def wholeP (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Prop :=
  (qa ≤ lo ∧ hi ≤ qb) ∧ (op = 0 → nd.smx < x) ∧ (op = 1 → x < nd.smn)

instance (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Decidable (stopP op qa qb x nd lo hi) := by
  unfold stopP; infer_instance

instance (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Decidable (wholeP op qa qb x nd lo hi) := by
  unfold wholeP; infer_instance

theorem clsOf_stop_iff (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (hop : op < 4) :
    clsOf op qa qb x nd lo hi = Cls.stop ↔ stopP op qa qb x nd lo hi := by
  have hops : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hops with h | h | h | h <;> subst h <;> simp only [clsOf, clsMin, clsMax, clsRange, stopP] <;> split_ifs <;> simp_all <;> omega

theorem clsOf_whole_iff (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (hop : op < 4) :
    clsOf op qa qb x nd lo hi = Cls.whole ↔ (¬ stopP op qa qb x nd lo hi ∧ wholeP op qa qb x nd lo hi) := by
  have hops : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hops with h | h | h | h <;> subst h <;> simp only [clsOf, clsMin, clsMax, clsRange, stopP, wholeP] <;> split_ifs <;> simp_all <;> omega

theorem clsOf_congr (op qa qb : Nat) (x : Int) (nd nd' : Nd) (lo hi : Nat) (h1 : nd.mx = nd'.mx) (h2 : nd.smx = nd'.smx)
    (h3 : nd.mn = nd'.mn) (h4 : nd.smn = nd'.smn) : clsOf op qa qb x nd lo hi = clsOf op qa qb x nd' lo hi := by
  simp only [clsOf, clsMin, clsMax, clsRange, h1, h2, h3, h4]

/-- Node summary stored at index `i`. -/
def decNd (b : BS) (i : Nat) : Nd :=
  ⟨b.mxv.getD i 0, b.smx.getD i 0, b.mxc.getD i 0, b.mnv.getD i 0, b.smn.getD i 0, b.mnc.getD i 0⟩

/-- Pending tag stored at index `i` (`lval = inf` means no assignment). -/
def decTag (inf : Int) (b : BS) (i : Nat) : Tag :=
  ⟨if b.lval.getD i 0 = inf then none else some (b.lval.getD i 0), b.ladd.getD i 0⟩

/-- The heap described by the arrays. -/
def Hof (inf : Int) (b : BS) : Heap := fun i => (decNd b i, decTag inf b i)

/-- The explicit stack: the top frame is in slot `sp - 1`. -/
def StkRep (b : BS) (sp : Nat) (S : List Fr) : Prop :=
  S.length = sp ∧ ∀ (j : Nat) (f : Fr), S[j]? = some f →
    b.sk.getD (sp - 1 - j) 0 = (f.k : Int) ∧ b.sl.getD (sp - 1 - j) 0 = (f.lo : Int) ∧ b.sr.getD (sp - 1 - j) 0 = (f.hi : Int)

/-- The entered nodes: the most recent is in slot `ne - 1`. -/
def EntRep (b : BS) (ne : Nat) (E : List Nat) : Prop :=
  E.length = ne ∧ ∀ (j e : Nat), E[j]? = some e → b.ent.getD (ne - 1 - j) 0 = (e : Int)

/-- Two states agree on the heap-related fields. -/
theorem Hof_congr (inf : Int) (b c : BS) (h0 : b.mxv = c.mxv) (h1 : b.smx = c.smx) (h2 : b.mxc = c.mxc) (h3 : b.mnv = c.mnv)
    (h4 : b.smn = c.smn) (h5 : b.mnc = c.mnc) (h8 : b.lval = c.lval) (h7 : b.ladd = c.ladd) : Hof inf b = Hof inf c := by
  funext i
  simp [Hof, decNd, decTag, h0, h1, h2, h3, h4, h5, h7, h8]

theorem StkRep_pop (b b' : BS) (sp : Nat) (f : Fr) (S : List Fr) (h : StkRep b sp (f :: S))
    (hk : ∀ i, i < sp - 1 → b'.sk.getD i 0 = b.sk.getD i 0) (hl : ∀ i, i < sp - 1 → b'.sl.getD i 0 = b.sl.getD i 0)
    (hr : ∀ i, i < sp - 1 → b'.sr.getD i 0 = b.sr.getD i 0) : StkRep b' (sp - 1) S := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp at h1; omega, fun j g hj => ?_⟩
  have := h2 (j + 1) g (by simpa using hj)
  have e : sp - 1 - 1 - j = sp - 1 - (j + 1) := by omega
  have hjS : j < S.length := by
    by_contra hc
    have := List.getElem?_eq_none (by omega : S.length ≤ j)
    rw [this] at hj; cases hj
  have hlt : sp - 1 - (j + 1) < sp - 1 := by simp at h1; omega
  rw [e, hk _ hlt, hl _ hlt, hr _ hlt]
  exact this

theorem EntRep_keep (b b' : BS) (ne : Nat) (E : List Nat) (h : EntRep b ne E) (hent : ∀ i, i < ne → b'.ent.getD i 0 = b.ent.getD i 0) :
    EntRep b' ne E := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun j e hj => ?_⟩
  have hlt : ne - 1 - j < ne := by
    have : j < E.length := by
      by_contra hc
      have := List.getElem?_eq_none (by omega : E.length ≤ j)
      rw [this] at hj; cases hj
    omega
  rw [hent _ hlt]
  exact h2 j e hj

theorem getD_set2_below (l : List Int) (a c : Nat) (x y : Int) (i : Nat) (ha : i < a) (hc : i < c) :
    ((l.set a x).set c y).getD i 0 = l.getD i 0 := by
  rw [getD_set_diff _ _ _ _ (by omega), getD_set_diff _ _ _ _ (by omega)]

theorem getD_set1_below (l : List Int) (a : Nat) (x : Int) (i : Nat) (ha : i < a) :
    (l.set a x).getD i 0 = l.getD i 0 :=
  getD_set_diff _ _ _ _ (by omega)

/-- A sequence of unconditional array writes, in program order. -/
def applySets : List Int → List (Nat × Int) → List Int
  | l, [] => l
  | l, (i, a) :: ops => applySets (l.set i a) ops

/-- The value written last to index `i`, if any. -/
def lastW : List (Nat × Int) → Nat → Option Int
  | [], _ => none
  | (j, a) :: ops, i => match lastW ops i with
    | some v => some v
    | none => if j = i then some a else none

theorem getD_applySets : ∀ (ops : List (Nat × Int)) (l : List Int) (i : Nat), (∀ p ∈ ops, p.1 < l.length) →
    (applySets l ops).getD i 0 = (lastW ops i).getD (l.getD i 0)
  | [], l, i, _ => by simp [applySets, lastW]
  | (j, a) :: ops, l, i, h => by
    have hj : j < l.length := h (j, a) (by simp)
    have h' : ∀ p ∈ ops, p.1 < (l.set j a).length := fun p hp => by
      simpa using h p (List.mem_cons_of_mem _ hp)
    simp only [applySets, lastW]
    rw [getD_applySets ops (l.set j a) i h']
    cases hl : lastW ops i with
    | some v => simp
    | none =>
      by_cases hji : j = i
      · subst hji
        rw [getD_set_same _ _ _ hj]
        simp
      · rw [getD_set_diff _ _ _ _ hji]
        simp [hji]

theorem lt_of_not_stop0 (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (hop : op = 0) (h : ¬ stopP op qa qb x nd lo hi) : x < nd.mx := by
  unfold stopP at h; omega

theorem lt_of_not_stop1 (op qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (hop : op = 1) (h : ¬ stopP op qa qb x nd lo hi) : x ≤ nd.mn → False := by
  unfold stopP at h; omega

theorem capMax_key (Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 x inf X8 X14 X15 X16 : Int)
    (hX14 : X14 = (if ((X8 = 1) ∧ (Z3 = Z5)) then x else Z5))
    (hX15 : X15 = (if (((X8 = 1) ∧ (Z3 ≠ Z5)) ∧ (Z3 = Z6)) then x else Z6))
    (hX16 : X16 = (if (((X8 = 1) ∧ (Z7 ≠ inf)) ∧ (x < Z7)) then x else Z7))
    (eX8 : X8 = 1) (hx : x ≠ inf) (hlt : x < Z3) :
    (({ mx := x, smx := Z4, mc := Z9, mn := X14, smn := X15, mnc := Z10 } : Nd),
      ({ lval := if X16 = inf then none else some X16, ladd := Z8 } : Tag)) =
    Cellh.capMaxC x
      (({ mx := Z3, smx := Z4, mc := Z9, mn := Z5, smn := Z6, mnc := Z10 } : Nd),
        ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag)) := by
  subst eX8 hX14 hX15 hX16
  simp only [Cellh.capMaxC, hlt, if_true, updMax, tagMax]
  split_ifs <;> simp_all <;> omega

theorem lastW_pair_below (a i : Nat) (x y d : Int) (h : i < a) : (lastW [(a, x), (a + 1, y)] i).getD d = d := by
  have h1 : ¬ a = i := by omega
  have h2 : ¬ a + 1 = i := by omega
  simp [lastW, h1, h2]

theorem lastW_single_below (a i : Nat) (x d : Int) (h : i < a) : (lastW [(a, x)] i).getD d = d := by
  have h1 : ¬ a = i := by omega
  simp [lastW, h1]

theorem capMin_key (Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 x inf X18 X19 X20 : Int)
    (e18 : X18 = (if (Z3 = Z5) then x else Z3))
    (e19 : X19 = (if ((Z3 ≠ Z5) ∧ (Z4 = Z5)) then x else Z4))
    (e20 : X20 = (if ((Z7 ≠ inf) ∧ (Z7 < x)) then x else Z7))
    (hx : x ≠ inf) (hlt : Z5 < x) :
    (({ mx := X18, smx := X19, mc := Z9, mn := x, smn := Z6, mnc := Z10 } : Nd),
      ({ lval := if X20 = inf then none else some X20, ladd := Z8 } : Tag)) =
    Cellh.capMinC x
      (({ mx := Z3, smx := Z4, mc := Z9, mn := Z5, smn := Z6, mnc := Z10 } : Nd),
        ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag)) := by
  subst e18 e19 e20
  simp only [Cellh.capMinC, hlt, if_true, updMin, negNd, updMax, tagMin]
  by_cases h1 : Z3 = Z5
  · have h1' : Z5 = Z3 := h1.symm
    by_cases h3 : Z7 = inf <;> by_cases h4 : Z7 < x <;> simp [h1, h3, h4, hx] <;> omega
  · have h1' : ¬ Z5 = Z3 := fun h => h1 h.symm
    by_cases h2 : Z4 = Z5
    · have h2' : Z5 = Z4 := h2.symm
      by_cases h3 : Z7 = inf <;> by_cases h4 : Z7 < x <;> simp [h1, h1', h2, h3, h4, hx] <;> omega
    · have h2' : ¬ Z5 = Z4 := fun h => h2 h.symm
      by_cases h3 : Z7 = inf <;> by_cases h4 : Z7 < x <;> simp [h1, h1', h2, h2', h3, h4, hx] <;> omega

theorem add_key (Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 x inf X21 X22 X23 X24 : Int)
    (e21 : X21 = (if (Z4 ≠ (-inf)) then (Z4 + x) else Z4))
    (e22 : X22 = (if (Z6 ≠ inf) then (Z6 + x) else Z6))
    (e23 : X23 = (if (Z7 = inf) then (Z8 + x) else Z8))
    (e24 : X24 = (if (Z7 ≠ inf) then (Z7 + x) else Z7))
    (hinfI : inf = INF) (hadd7 : Z7 ≠ inf → Z7 + x ≠ inf) :
    (({ mx := Z3 + x, smx := X21, mc := Z9, mn := Z5 + x, smn := X22, mnc := Z10 } : Nd),
      ({ lval := if X24 = inf then none else some X24, ladd := X23 } : Tag)) =
    Cellh.addC x
      (({ mx := Z3, smx := Z4, mc := Z9, mn := Z5, smn := Z6, mnc := Z10 } : Nd),
        ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag)) := by
  subst e21 e22 e23 e24
  subst hinfI
  simp only [Cellh.addC, addNd, tagAdd]
  by_cases h7 : Z7 = INF
  · simp [h7]
  · have := hadd7 h7
    simp [h7, this]

theorem set_key (Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 x inf : Int) (W1 W2 : Nat)
    (hinfI : inf = INF) (hx : x ≠ inf) (hlen : Z11 = ((W2 - W1 : Nat) : Int)) :
    (({ mx := x, smx := -inf, mc := Z11, mn := x, smn := inf, mnc := Z11 } : Nd),
      ({ lval := if x = inf then none else some x, ladd := 0 } : Tag)) =
    Cellh.setC ((W2 - W1 : Nat) : Int) x
      (({ mx := Z3, smx := Z4, mc := Z9, mn := Z5, smn := Z6, mnc := Z10 } : Nd),
        ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag)) := by
  subst hinfI hlen
  simp [Cellh.setC, setNd, tagSet, hx]

/-- The cap-by-maximum step on an arbitrary cell. -/
theorem capMax_step (Z3 M SM mc N SN nc LV LA inf g A49 A50 A51 A52 : Int)
    (eg : g = (if Z3 < M then 1 else 0))
    (e49 : A49 = (if (g = 1) then Z3 else M))
    (e50 : A50 = (if ((g = 1) ∧ (M = N)) then Z3 else N))
    (e51 : A51 = (if (((g = 1) ∧ (M ≠ N)) ∧ (M = SN)) then Z3 else SN))
    (e52 : A52 = (if (((g = 1) ∧ (LV ≠ inf)) ∧ (Z3 < LV)) then Z3 else LV))
    (hZ3 : Z3 ≠ inf) :
    (({ mx := A49, smx := SM, mc := mc, mn := A50, smn := A51, mnc := nc } : Nd),
      ({ lval := if A52 = inf then none else some A52, ladd := LA } : Tag)) =
    Cellh.capMaxC Z3
      (({ mx := M, smx := SM, mc := mc, mn := N, smn := SN, mnc := nc } : Nd),
        ({ lval := if LV = inf then none else some LV, ladd := LA } : Tag)) := by
  subst eg e49 e50 e51 e52
  by_cases hg : Z3 < M
  · simp only [Cellh.capMaxC, hg, if_true, updMax, tagMax]
    by_cases h1 : M = N
    · by_cases h3 : LV = inf <;> by_cases h4 : Z3 < LV <;> simp [hg, h1, h3, h4, hZ3] <;> (try split_ifs) <;> (try simp_all) <;> (try omega)
    · by_cases h2 : M = SN
      · by_cases h3 : LV = inf <;> by_cases h4 : Z3 < LV <;> simp [hg, h1, h2, h3, h4, hZ3] <;> (try split_ifs) <;> (try simp_all) <;> (try omega)
      · by_cases h3 : LV = inf <;> by_cases h4 : Z3 < LV <;> simp [hg, h1, h2, h3, h4, hZ3] <;> (try split_ifs) <;> (try simp_all) <;> (try omega)
  · simp [Cellh.capMaxC, hg] <;> (try split_ifs) <;> (try simp_all) <;> (try omega)

/-- The cap-by-minimum step on an arbitrary cell. -/
theorem capMin_step (Z5 M SM mc N SN nc LV LA inf g A54 A55 A56 A57 : Int)
    (eg : g = (if N < Z5 then 1 else 0))
    (e54 : A54 = (if (g = 1) then Z5 else N))
    (e55 : A55 = (if ((g = 1) ∧ (M = N)) then Z5 else M))
    (e56 : A56 = (if (((g = 1) ∧ (M ≠ N)) ∧ (SM = N)) then Z5 else SM))
    (e57 : A57 = (if (((g = 1) ∧ (LV ≠ inf)) ∧ (LV < Z5)) then Z5 else LV))
    (hZ5 : Z5 ≠ inf) :
    (({ mx := A55, smx := A56, mc := mc, mn := A54, smn := SN, mnc := nc } : Nd),
      ({ lval := if A57 = inf then none else some A57, ladd := LA } : Tag)) =
    Cellh.capMinC Z5
      (({ mx := M, smx := SM, mc := mc, mn := N, smn := SN, mnc := nc } : Nd),
        ({ lval := if LV = inf then none else some LV, ladd := LA } : Tag)) := by
  subst eg e54 e55 e56 e57
  by_cases hg : N < Z5
  · simp only [Cellh.capMinC, hg, if_true, updMin, negNd, updMax, tagMin]
    by_cases h1 : M = N
    · subst h1
      by_cases h3 : LV = inf <;> by_cases h4 : LV < Z5 <;> simp [h3, h4, hZ5] <;> (try split_ifs) <;> (try omega)
    · have h1' : ¬ N = M := fun h => h1 h.symm
      by_cases h2 : SM = N
      · subst h2
        by_cases h3 : LV = inf <;> by_cases h4 : LV < Z5 <;> simp [h1, h1', h3, h4, hZ5] <;> (try split_ifs) <;> (try omega)
      · have h2' : ¬ N = SM := fun h => h2 h.symm
        by_cases h3 : LV = inf <;> by_cases h4 : LV < Z5 <;> simp [h1, h1', h2, h2', h3, h4, hZ5] <;> (try split_ifs) <;> (try omega)
  · simp [Cellh.capMinC, hg]

theorem addC_eq (Z8 m0 sm0 mc0 n0 sn0 nc0 la0 lv0 inf A44 A45 A46 A47 : Int)
    (e44 : A44 = (if (sm0 ≠ (-inf)) then (sm0 + Z8) else sm0))
    (e45 : A45 = (if (sn0 ≠ inf) then (sn0 + Z8) else sn0))
    (e46 : A46 = (if (lv0 = inf) then (la0 + Z8) else la0))
    (e47 : A47 = (if (lv0 ≠ inf) then (lv0 + Z8) else lv0))
    (hinfI : inf = INF) (hlv : lv0 ≠ inf → lv0 + Z8 ≠ inf) :
    Cellh.addC Z8
      (({ mx := m0, smx := sm0, mc := mc0, mn := n0, smn := sn0, mnc := nc0 } : Nd),
        ({ lval := if lv0 = inf then none else some lv0, ladd := la0 } : Tag)) =
    (({ mx := m0 + Z8, smx := A44, mc := mc0, mn := n0 + Z8, smn := A45, mnc := nc0 } : Nd),
      ({ lval := if A47 = inf then none else some A47, ladd := A46 } : Tag)) := by
  subst e44 e45 e46 e47
  subst hinfI
  simp only [Cellh.addC, addNd, tagAdd]
  by_cases h7 : lv0 = INF
  · simp [h7]
  · have := hlv h7
    simp [h7, this]

/-- One child of `push` when the parent holds an add tag (`lval = inf`): the C++ chain equals `applyTagC`. -/
theorem child_add_key (Z3 Z5 Z8 m0 sm0 mc0 n0 sn0 nc0 la0 lv0 inf : Int)
    (A44 A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57 : Int)
    (e44 : A44 = (if (sm0 ≠ (-inf)) then (sm0 + Z8) else sm0))
    (e45 : A45 = (if (sn0 ≠ inf) then (sn0 + Z8) else sn0))
    (e46 : A46 = (if (lv0 = inf) then (la0 + Z8) else la0))
    (e47 : A47 = (if (lv0 ≠ inf) then (lv0 + Z8) else lv0))
    (e48 : A48 = (if (Z3 < (m0 + Z8)) then 1 else 0))
    (e49 : A49 = (if (A48 = 1) then Z3 else (m0 + Z8)))
    (e50 : A50 = (if ((A48 = 1) ∧ ((m0 + Z8) = (n0 + Z8))) then Z3 else (n0 + Z8)))
    (e51 : A51 = (if (((A48 = 1) ∧ ((m0 + Z8) ≠ (n0 + Z8))) ∧ ((m0 + Z8) = A45)) then Z3 else A45))
    (e52 : A52 = (if (((A48 = 1) ∧ (A47 ≠ inf)) ∧ (Z3 < A47)) then Z3 else A47))
    (e53 : A53 = (if (A50 < Z5) then 1 else 0))
    (e54 : A54 = (if (A53 = 1) then Z5 else A50))
    (e55 : A55 = (if ((A53 = 1) ∧ (A49 = A50)) then Z5 else A49))
    (e56 : A56 = (if (((A53 = 1) ∧ (A49 ≠ A50)) ∧ (A44 = A50)) then Z5 else A44))
    (e57 : A57 = (if (((A53 = 1) ∧ (A52 ≠ inf)) ∧ (A52 < Z5)) then Z5 else A52))
    (hinfI : inf = INF) (hZ3 : Z3 ≠ inf) (hZ5 : Z5 ≠ inf) (hlv : lv0 ≠ inf → lv0 + Z8 ≠ inf) :
    (({ mx := A55, smx := A56, mc := mc0, mn := A54, smn := A51, mnc := nc0 } : Nd),
      ({ lval := if A57 = inf then none else some A57, ladd := A46 } : Tag)) =
    Cellh.capMinC Z5 (Cellh.capMaxC Z3 (Cellh.addC Z8
      (({ mx := m0, smx := sm0, mc := mc0, mn := n0, smn := sn0, mnc := nc0 } : Nd),
        ({ lval := if lv0 = inf then none else some lv0, ladd := la0 } : Tag)))) := by
  have h1 := capMax_step Z3 (m0 + Z8) A44 mc0 (n0 + Z8) A45 nc0 A47 A46 inf A48 A49 A50 A51 A52 e48 e49 e50 e51 e52 hZ3
  have h2 := capMin_step Z5 A49 A44 mc0 A50 A51 nc0 A52 A46 inf A53 A54 A55 A56 A57 e53 e54 e55 e56 e57 hZ5
  rw [addC_eq Z8 m0 sm0 mc0 n0 sn0 nc0 la0 lv0 inf A44 A45 A46 A47 e44 e45 e46 e47 hinfI hlv, ← h1]
  exact h2

/-- One child of `push` when the parent holds an assignment tag. -/
theorem child_set_key (Zlv Zlen len inf : Int) (hinfI : inf = INF) (hne : Zlv ≠ inf) (hlen : Zlen = len) (c : Cellh) :
    (({ mx := Zlv, smx := -inf, mc := Zlen, mn := Zlv, smn := inf, mnc := Zlen } : Nd),
      ({ lval := some Zlv, ladd := 0 } : Tag)) = Cellh.setC len Zlv c := by
  subst hinfI hlen
  simp [Cellh.setC, setNd, tagSet]

theorem StkRep_push (b B : BS) (sp : Nat) (f : Fr) (S : List Fr) (c1 c2 : Fr) (h : StkRep b sp (f :: S))
    (hk : ∀ i, i < sp - 1 → B.sk.getD i 0 = b.sk.getD i 0) (hl : ∀ i, i < sp - 1 → B.sl.getD i 0 = b.sl.getD i 0)
    (hr : ∀ i, i < sp - 1 → B.sr.getD i 0 = b.sr.getD i 0)
    (h2 : B.sk.getD (sp - 1) 0 = (c2.k : Int) ∧ B.sl.getD (sp - 1) 0 = (c2.lo : Int) ∧ B.sr.getD (sp - 1) 0 = (c2.hi : Int))
    (h1 : B.sk.getD (sp - 1 + 1) 0 = (c1.k : Int) ∧ B.sl.getD (sp - 1 + 1) 0 = (c1.lo : Int) ∧ B.sr.getD (sp - 1 + 1) 0 = (c1.hi : Int)) :
    StkRep B (sp - 1 + 2) (c1 :: c2 :: S) := by
  obtain ⟨hlen, hall⟩ := h
  simp at hlen
  refine ⟨by simp; omega, fun j g hj => ?_⟩
  rcases j with _ | _ | j
  · simp at hj; subst hj
    have e : sp - 1 + 2 - 1 - 0 = sp - 1 + 1 := by omega
    rw [e]; exact h1
  · simp at hj; subst hj
    have e : sp - 1 + 2 - 1 - (0 + 1) = sp - 1 := by omega
    rw [e]; exact h2
  · have hj' : S[j]? = some g := by simpa using hj
    have := hall (j + 1) g (by simpa using hj')
    have hjS : j < S.length := by
      by_contra hc
      have := List.getElem?_eq_none (by omega : S.length ≤ j)
      rw [this] at hj'; cases hj'
    have e : sp - 1 + 2 - 1 - (j + 1 + 1) = sp - 1 - (j + 1) := by omega
    have hlt : sp - 1 - (j + 1) < sp - 1 := by omega
    rw [e, hk _ hlt, hl _ hlt, hr _ hlt]
    exact this

theorem EntRep_push (b B : BS) (ne : Nat) (E : List Nat) (e : Nat) (h : EntRep b ne E)
    (hent : ∀ i, i < ne → B.ent.getD i 0 = b.ent.getD i 0) (hne : B.ent.getD ne 0 = (e : Int)) : EntRep B (ne + 1) (e :: E) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], fun j g hj => ?_⟩
  rcases j with _ | j
  · simp at hj; subst hj
    simpa using hne
  · have hj' : E[j]? = some g := by simpa using hj
    have := h2 j g hj'
    have hjE : j < E.length := by
      by_contra hc
      have := List.getElem?_eq_none (by omega : E.length ≤ j)
      rw [this] at hj'; cases hj'
    have e' : ne + 1 - 1 - (j + 1) = ne - 1 - j := by omega
    have hlt : ne - 1 - j < ne := by omega
    rw [e', hent _ hlt]
    exact this

theorem lastW_pair_fst (a : Nat) (x y d : Int) : (lastW [(a, x), (a + 1, y)] a).getD d = x := by
  have h2 : ¬ a + 1 = a := by omega
  simp [lastW, h2]

theorem lastW_pair_snd (a : Nat) (x y d : Int) : (lastW [(a, x), (a + 1, y)] (a + 1)).getD d = y := by
  simp [lastW]

theorem lastW_single_at (a : Nat) (x d : Int) : (lastW [(a, x)] a).getD d = x := by
  simp [lastW]

theorem ci_sp_down (sp : Nat) (h : 0 < sp) : ci (sp - 1 + 2) = ⟨(ci 0).type, ((sp - 1 : Nat) : Int) + 2⟩ := by
  show (⟨_, _⟩ : Cell) = ⟨_, _⟩
  congr 1
  try omega

theorem ci_ne_up (ne : Nat) : ci (ne + 1) = ⟨(ci 0).type, (ne : Int) + 1⟩ := by
  show (⟨_, _⟩ : Cell) = ⟨_, _⟩
  congr 1

/-- Every array entry is a valid value of its element type. -/
structure ValidOK (b : BS) : Prop where
  v0 : ∀ w ∈ b.mxv, s64.valid w = true
  v1 : ∀ w ∈ b.smx, s64.valid w = true
  v2 : ∀ w ∈ b.mxc, s64.valid w = true
  v3 : ∀ w ∈ b.mnv, s64.valid w = true
  v4 : ∀ w ∈ b.smn, s64.valid w = true
  v5 : ∀ w ∈ b.mnc, s64.valid w = true
  v6 : ∀ w ∈ b.len, s64.valid w = true
  v7 : ∀ w ∈ b.ladd, s64.valid w = true
  v8 : ∀ w ∈ b.lval, s64.valid w = true
  v9 : ∀ w ∈ b.lo, i32.valid w = true
  v10 : ∀ w ∈ b.hi, i32.valid w = true
  v11 : ∀ w ∈ b.sk, i32.valid w = true
  v12 : ∀ w ∈ b.sl, i32.valid w = true
  v13 : ∀ w ∈ b.sr, i32.valid w = true
  v14 : ∀ w ∈ b.ent, i32.valid w = true

/-- The arrays keep their lengths. -/
structure SameLen (b b' : BS) : Prop where
  l0 : b'.mxv.length = b.mxv.length
  l1 : b'.smx.length = b.smx.length
  l2 : b'.mxc.length = b.mxc.length
  l3 : b'.mnv.length = b.mnv.length
  l4 : b'.smn.length = b.smn.length
  l5 : b'.mnc.length = b.mnc.length
  l6 : b'.len.length = b.len.length
  l7 : b'.ladd.length = b.ladd.length
  l8 : b'.lval.length = b.lval.length
  l9 : b'.lo.length = b.lo.length
  l10 : b'.hi.length = b.hi.length
  l11 : b'.sk.length = b.sk.length
  l12 : b'.sl.length = b.sl.length
  l13 : b'.sr.length = b.sr.length
  l14 : b'.ent.length = b.ent.length
  leneq : b'.len = b.len

theorem applySets_length : ∀ (ops : List (Nat × Int)) (l : List Int), (applySets l ops).length = l.length
  | [], l => rfl
  | (i, a) :: ops, l => by
    simp only [applySets]
    rw [applySets_length ops (l.set i a)]
    simp

theorem valid_applySets (P : Int → Prop) : ∀ (ops : List (Nat × Int)) (l : List Int), (∀ w ∈ l, P w) → (∀ p ∈ ops, P p.2) →
    ∀ w ∈ applySets l ops, P w
  | [], l, hl, _ => hl
  | (i, a) :: ops, l, hl, hops => by
    simp only [applySets]
    exact valid_applySets P ops (l.set i a) (valid_set P l i a hl (hops (i, a) (by simp))) (fun p hp => hops p (List.mem_cons_of_mem _ hp))

/-- The generic side conditions of one iteration of the traversal loop. -/
structure IterCtx (b : BS) (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (W0 W1 W2 : Nat) : Prop where
  hinf : s64.valid inf = true
  hninf : s64.valid (-inf) = true
  hnM : n < Proofs.BellmanFordExec.M31
  hopM : op < Proofs.BellmanFordExec.M31
  hqaM : qa < Proofs.BellmanFordExec.M31
  hqbM : qb < Proofs.BellmanFordExec.M31
  hspM : sp < Proofs.BellmanFordExec.M31
  hneM : ne < Proofs.BellmanFordExec.M31
  hsp : 0 < sp
  hx : s64.valid x = true
  hV : ValidOK b
  hW0 : W0 < Proofs.BellmanFordExec.M31
  hW1 : W1 < Proofs.BellmanFordExec.M31
  hW2 : W2 < Proofs.BellmanFordExec.M31
  hk2 : 2 * W0 + 2 < Proofs.BellmanFordExec.M31
  hlohi : W1 + W2 < Proofs.BellmanFordExec.M31
  hne1 : ne + 1 < Proofs.BellmanFordExec.M31
  hsp2 : sp - 1 + 2 < Proofs.BellmanFordExec.M31
  hl0 : 2 * W0 + 2 < b.mxv.length
  hl1 : 2 * W0 + 2 < b.smx.length
  hl2 : 2 * W0 + 2 < b.mxc.length
  hl3 : 2 * W0 + 2 < b.mnv.length
  hl4 : 2 * W0 + 2 < b.smn.length
  hl5 : 2 * W0 + 2 < b.mnc.length
  hl6 : 2 * W0 + 2 < b.len.length
  hl7 : 2 * W0 + 2 < b.ladd.length
  hl8 : 2 * W0 + 2 < b.lval.length
  hlsk : sp + 1 < b.sk.length
  hlsl : sp + 1 < b.sl.length
  hlsr : sp + 1 < b.sr.length
  hlent : ne < b.ent.length

/-- The arrays describe the heap `H`: the node summaries agree everywhere; the tags agree at every node that is not a leaf;
a leaf carries no tag (`lval = inf`, `ladd = 0`), which is what the C++ code keeps true. -/
def HRel (inf : Int) (b : BS) (H : Heap) : Prop :=
  ∀ i, decNd b i = (H i).1 ∧ (b.len.getD i 0 ≠ 1 → decTag inf b i = (H i).2) ∧ (b.len.getD i 0 = 1 → decTag inf b i = noTag)

/-- Only the cell `k` changes. -/
theorem HRel_set (inf : Int) (b b' : BS) (H : Heap) (k : Nat) (c2 : Cellh) (hH : HRel inf b H)
    (hB : ∀ i, i ≠ k → decNd b' i = decNd b i ∧ decTag inf b' i = decTag inf b i) (hlen : b'.len = b.len)
    (hn : decNd b' k = c2.1) (ht : b.len.getD k 0 ≠ 1 → decTag inf b' k = c2.2)
    (hl : b.len.getD k 0 = 1 → decTag inf b' k = noTag) : HRel inf b' (H.set k c2) := by
  intro i
  rw [hlen]
  by_cases hi : i = k
  · subst hi
    simp only [Heap.set_eq]
    exact ⟨hn, ht, hl⟩
  · rw [Heap.set_ne _ _ _ _ hi]
    obtain ⟨h1, h2, h3⟩ := hH i
    obtain ⟨h4, h5⟩ := hB i hi
    exact ⟨by rw [h4]; exact h1, fun h => by rw [h5]; exact h2 h, fun h => by rw [h5]; exact h3 h⟩

/-- The three cells of a `push` change (in the order `2k+1`, `2k+2`, `k`). -/
theorem HRel_set3 (inf : Int) (b b' : BS) (H : Heap) (k1 k2 k3 : Nat) (c1 c2 c3 : Cellh) (hH : HRel inf b H)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hB : ∀ i, i ≠ k1 → i ≠ k2 → i ≠ k3 → decNd b' i = decNd b i ∧ decTag inf b' i = decTag inf b i) (hlen : b'.len = b.len)
    (hn1 : decNd b' k1 = c1.1) (ht1 : b.len.getD k1 0 ≠ 1 → decTag inf b' k1 = c1.2) (hl1 : b.len.getD k1 0 = 1 → decTag inf b' k1 = noTag)
    (hn2 : decNd b' k2 = c2.1) (ht2 : b.len.getD k2 0 ≠ 1 → decTag inf b' k2 = c2.2) (hl2 : b.len.getD k2 0 = 1 → decTag inf b' k2 = noTag)
    (hn3 : decNd b' k3 = c3.1) (ht3 : b.len.getD k3 0 ≠ 1 → decTag inf b' k3 = c3.2) (hl3 : b.len.getD k3 0 = 1 → decTag inf b' k3 = noTag) :
    HRel inf b' (((H.set k1 c1).set k2 c2).set k3 c3) := by
  intro i
  rw [hlen]
  by_cases e3 : i = k3
  · subst e3; simp only [Heap.set_eq]; exact ⟨hn3, ht3, hl3⟩
  · rw [Heap.set_ne _ _ _ _ e3]
    by_cases e2 : i = k2
    · subst e2; simp only [Heap.set_eq]; exact ⟨hn2, ht2, hl2⟩
    · rw [Heap.set_ne _ _ _ _ e2]
      by_cases e1 : i = k1
      · subst e1; simp only [Heap.set_eq]; exact ⟨hn1, ht1, hl1⟩
      · rw [Heap.set_ne _ _ _ _ e1]
        obtain ⟨h1, h2, h3⟩ := hH i
        obtain ⟨h4, h5⟩ := hB i e1 e2 e3
        exact ⟨by rw [h4]; exact h1, fun h => by rw [h5]; exact h2 h, fun h => by rw [h5]; exact h3 h⟩

theorem HRel_stable (inf : Int) (b b' : BS) (H : Heap) (hH : HRel inf b H)
    (hB : ∀ i, decNd b' i = decNd b i ∧ decTag inf b' i = decTag inf b i) (hlen : b'.len = b.len) : HRel inf b' H := by
  intro i
  rw [hlen]
  obtain ⟨h1, h2, h3⟩ := hH i
  obtain ⟨h4, h5⟩ := hB i
  exact ⟨by rw [h4]; exact h1, fun h => by rw [h5]; exact h2 h, fun h => by rw [h5]; exact h3 h⟩

theorem capMaxC_fst (x : Int) (c c' : Cellh) (h : c.1 = c'.1) : (Cellh.capMaxC x c).1 = (Cellh.capMaxC x c').1 := by
  simp only [Cellh.capMaxC, h]; split_ifs <;> first | rfl | exact h
theorem capMinC_fst (x : Int) (c c' : Cellh) (h : c.1 = c'.1) : (Cellh.capMinC x c).1 = (Cellh.capMinC x c').1 := by
  simp only [Cellh.capMinC, h]; split_ifs <;> first | rfl | exact h
theorem capMaxC_tag (x : Int) (c c' : Cellh) (h : c = c') : Cellh.capMaxC x c = Cellh.capMaxC x c' := by rw [h]

theorem HRel_of_act (inf : Int) (b b' : BS) (H : Heap) (k : Nat) (act : Cellh → Cellh) (hH : HRel inf b H)
    (hHof : Hof inf b' = (Hof inf b).set k (act (Hof inf b k))) (hlen : b'.len = b.len)
    (hfst : ∀ c c' : Cellh, c.1 = c'.1 → (act c).1 = (act c').1)
    (hleaf : ∀ nd : Nd, (act (nd, noTag)).2 = noTag) : HRel inf b' (H.set k (act (H k))) := by
  have hk := hH k
  have hcell : ∀ i, (Hof inf b' i) = ((Hof inf b).set k (act (Hof inf b k))) i := fun i => by rw [hHof]
  apply HRel_set inf b b' H k _ hH
  · intro i hi
    have := hcell i
    rw [Heap.set_ne _ _ _ _ hi] at this
    simp only [Hof, Prod.mk.injEq] at this
    exact this
  · exact hlen
  · have h0 := congrArg Prod.fst (hcell k)
    rw [Heap.set_eq] at h0
    have h1 : (Hof inf b k).1 = (H k).1 := hk.1
    have h4 : decNd b' k = (act (Hof inf b k)).1 := h0
    rw [h4]
    exact hfst _ _ h1
  · intro hl
    have := hcell k
    rw [Heap.set_eq] at this
    have h2 : Hof inf b k = H k := Prod.ext hk.1 (hk.2.1 hl)
    have h3 : decTag inf b' k = (act (Hof inf b k)).2 := by
      have := congrArg Prod.snd this
      simpa [Hof] using this
    rw [h3, h2]
  · intro hl
    have := hcell k
    rw [Heap.set_eq] at this
    have h2 : Hof inf b k = (decNd b k, noTag) := Prod.ext rfl (hk.2.2 hl)
    have h3 : decTag inf b' k = (act (Hof inf b k)).2 := by
      have := congrArg Prod.snd this
      simpa [Hof] using this
    rw [h3, h2]
    exact hleaf _

theorem capMaxC_noTag (x : Int) (nd : Nd) : (Cellh.capMaxC x (nd, noTag)).2 = noTag := by
  unfold Cellh.capMaxC
  split_ifs <;> simp [tagMax, noTag]

theorem capMinC_noTag (x : Int) (nd : Nd) : (Cellh.capMinC x (nd, noTag)).2 = noTag := by
  unfold Cellh.capMinC
  split_ifs <;> simp [tagMin, noTag]

theorem tag_noTag_iff (Z7 Z8 inf : Int) :
    (({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag) = noTag) ↔ (Z7 = inf ∧ Z8 = 0) := by
  by_cases h : Z7 = inf <;> simp [noTag, h]

theorem set_nd_key (Zlen len inf x : Int) (hinfI : inf = INF) (hlen : Zlen = len) :
    ({ mx := x, smx := -inf, mc := Zlen, mn := x, smn := inf, mnc := Zlen } : Nd) = setNd len x := by
  subst hinfI hlen; simp [setNd]

theorem set_tag_key (Zlen Z7 Z8 x inf X31 X32 : Int)
    (e31 : X31 = (if (Zlen ≠ 1) then x else Z7)) (e32 : X32 = (if (Zlen ≠ 1) then 0 else Z8)) (hx : x ≠ inf) :
    (Zlen ≠ 1 → ({ lval := if X31 = inf then none else some X31, ladd := X32 } : Tag) = tagSet x) ∧
    (Zlen = 1 → Z7 = inf → Z8 = 0 → ({ lval := if X31 = inf then none else some X31, ladd := X32 } : Tag) = noTag) := by
  subst e31 e32
  refine ⟨fun h => ?_, fun h h7 h8 => ?_⟩
  · simp [h, hx, tagSet]
  · simp [h, h7, h8, noTag]

theorem add_nd_key (Z3 Z4 Z5 Z6 mc nc x inf X21 X22 : Int)
    (e21 : X21 = (if (Z4 ≠ (-inf)) then (Z4 + x) else Z4))
    (e22 : X22 = (if (Z6 ≠ inf) then (Z6 + x) else Z6)) (hinfI : inf = INF) :
    ({ mx := Z3 + x, smx := X21, mc := mc, mn := Z5 + x, smn := X22, mnc := nc } : Nd) =
      addNd ({ mx := Z3, smx := Z4, mc := mc, mn := Z5, smn := Z6, mnc := nc } : Nd) x := by
  subst e21 e22 hinfI
  simp [addNd]

theorem add_tag_key (Zlen Z7 Z8 x inf X23 X24 : Int)
    (e23 : X23 = (if ((Z7 = inf) ∧ (Zlen ≠ 1)) then (Z8 + x) else Z8))
    (e24 : X24 = (if ((Z7 ≠ inf) ∧ (Zlen ≠ 1)) then (Z7 + x) else Z7))
    (hadd7 : Z7 ≠ inf → Z7 + x ≠ inf) :
    (Zlen ≠ 1 → ({ lval := if X24 = inf then none else some X24, ladd := X23 } : Tag) =
      tagAdd ({ lval := if Z7 = inf then none else some Z7, ladd := Z8 } : Tag) x) ∧
    (Zlen = 1 → Z7 = inf → Z8 = 0 → ({ lval := if X24 = inf then none else some X24, ladd := X23 } : Tag) = noTag) := by
  subst e23 e24
  refine ⟨fun h => ?_, fun h h7 h8 => ?_⟩
  · by_cases h7 : Z7 = inf
    · simp [h, h7, tagAdd]
    · have := hadd7 h7
      simp [h, h7, this, tagAdd]
  · simp [h, h7, h8, noTag]

theorem addC_fst (Z8 m0 sm0 mc0 n0 sn0 nc0 inf A44 A45 : Int) (c : Cellh)
    (hc : c.1 = ({ mx := m0, smx := sm0, mc := mc0, mn := n0, smn := sn0, mnc := nc0 } : Nd))
    (e44 : A44 = (if (sm0 ≠ (-inf)) then (sm0 + Z8) else sm0))
    (e45 : A45 = (if (sn0 ≠ inf) then (sn0 + Z8) else sn0)) (hinfI : inf = INF) :
    (Cellh.addC Z8 c).1 = ({ mx := m0 + Z8, smx := A44, mc := mc0, mn := n0 + Z8, smn := A45, mnc := nc0 } : Nd) := by
  subst e44 e45 hinfI
  simp [Cellh.addC, hc, addNd]

/-- The node part of one child of `push` under an add tag (independent of the tag of the child). -/
theorem child_add_nd (Z3 Z5 Z8 m0 sm0 mc0 n0 sn0 nc0 inf : Int)
    (A44 A45 A48 A49 A50 A51 A53 A54 A55 A56 : Int) (c : Cellh)
    (hc : c.1 = ({ mx := m0, smx := sm0, mc := mc0, mn := n0, smn := sn0, mnc := nc0 } : Nd))
    (e44 : A44 = (if (sm0 ≠ (-inf)) then (sm0 + Z8) else sm0))
    (e45 : A45 = (if (sn0 ≠ inf) then (sn0 + Z8) else sn0))
    (e48 : A48 = (if (Z3 < (m0 + Z8)) then 1 else 0))
    (e49 : A49 = (if (A48 = 1) then Z3 else (m0 + Z8)))
    (e50 : A50 = (if ((A48 = 1) ∧ ((m0 + Z8) = (n0 + Z8))) then Z3 else (n0 + Z8)))
    (e51 : A51 = (if (((A48 = 1) ∧ ((m0 + Z8) ≠ (n0 + Z8))) ∧ ((m0 + Z8) = A45)) then Z3 else A45))
    (e53 : A53 = (if (A50 < Z5) then 1 else 0))
    (e54 : A54 = (if (A53 = 1) then Z5 else A50))
    (e55 : A55 = (if ((A53 = 1) ∧ (A49 = A50)) then Z5 else A49))
    (e56 : A56 = (if (((A53 = 1) ∧ (A49 ≠ A50)) ∧ (A44 = A50)) then Z5 else A44))
    (hinfI : inf = INF) (hZ3 : Z3 ≠ inf) (hZ5 : Z5 ≠ inf) :
    (Cellh.capMinC Z5 (Cellh.capMaxC Z3 (Cellh.addC Z8 c))).1 =
      ({ mx := A55, smx := A56, mc := mc0, mn := A54, smn := A51, mnc := nc0 } : Nd) := by
  have ha := addC_fst Z8 m0 sm0 mc0 n0 sn0 nc0 inf A44 A45 c hc e44 e45 hinfI
  obtain ⟨A52d, he52⟩ : ∃ v : Int, v = (if (((A48 = 1) ∧ ((0 : Int) ≠ inf)) ∧ Z3 < 0) then Z3 else 0) := ⟨_, rfl⟩
  have h1 := capMax_step Z3 (m0 + Z8) A44 mc0 (n0 + Z8) A45 nc0 0 0 inf A48 A49 A50 A51 A52d e48 e49 e50 e51 he52 hZ3
  obtain ⟨A57d, he57⟩ : ∃ v : Int, v = (if (((A53 = 1) ∧ (A52d ≠ inf)) ∧ A52d < Z5) then Z5 else A52d) := ⟨_, rfl⟩
  have h2 := capMin_step Z5 A49 A44 mc0 A50 A51 nc0 A52d 0 inf A53 A54 A55 A56 A57d e53 e54 e55 e56 he57 hZ5
  have hA : (Cellh.capMaxC Z3 (Cellh.addC Z8 c)).1 = ({ mx := A49, smx := A44, mc := mc0, mn := A50, smn := A51, mnc := nc0 } : Nd) := by
    have := capMaxC_fst Z3 (Cellh.addC Z8 c)
      (({ mx := m0 + Z8, smx := A44, mc := mc0, mn := n0 + Z8, smn := A45, mnc := nc0 } : Nd),
        ({ lval := if (0 : Int) = inf then none else some 0, ladd := 0 } : Tag)) (by rw [ha])
    rw [this]
    exact (congrArg Prod.fst h1).symm
  have := capMinC_fst Z5 (Cellh.capMaxC Z3 (Cellh.addC Z8 c))
    (({ mx := A49, smx := A44, mc := mc0, mn := A50, smn := A51, mnc := nc0 } : Nd),
      ({ lval := if A52d = inf then none else some A52d, ladd := 0 } : Tag)) hA
  rw [this]
  exact (congrArg Prod.fst h2).symm

theorem child_set_tag (Zlen Zlv Zlc Zla X43 : Int) (inf : Int)
    (e43 : X43 = (if (Zlen ≠ 1) then Zlv else Zlc)) (hne : Zlv ≠ inf) :
    (Zlen ≠ 1 → ({ lval := if X43 = inf then none else some X43, ladd := 0 } : Tag) = tagSet Zlv) ∧
    (Zlen = 1 → Zlc = inf → Zla = 0 → ({ lval := if X43 = inf then none else some X43, ladd := 0 } : Tag) = noTag) := by
  subst e43
  refine ⟨fun h => ?_, fun h h7 _ => ?_⟩
  · simp [h, hne, tagSet]
  · simp [h, h7, noTag]

theorem child_add_tag (Z3 Z5 Z8 m0 sm0 mc0 n0 sn0 nc0 la0 lv0 inf Zlen : Int)
    (A44 A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57 : Int)
    (e44 : A44 = (if (sm0 ≠ (-inf)) then (sm0 + Z8) else sm0))
    (e45 : A45 = (if (sn0 ≠ inf) then (sn0 + Z8) else sn0))
    (e46 : A46 = (if ((lv0 = inf) ∧ (Zlen ≠ 1)) then (la0 + Z8) else la0))
    (e47 : A47 = (if (lv0 ≠ inf) then (lv0 + Z8) else lv0))
    (e48 : A48 = (if (Z3 < (m0 + Z8)) then 1 else 0))
    (e49 : A49 = (if (A48 = 1) then Z3 else (m0 + Z8)))
    (e50 : A50 = (if ((A48 = 1) ∧ ((m0 + Z8) = (n0 + Z8))) then Z3 else (n0 + Z8)))
    (e51 : A51 = (if (((A48 = 1) ∧ ((m0 + Z8) ≠ (n0 + Z8))) ∧ ((m0 + Z8) = A45)) then Z3 else A45))
    (e52 : A52 = (if (((A48 = 1) ∧ (A47 ≠ inf)) ∧ (Z3 < A47)) then Z3 else A47))
    (e53 : A53 = (if (A50 < Z5) then 1 else 0))
    (e54 : A54 = (if (A53 = 1) then Z5 else A50))
    (e55 : A55 = (if ((A53 = 1) ∧ (A49 = A50)) then Z5 else A49))
    (e56 : A56 = (if (((A53 = 1) ∧ (A49 ≠ A50)) ∧ (A44 = A50)) then Z5 else A44))
    (e57 : A57 = (if (((A53 = 1) ∧ (A52 ≠ inf)) ∧ (A52 < Z5)) then Z5 else A52))
    (hinfI : inf = INF) (hZ3 : Z3 ≠ inf) (hZ5 : Z5 ≠ inf) (hlv : lv0 ≠ inf → lv0 + Z8 ≠ inf) :
    (Zlen ≠ 1 → ({ lval := if A57 = inf then none else some A57, ladd := A46 } : Tag) =
      (Cellh.capMinC Z5 (Cellh.capMaxC Z3 (Cellh.addC Z8
        (({ mx := m0, smx := sm0, mc := mc0, mn := n0, smn := sn0, mnc := nc0 } : Nd),
          ({ lval := if lv0 = inf then none else some lv0, ladd := la0 } : Tag))))).2) ∧
    (Zlen = 1 → lv0 = inf → la0 = 0 → ({ lval := if A57 = inf then none else some A57, ladd := A46 } : Tag) = noTag) := by
  refine ⟨fun hl => ?_, fun hl h7 h8 => ?_⟩
  · have e46' : A46 = (if (lv0 = inf) then (la0 + Z8) else la0) := by rw [e46]; simp [hl]
    have := child_add_key Z3 Z5 Z8 m0 sm0 mc0 n0 sn0 nc0 la0 lv0 inf A44 A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57
      e44 e45 e46' e47 e48 e49 e50 e51 e52 e53 e54 e55 e56 e57 hinfI hZ3 hZ5 hlv
    exact congrArg Prod.snd this
  · have e46' : A46 = la0 := by rw [e46]; simp [hl]
    have e47' : A47 = inf := by rw [e47]; simp [h7]
    have e52' : A52 = inf := by rw [e52, e47']; simp
    have e57' : A57 = inf := by rw [e57, e52']; simp
    rw [e46', e57', h8]
    simp [noTag]

end Proofs.BeatsRep
