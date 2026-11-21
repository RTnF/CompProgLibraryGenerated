import Proofs.Cpp.Gen.FindCycle
import Proofs.Cpp.Lib.Basic
import Proofs.Math.FindCycleSpec
import Proofs.Math.FindCyclePhi

/-! # `find_cycle` (library/graph/find_cycle.hpp)

The translated model refines the machine `FS` of `Proofs.FindCycleInv` (invariant `FInv`; one step of the search is
`fRoot`, `fPush`, `fSkip` or `fPop`, and the search stops when it meets a grey vertex, giving `Found`). The arrays of
the C++ state are the fields of `FS` on `0 .. n-1` (`Abs`); the ghost fields `Fi`, `nb` exist (`∃ st`). The potential
`phiF` (unscanned arcs, white vertices, the stack) bounds the iterations. After the search the stack from the grey
vertex up is copied to `cyc` (`Proofs.FindCycleSpec.cycout_of_found`), or there is no cycle
(`Proofs.FindCycleSpec.acyclic_of_done`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.LowlinkInv Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.FindCycleSpec Proofs.FindCyclePhi
open Proofs.LowlinkPhiMath (sum_map_le)

namespace Proofs.Cpp.FindCycle

/-- The CSR arrays as functions. -/
def hdF (head : Array Int) : Nat → Nat := fun v => head[v]!.toNat
def tgF (target : Array Int) : Nat → Nat := fun q => target[q]!.toNat

/-- The preconditions on the CSR graph. -/
structure Pre (head target : Array Int) (n : Nat) : Prop where
  hsize : head.size = n + 1
  hnn : ∀ v, v ≤ n → 0 ≤ head[v]!
  G : FGH n (hdF head) (tgF target)
  tnn : ∀ x q, x < n → hdF head x ≤ q → q < hdF head (x + 1) → 0 ≤ target[q]!
  bound : hdF head n + 3 * n < 2 ^ 62

/-- The C++ arrays hold the fields of `st` on the vertices `0 .. n-1`. -/
def Abs (n : Nat) (state it stk : Array Int) (sp : Int) (st : FS) : Prop :=
  state.size = n ∧ it.size = n ∧ stk.size = n ∧ (∀ v, v < n → state[v]! = st.C v ∧ it[v]! = st.It v) ∧
  (∀ i, i < st.sp → stk[i]! = (st.Sk i : Int)) ∧ sp = st.sp

/-- The stack when a back arc to `fw` was found at height `fsp`. -/
def FoundC (head target : Array Int) (n : Nat) (stk : Array Int) (fsp fw : Int) : Prop :=
  0 < fsp ∧ 0 ≤ fw ∧ stk.size = n ∧ (∀ i, i < fsp.toNat → 0 ≤ stk[i]!) ∧
  Found n (hdF head) (tgF target) (fun i => stk[i]!.toNat) fsp.toNat fw.toNat

/-- The initial potential: all arcs and all vertices. -/
def P0 (head : Array Int) (n : Nat) : Nat := ((List.range n).map (fun a => hdF head (a + 1) - hdF head a)).sum + n

/-- The invariant of the outer loop after the roots `0 .. k-1`. -/
def OI (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw : Int) (c t0 : Nat) : Prop :=
  (fsp = 0 ∧ ∃ st, FInv n (hdF head) (tgF target) st ∧ Abs n state it stk 0 st ∧ st.sp = 0 ∧
    (∀ v, v < k → st.C v ≠ 0) ∧ c + phiF n (hdF head) st ≤ t0 + 1 + 2 * k + P0 head n) ∨
  (FoundC head target n stk fsp fw ∧ c ≤ t0 + 1 + 2 * k + P0 head n)

/-- The invariant of the depth-first search from the root `k`. -/
def II (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw sp : Int) (c t0 : Nat) : Prop :=
  (fsp = 0 ∧ ∃ st, FInv n (hdF head) (tgF target) st ∧ Abs n state it stk sp st ∧
    (∀ v, v < k + 1 → st.C v ≠ 0) ∧ c + phiF n (hdF head) st ≤ t0 + 1 + 2 * k + 1 + P0 head n) ∨
  (sp = 0 ∧ FoundC head target n stk fsp fw ∧ c ≤ t0 + 1 + 2 * k + 1 + P0 head n)

/-- `phiF` computed from the C++ state. -/
def phiC (head : Array Int) (n : Nat) (state it : Array Int) (sp : Int) : Nat :=
  ((List.range n).map (fun a => hdF head (a + 1) - (if state[a]! ≠ 0 then it[a]!.toNat else hdF head a))).sum +
    ((List.range n).map (fun a => if state[a]! = 0 then 1 else 0)).sum + sp.toNat

/-- The measure of the search loop: it drops to `0` when a cycle is found. -/
def mu (head : Array Int) (n : Nat) (state it : Array Int) (fsp sp : Int) : Nat :=
  if fsp = 0 then phiC head n state it sp + 1 else 0

theorem head_eq (head : Array Int) (v : Nat) (h : 0 ≤ head[v]!) : head[v]! = (hdF head v : Int) := by
  unfold hdF; omega

theorem get_set (A : Array Int) (i : Int) (x : Int) (hi0 : 0 ≤ i) (hi : i.toNat < A.size) (v : Nat) :
    (set A i x)[v]! = upd (fun u => A[u]!) i.toNat x v := by
  rw [getElemBang_set _ _ _ _ hi]; unfold upd; rfl

theorem tele (hd : Nat → Nat) (n : Nat) (hm : ∀ x, x < n → hd x ≤ hd (x + 1)) :
    ((List.range n).map (fun a => hd (a + 1) - hd a)).sum + hd 0 = hd n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := ih (fun x hx => hm x (by omega))
    have := hm n (by omega)
    omega

theorem white_le (n : Nat) (f : Nat → Nat) (h : ∀ a, f a ≤ 1) : ((List.range n).map f).sum ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := h n
    omega

theorem phi_le (head target : Array Int) (n : Nat) (P : Pre head target n) (st : FS)
    (I : FInv n (hdF head) (tgF target) st) : phiF n (hdF head) st ≤ hdF head n + 2 * n := by
  unfold phiF unscF whiteF
  have h1 : ((List.range n).map (fun a => hdF head (a + 1) - itNF (hdF head) st a)).sum ≤
      ((List.range n).map (fun a => hdF head (a + 1) - hdF head a)).sum := by
    apply sum_map_le
    intro a _
    unfold itNF
    split
    · rename_i ha; have := (I.it_rng a ha).1; omega
    · omega
  have h2 := tele (hdF head) n (fun x hx => P.G.mono x hx)
  have h3 := I.sp_le
  have h4 := white_le n (fun a => if st.C a = 0 then 1 else 0) (fun a => by split <;> omega)
  omega

theorem phiC_eq (head : Array Int) (n : Nat) (st : FS) (state it stk : Array Int) (sp : Int)
    (A : Abs n state it stk sp st) : phiC head n state it sp = phiF n (hdF head) st := by
  obtain ⟨-, -, -, hv, -, hsp⟩ := A
  unfold phiC phiF unscF whiteF
  have e1 : (List.range n).map (fun a => hdF head (a + 1) - (if state[a]! ≠ 0 then it[a]!.toNat else hdF head a)) =
      (List.range n).map (fun a => hdF head (a + 1) - itNF (hdF head) st a) := by
    apply List.map_congr_left
    intro a ha
    obtain ⟨e1, e2⟩ := hv a (List.mem_range.mp ha)
    unfold itNF; rw [e1, e2]
  have e2 : (List.range n).map (fun a => if state[a]! = 0 then 1 else 0) =
      (List.range n).map (fun a => if st.C a = 0 then 1 else 0) := by
    apply List.map_congr_left
    intro a ha
    rw [(hv a (List.mem_range.mp ha)).1]
  rw [e1, e2, hsp]
  simp

/-- The initial machine: every vertex white, the iterators as in the C++ array. -/
def initF (it : Array Int) : FS :=
  { C := (fun _ => 0), It := (fun v => it[v]!), Fi := (fun _ => 0), Sk := (fun _ => 0), sp := 0, nb := 0 }

theorem inv_initF (n : Nat) (hd tg : Nat → Nat) (it : Array Int) : FInv n hd tg (initF it) :=
  ⟨fun _ => Or.inl rfl, fun _ h => absurd rfl h, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (by simp [initF]), fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (by simp [initF]), fun _ h => absurd rfl h, fun _ h => absurd rfl h,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (by simp [initF]),
    fun _ h => absurd h (by simp [initF])⟩

theorem oi_init (head target : Array Int) (n : Nat) (state it stk : Array Int) (t0 : Nat)
    (hs : state.size = n ∧ it.size = n ∧ stk.size = n) (h0 : ∀ v, v < n → state[v]! = 0) :
    OI head target n 0 state it stk 0 0 (t0 + 1) t0 := by
  refine Or.inl ⟨rfl, initF it, inv_initF _ _ _ _, ?_, rfl, fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hs
    exact ⟨h1, h2, h3, fun v hv => ⟨h0 v hv, rfl⟩, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  · have : phiF n (hdF head) (initF it) = P0 head n := by
      simp only [phiF, unscF, whiteF, itNF, initF, P0, ne_eq, not_true_eq_false, ite_false, ite_true]
      simp
    omega

theorem oi_skip (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw : Int) (c t0 : Nat)
    (H : OI head target n k state it stk fsp fw c t0) (hk : k < n)
    (h : fsp = 0 → get state (k : Int) ≠ 0) :
    OI head target n (k + 1) state it stk fsp fw (c + 1) t0 := by
  rcases H with ⟨hf, st, I, A, hsp, hvis, hc⟩ | ⟨F, hc⟩
  · have hC : st.C k ≠ 0 := by
      have := (A.2.2.2.1 k hk).1; have h' := h hf; simp [get] at h'; omega
    refine Or.inl ⟨hf, st, I, A, hsp, fun v hv => ?_, by omega⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h' | h'
    · exact hvis v h'
    · subst h'; exact hC
  · exact Or.inr ⟨F, by omega⟩

theorem ii_exit (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw sp : Int) (c t0 : Nat)
    (H : II head target n k state it stk fsp fw sp c t0) (h : sp ≤ 0) :
    OI head target n (k + 1) state it stk fsp fw (c + 1) t0 := by
  rcases H with ⟨hf, st, I, A, hvis, hc⟩ | ⟨-, F, hc⟩
  · have hsp : st.sp = 0 := by have := A.2.2.2.2.2; omega
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := A
    exact Or.inl ⟨hf, st, I, ⟨a1, a2, a3, a4, a5, by rw [hsp]; rfl⟩, hsp, hvis, by omega⟩
  · exact Or.inr ⟨F, by omega⟩

theorem ii_root (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw : Int) (c t0 : Nat) (H : OI head target n k state it stk 0 fw c t0) (hk : k < n)
    (h : get state (k : Int) = 0) :
    II head target n k (set state k 1) (set it k (get head k)) (set stk 0 k) 0 fw 1 (c + 1) t0 ∧
    mu head n (set state k 1) (set it k (get head k)) 0 1 < fuel := by
  rcases H with ⟨-, st, I, A, hsp, hvis, hc⟩ | ⟨F, -⟩
  swap
  · exact absurd F.1 (by omega)
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A
  have hC : st.C k = 0 := by have := (a4 k hk).1; simp [get] at h; omega
  have I' := inv_root P.G I hsp hk hC
  have hph := phiF_root n (hdF head) st k hk hC hsp
  have hhk : get head (k : Int) = (hdF head k : Int) := by simp [get]; exact head_eq head k (P.hnn k (by omega))
  have A' : Abs n (set state k 1) (set it k (get head k)) (set stk 0 k) 1 (fRoot (hdF head) st k) := by
    refine ⟨by simp [a1], by simp [a2], by simp [a3], fun v hv => ?_, fun i hi => ?_, by simp [fRoot]⟩
    · obtain ⟨b1, b2⟩ := a4 v hv
      refine ⟨?_, ?_⟩
      · rw [get_set _ _ _ (by omega) (by simp; omega)]; simp only [Int.toNat_natCast, fRoot]
        unfold upd; split
        · rfl
        · exact b1
      · rw [get_set _ _ _ (by omega) (by simp; omega), hhk]; simp only [Int.toNat_natCast, fRoot]
        unfold upd; split
        · rfl
        · exact b2
    · simp [fRoot] at hi; subst hi
      rw [get_set _ _ _ (by omega) (by simp; omega)]; simp [fRoot, upd]
  have hp := phi_le head target n P _ I'
  refine ⟨Or.inl ⟨rfl, _, I', A', fun v hv => ?_, by omega⟩, ?_⟩
  · show (upd st.C k 1) v ≠ 0
    unfold upd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h' | h'
    · split
      · omega
      · exact hvis v h'
    · subst h'; simp
  · simp only [mu, ↓reduceIte]
    rw [phiC_eq head n _ _ _ _ _ A']
    have := P.bound; simp only [fuel]; omega

/-- The facts about the top of the stack. -/
theorem top_facts (head target : Array Int) (n : Nat) (st : FS) (I : FInv n (hdF head) (tgF target) st)
    (state it stk : Array Int) (sp : Int) (A : Abs n state it stk sp st) (hsp : 0 < sp) :
    0 < st.sp ∧ get stk (sp - 1) = (st.Sk (st.sp - 1) : Int) ∧ st.C (st.Sk (st.sp - 1)) = 1 ∧
      st.Sk (st.sp - 1) < n := by
  obtain ⟨-, -, -, -, a5, a6⟩ := A
  have h0 : 0 < st.sp := by omega
  have hg := top_gray I h0 rfl
  refine ⟨h0, ?_, hg, I.c_lt _ (by omega)⟩
  have e : (sp - 1).toNat = st.sp - 1 := by omega
  simp only [get, e]; exact a5 _ (by omega)

theorem arc_facts (head target : Array Int) (n : Nat) (P : Pre head target n) (st : FS)
    (I : FInv n (hdF head) (tgF target) st) (v : Nat) (hvC : st.C v ≠ 0) (hvn : v < n) (itv : Int)
    (hitv : itv = st.It v) (hlt : itv < get head ((v : Int) + 1)) :
    (hdF head v : Int) ≤ st.It v ∧ st.It v < (hdF head (v + 1) : Int) ∧ 0 ≤ itv ∧
      get target itv = (tgF target itv.toNat : Int) ∧ AdjH (hdF head) (tgF target) v (tgF target itv.toNat) ∧
      tgF target itv.toNat < n := by
  have hr := I.it_rng v hvC
  have hh : get head ((v : Int) + 1) = (hdF head (v + 1) : Int) := by
    have e : ((v : Int) + 1).toNat = v + 1 := by omega
    simp only [get, e]; exact head_eq head (v + 1) (P.hnn (v + 1) (by omega))
  rw [hh] at hlt
  have q1 : hdF head v ≤ itv.toNat := by omega
  have q2 : itv.toNat < hdF head (v + 1) := by omega
  have ht := P.tnn v itv.toNat hvn q1 q2
  have hadj : AdjH (hdF head) (tgF target) v (tgF target itv.toNat) := ⟨itv.toNat, q1, q2, rfl⟩
  refine ⟨hr.1, by omega, by omega, ?_, hadj, (P.G.adj_lt _ _ hadj).2⟩
  simp only [get]; unfold tgF; omega

/-- The common start of a step that reads the arc at the cursor of the top vertex. -/
theorem step_facts (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw sp : Int) (c t0 : Nat) (H : II head target n k state it stk 0 fw sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) :
    ∃ st, FInv n (hdF head) (tgF target) st ∧ Abs n state it stk sp st ∧ (∀ u, u < k + 1 → st.C u ≠ 0) ∧
      c + phiF n (hdF head) st ≤ t0 + 1 + 2 * k + 1 + P0 head n ∧
      ∃ vN wN q : Nat, v = vN ∧ w = wN ∧ e = q ∧ st.Sk (st.sp - 1) = vN ∧ 0 < st.sp ∧ st.C vN = 1 ∧ vN < n ∧
        wN < n ∧ (q : Int) = st.It vN ∧ q < hdF head (vN + 1) ∧ tgF target q = wN ∧
        (hdF head vN : Int) ≤ st.It vN ∧ st.It vN < (hdF head (vN + 1) : Int) := by
  rcases H with ⟨-, st, I, A, hvis, hc⟩ | ⟨h, -⟩
  swap
  · omega
  refine ⟨st, I, A, hvis, hc, ?_⟩
  obtain ⟨h0, hstk, hvg, hvn⟩ := top_facts head target n st I _ _ _ _ A hsp
  rw [hstk] at hv; subst hv
  have hitv : get it (st.Sk (st.sp - 1) : Int) = st.It (st.Sk (st.sp - 1)) := by
    simpa [get] using (A.2.2.2.1 _ hvn).2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ :=
    arc_facts head target n P st I _ (by omega) hvn _ hitv hlt
  rw [← he] at f3 f4 f5 f6 hitv
  rw [f4] at hw
  refine ⟨_, _, e.toNat, rfl, hw, by omega, rfl, h0, hvg, hvn, f6, by omega, by omega, rfl, f1, f2⟩

theorem abs_it (n : Nat) (state it stk : Array Int) (sp : Int) (st : FS) (A : Abs n state it stk sp st)
    (vN : Nat) (hvn : vN < n) (e : Int) (he : e = st.It vN) :
    ∀ u, u < n → (set it (vN : Int) (e + 1))[u]! = upd st.It vN (st.It vN + 1) u := by
  intro u hu
  rw [get_set it vN (e + 1) (by omega) (by rw [A.2.1]; simpa using hvn)]; simp only [Int.toNat_natCast]
  unfold upd; split
  · rw [he]
  · exact (A.2.2.2.1 u hu).2

theorem ii_push (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw sp : Int) (c t0 : Nat) (H : II head target n k state it stk 0 fw sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) (hu : get state w = 0) :
    II head target n k (set state w 1) (set (set it v (e + 1)) w (get head w)) (set stk sp w) 0 fw (sp + 1)
      (c + 1) t0 ∧
    mu head n (set state w 1) (set (set it v (e + 1)) w (get head w)) 0 (sp + 1) < mu head n state it 0 sp := by
  obtain ⟨st, I, A, hvis, hc, vN, wN, q, rfl, rfl, rfl, hvN, h0, hvg, hvn, hwn, hq, hit, hwq, f1, f2⟩ :=
    step_facts head target n k P state it stk fw sp c t0 H hsp v e w hv he hw hlt
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A
  have hC : st.C wN = 0 := by have := (a4 wN hwn).1; simp [get] at hu; omega
  have I' := inv_push P.G I h0 hvN hq hit hwq hC
  have hph := phiF_push n (hdF head) st vN wN hvn hwn (by omega) hC f1 f2
  have hhw : get head (wN : Int) = (hdF head wN : Int) := by
    simp only [get, Int.toNat_natCast]; exact head_eq head wN (P.hnn wN (by omega))
  have hspn' : st.sp < n := by
    have hnd : (wN :: (List.range st.sp).map st.Sk).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => ?_, Proofs.PrimMath.nodup_map_inj List.nodup_range st.Sk
        (fun x hx y hy h => I.sk_inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) h)⟩
      obtain ⟨i, hi, hik⟩ := List.mem_map.mp hm
      have := I.sk_gray i (List.mem_range.mp hi)
      rw [hik] at this; omega
    have hsub : (wN :: (List.range st.sp).map st.Sk) ⊆ List.range n := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_range.mpr hwn
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        have := I.sk_gray i (List.mem_range.mp hi)
        exact List.mem_range.mpr (I.c_lt _ (by omega))
    have := List.Nodup.length_le_of_subset hnd hsub
    simp at this; omega
  have hsp9 : sp.toNat = st.sp := by omega
  have A' : Abs n (set state wN 1) (set (set it vN (q + 1)) wN (get head wN)) (set stk sp wN) (sp + 1)
      (fPush (hdF head) st vN wN) := by
    refine ⟨by simp [a1], by simp [a2], by simp [a3], fun u hu' => ?_, fun i hi => ?_, by simp [fPush]; omega⟩
    · refine ⟨?_, ?_⟩
      · rw [get_set state wN 1 (by omega) (by simp [a1]; omega)]; simp only [Int.toNat_natCast, fPush]
        unfold upd; split
        · rfl
        · exact (a4 u hu').1
      · rw [get_set _ wN _ (by omega) (by simp [a2]; omega), hhw]
        simp only [Int.toNat_natCast, fPush]
        unfold upd; split
        · rfl
        · beta_reduce
          have := abs_it n state it stk sp st ⟨a1, a2, a3, a4, a5, a6⟩ vN hvn q hq u hu'
          unfold upd at this; exact this
    · simp only [fPush] at hi
      rw [get_set stk sp wN (by omega) (by simp [a3]; omega)]
      simp only [fPush]; unfold upd
      rw [hsp9]
      split
      · rfl
      · exact a5 i (by omega)
  have hp := phi_le head target n P _ I'
  refine ⟨Or.inl ⟨rfl, _, I', A', fun u hu' => ?_, by omega⟩, ?_⟩
  · show (upd st.C wN 1) u ≠ 0
    unfold upd; split
    · omega
    · exact hvis u hu'
  · simp only [mu, ↓reduceIte]
    rw [phiC_eq head n _ _ _ _ _ A', phiC_eq head n _ _ _ _ _ ⟨a1, a2, a3, a4, a5, a6⟩]
    omega

theorem ii_found (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw sp : Int) (c t0 : Nat) (H : II head target n k state it stk 0 fw sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) (hg : get state w = 1) (it' : Array Int) :
    II head target n k state it' stk sp w 0 (c + 1) t0 ∧ mu head n state it' sp 0 < mu head n state it 0 sp := by
  obtain ⟨st, I, A, hvis, hc, vN, wN, q, rfl, rfl, rfl, hvN, h0, hvg, hvn, hwn, hq, hit, hwq, f1, f2⟩ :=
    step_facts head target n k P state it stk fw sp c t0 H hsp v e w hv he hw hlt
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A
  have hC : st.C wN = 1 := by have := (a4 wN hwn).1; simp [get] at hg; omega
  have F := found_of_inv I h0 hvN hq hit hwq hC
  have hsk : ∀ i, i < st.sp → stk[i]! = (st.Sk i : Int) := a5
  have F' : Found n (hdF head) (tgF target) (fun i => stk[i]!.toNat) sp.toNat (wN : Int).toNat := by
    have e1 : sp.toNat = st.sp := by omega
    rw [e1, Int.toNat_natCast]
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := F
    have hS : ∀ i, i < st.sp → stk[i]!.toNat = st.Sk i := fun i hi => by rw [hsk i hi]; simp
    refine ⟨p1, fun i hi => by rw [hS i hi]; exact p2 i hi, fun i j hi hj h => p3 i j hi hj (by
      rw [hS i hi, hS j hj] at h; exact h), fun i hi => by rw [hS i (by omega), hS (i + 1) hi]; exact p4 i hi, ?_, ?_⟩
    · obtain ⟨j, hj, hjw⟩ := p5; exact ⟨j, hj, by rw [hS j hj]; exact hjw⟩
    · rw [hS _ (by omega)]; exact p6
  have hph := phiF_pop n (hdF head) st vN h0 hvg
  refine ⟨Or.inr ⟨rfl, ⟨hsp, by omega, a3, fun i hi => by rw [hsk i (by omega)]; omega, F'⟩, by omega⟩, ?_⟩
  simp only [mu, if_neg (show sp ≠ 0 by omega), ↓reduceIte]
  omega

theorem ii_skip (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw sp : Int) (c t0 : Nat) (H : II head target n k state it stk 0 fw sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) (h0w : get state w ≠ 0) (h1w : get state w ≠ 1) :
    II head target n k state (set it v (e + 1)) stk 0 fw sp (c + 1) t0 ∧
    mu head n state (set it v (e + 1)) 0 sp < mu head n state it 0 sp := by
  obtain ⟨st, I, A, hvis, hc, vN, wN, q, rfl, rfl, rfl, hvN, h0, hvg, hvn, hwn, hq, hit, hwq, f1, f2⟩ :=
    step_facts head target n k P state it stk fw sp c t0 H hsp v e w hv he hw hlt
  have A0 := A
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A
  have hC : st.C wN = 2 := by
    have := (a4 wN hwn).1; simp [get] at h0w h1w
    rcases I.c_rng wN with h | h | h <;> omega
  have I' := inv_skip I h0 hvN hq hit hwq hC
  have hph := phiF_skip n (hdF head) st vN hvn (by omega) f1 f2
  have A' : Abs n state (set it vN (q + 1)) stk sp (fSkip st vN) :=
    ⟨a1, by simp [a2], a3, fun u hu' => ⟨(a4 u hu').1, abs_it n state it stk sp st A0 vN hvn q hq u hu'⟩, a5, a6⟩
  refine ⟨Or.inl ⟨rfl, _, I', A', hvis, by omega⟩, ?_⟩
  simp only [mu, ↓reduceIte]
  rw [phiC_eq head n _ _ _ _ _ A', phiC_eq head n _ _ _ _ _ A0]
  omega

theorem ii_pop (head target : Array Int) (n k : Nat) (P : Pre head target n) (state it stk : Array Int)
    (fw sp : Int) (c t0 : Nat) (H : II head target n k state it stk 0 fw sp c t0) (hsp : 0 < sp)
    (v : Int) (hv : v = get stk (sp - 1)) (hge : get head (v + 1) ≤ get it v) :
    II head target n k (set state v 2) it stk 0 fw (sp - 1) (c + 1) t0 ∧
    mu head n (set state v 2) it 0 (sp - 1) < mu head n state it 0 sp := by
  rcases H with ⟨-, st, I, A, hvis, hc⟩ | ⟨h, -⟩
  swap
  · omega
  obtain ⟨h0, hstk, hvg, hvn⟩ := top_facts head target n st I _ _ _ _ A hsp
  have A0 := A
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A
  generalize hvN : st.Sk (st.sp - 1) = vN at hstk hvg hvn
  rw [hstk] at hv; subst hv
  have hr := I.it_rng vN (by omega)
  have hh : get head ((vN : Int) + 1) = (hdF head (vN + 1) : Int) := by
    have e : ((vN : Int) + 1).toNat = vN + 1 := by omega
    simp only [get, e]; exact head_eq head (vN + 1) (P.hnn (vN + 1) (by omega))
  have hitv : get it (vN : Int) = st.It vN := by simpa [get] using (a4 vN hvn).2
  rw [hh, hitv] at hge
  have I' := inv_pop I h0 hvN (by omega)
  have hph := phiF_pop n (hdF head) st vN h0 hvg
  have A' : Abs n (set state vN 2) it stk (sp - 1) (fPop st vN) := by
    refine ⟨by simp [a1], a2, a3, fun u hu' => ⟨?_, (a4 u hu').2⟩, fun i hi => a5 i (by simp [fPop] at hi; omega),
      by simp [fPop]; omega⟩
    rw [get_set state vN 2 (by omega) (by simp [a1]; omega)]; simp only [Int.toNat_natCast, fPop]
    unfold upd; split
    · rfl
    · exact (a4 u hu').1
  refine ⟨Or.inl ⟨rfl, _, I', A', fun u hu' => ?_, by omega⟩, ?_⟩
  · show (upd st.C vN 2) u ≠ 0
    unfold upd; split
    · omega
    · exact hvis u hu'
  · simp only [mu, ↓reduceIte]
    rw [phiC_eq head n _ _ _ _ _ A', phiC_eq head n _ _ _ _ _ A0]
    omega

theorem ii_nf (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw sp : Int) (c t0 : Nat)
    (H : II head target n k state it stk fsp fw sp c t0) (hsp : 0 < sp) : fsp = 0 := by
  rcases H with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · omega

open Proofs.PrimMath (Rtc) in
/-- The meaning of the result: no directed cycle (`k = 0`), or a directed cycle of `k` distinct vertices in `cyc`. -/
def Out (head target : Array Int) (n : Nat) (k : Int) (cyc : Array Int) : Prop :=
  (k = 0 ∧ ∀ u w, AdjH (hdF head) (tgF target) u w → ¬ Rtc (AdjH (hdF head) (tgF target)) w u) ∨
  (0 < k ∧ CycOut n (hdF head) (tgF target) cyc.toList k.toNat)


theorem lt_of_toNat_lt (t : Nat) (x : Int) (h : t < x.toNat) : (t : Int) < x := by omega

theorem cost_found (fsp j : Int) (s s1 s2 t0 N hd P : Nat) (h1 : 0 < fsp) (h2 : 0 ≤ j) (h3 : j < fsp)
    (h4 : fsp.toNat ≤ N) (h5 : s2 ≤ t0 + 1 + 2 * N + P) (h6 : P ≤ hd + N) (h7 : s1 ≤ s2 + fsp.toNat + 1)
    (h8 : s = s1 + (fsp - j).toNat) : s ≤ t0 + 3 + 5 * N + hd := by omega

theorem copy_bound (fsp j : Int) (m s N : Nat) (h2 : 0 ≤ j) (h3 : fsp.toNat ≤ N)
    (h4 : (fsp - j).toNat = m + (s + 1)) : m < N := by omega

theorem copy_step (b stk : Array Int) (j : Int) (m N : Nat) (hsz : b.size = N) (hm : m < N)
    (hcp : ∀ t, t < m → b[t]! = stk[(j + t).toNat]!) :
    (set b (m : Int) (get stk (j + m))).size = N ∧
      ∀ t, t < m + 1 → (set b (m : Int) (get stk (j + m)))[t]! = stk[(j + t).toNat]! := by
  refine ⟨by simp [hsz], fun t ht => ?_⟩
  rw [get_set _ _ _ (by omega) (by rw [hsz]; omega)]
  unfold upd
  split
  · rename_i htt; simp only [Int.toNat_natCast] at htt; subst htt; simp [get]
  · rename_i htt; simp only [Int.toNat_natCast] at htt; exact hcp t (by omega)

theorem oi_fd (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw : Int) (c t0 : Nat)
    (H : OI head target n k state it stk fsp fw c t0) (h : 0 < fsp) :
    FoundC head target n stk fsp fw ∧ c ≤ t0 + 1 + 2 * k + P0 head n := by
  rcases H with ⟨h', -⟩ | H
  · omega
  · exact H

theorem oi_nf (head target : Array Int) (n k : Nat) (state it stk : Array Int) (fsp fw : Int) (c t0 : Nat)
    (H : OI head target n k state it stk fsp fw c t0) (h : fsp ≤ 0) :
    ∃ st, FInv n (hdF head) (tgF target) st ∧ st.sp = 0 ∧ (∀ v, v < k → st.C v ≠ 0) ∧
      c ≤ t0 + 1 + 2 * k + P0 head n := by
  rcases H with ⟨-, st, I, -, hsp, hv, hc⟩ | ⟨F, -⟩
  · exact ⟨st, I, hsp, hv, by omega⟩
  · have := F.1; omega

theorem p0_le (head target : Array Int) (n : Nat) (P : Pre head target n) : P0 head n ≤ hdF head n + n := by
  have := tele (hdF head) n (fun x hx => P.G.mono x hx); unfold P0; omega

theorem found_mem (head target : Array Int) (n : Nat) (stk : Array Int) (fsp fw : Int)
    (F : FoundC head target n stk fsp fw) : ∃ j0 : Nat, (j0 : Int) ≤ fsp - 1 ∧ stk[j0]! = fw := by
  obtain ⟨h1, h2, -, h4, F⟩ := F
  obtain ⟨j, hj, hjw⟩ := F.mem
  have := h4 j hj
  have hjw' : stk[j]!.toNat = fw.toNat := hjw
  exact ⟨j, by omega, by omega⟩

theorem out_found (head target : Array Int) (n : Nat) (stk : Array Int) (fsp fw : Int)
    (F : FoundC head target n stk fsp fw) (j : Int) (hj0 : 0 ≤ j) (hj : j < fsp) (hjw : stk[j.toNat]! = fw)
    (cyc : Array Int) (hcs : cyc.size = n) (hcyc : ∀ t, t < (fsp - j).toNat → cyc[t]! = stk[(j + t).toNat]!) :
    Out head target n (fsp - j) cyc := by
  obtain ⟨h1, h2, -, h4, F⟩ := F
  have hfn := F.fsp_le
  refine Or.inr ⟨by omega, ?_⟩
  have e : (fsp - j).toNat = fsp.toNat - j.toNat := by omega
  rw [e]
  refine cycout_of_found F (j := j.toNat) (by omega) (by show stk[j.toNat]!.toNat = fw.toNat; rw [hjw]) cyc.toList (fun t ht => ?_)
  have htc : t < cyc.size := by omega
  have hnn := h4 (j.toNat + t) (by omega)
  have e2 : (j + (t : Int)).toNat = j.toNat + t := by omega
  have hg : cyc.toList.getD t 0 = cyc[t]! := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]; simp [htc, getElem!_pos]
  rw [hg, hcyc t (by omega), e2]
  show _ = ((stk[j.toNat + t]!.toNat : Nat) : Int)
  omega

open Proofs.PrimMath (Rtc) in
theorem out_none (head target : Array Int) (n : Nat) (P : Pre head target n) (st : FS)
    (I : FInv n (hdF head) (tgF target) st) (hsp : st.sp = 0) (hall : ∀ v, v < n → st.C v ≠ 0) (cyc : Array Int) :
    Out head target n 0 cyc :=
  Or.inl ⟨rfl, acyclic_of_done P.G I hsp hall⟩

theorem find_cycle_spec (head target state it stk cyc : Array Int) (n : Int) (hn : 0 ≤ n)
    (P : Pre head target n.toNat) (hs : state.size = n.toNat ∧ it.size = n.toNat ∧ stk.size = n.toNat ∧
      cyc.size = n.toNat) (h0 : ∀ v, v < n.toNat → state[v]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.find_cycle head target state it stk cyc n
    ⦃⇓ r c => ⌜Out head target n.toNat r.1 r.2.2.2.2 ∧ c ≤ t0 + 3 + 5 * n.toNat + hdF head n.toNat⌝⦄ := by
  mvcgen [cp.find_cycle]
  case inv1 =>
    exact ⇓⟨xs, state, it, stk, fsp, fw⟩ c =>
      ⌜OI head target n.toNat xs.prefix.length state it stk fsp fw c t0⌝
  case vc1.inv =>
    rename_i pref _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨fun ⟨state, it, stk, fsp, fw, sp⟩ c =>
        ⌜II head target n.toNat pref.length state it stk fsp fw sp c t0⌝,
      fun ⟨state, it, stk, fsp, fw, _⟩ c => ⌜OI head target n.toNat (pref.length + 1) state it stk fsp fw c t0⌝,
      fun ⟨state, it, _, fsp, _, sp⟩ => mu head n.toNat state it fsp sp⟩
  case vc12.inv =>
    rename_i _ _ r _ _ _ _ _ _ _ _ _ _ _ c0 _
    exact ⟨fun j c => ⌜∃ j0 : Nat, (j0 : Int) ≤ j ∧ j < r.2.2.2.1 ∧ r.2.2.1[j0]! = r.2.2.2.2 ∧
        c + j.toNat ≤ c0 + r.2.2.2.1.toNat⌝,
      fun j c => ⌜0 ≤ j ∧ j < r.2.2.2.1 ∧ r.2.2.1[j.toNat]! = r.2.2.2.2 ∧ c ≤ c0 + r.2.2.2.1.toNat + 1⌝,
      fun j => j.toNat⟩
  case inv2 =>
    rename_i _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ j _ cE _
    exact ⇓⟨xs, cyc'⟩ c => ⌜cyc'.size = n.toNat ∧
      (∀ t, t < xs.prefix.length → cyc'[t]! = r.2.2.1[(j + t).toNat]!) ∧ c = cE + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    rename_i hsp
    have hII := ‹II _ _ _ _ _ _ _ _ _ _ _ _›
    exact ii_exit head target _ _ _ _ _ _ _ _ _ _ hII hsp
  case vc3.step.isFalse.isTrue.isTrue =>
    rename_i hsp hlt hu
    have hII := ‹II _ _ _ _ _ _ _ _ _ _ _ _›
    have hf := ii_nf head target _ _ _ _ _ _ _ _ _ _ hII hsp
    rw [hf] at hII ⊢
    exact ii_push head target _ _ P _ _ _ _ _ _ _ hII hsp _ _ _ rfl rfl rfl hlt hu
  case vc4.step.isFalse.isTrue.isFalse.isTrue =>
    rename_i hsp hlt hu0 hg
    have hII := ‹II _ _ _ _ _ _ _ _ _ _ _ _›
    have hf := ii_nf head target _ _ _ _ _ _ _ _ _ _ hII hsp
    rw [hf] at hII ⊢
    exact ii_found head target _ _ P _ _ _ _ _ _ _ hII hsp _ _ _ rfl rfl rfl hlt hg _
  case vc5.step.isFalse.isTrue.isFalse.isFalse =>
    rename_i hsp hlt hu0 hg
    have hII := ‹II _ _ _ _ _ _ _ _ _ _ _ _›
    have hf := ii_nf head target _ _ _ _ _ _ _ _ _ _ hII hsp
    rw [hf] at hII ⊢
    exact ii_skip head target _ _ P _ _ _ _ _ _ _ hII hsp _ _ _ rfl rfl rfl hlt hu0 hg
  case vc6.step.isFalse.isFalse =>
    rename_i hsp hge
    have hII := ‹II _ _ _ _ _ _ _ _ _ _ _ _›
    have hf := ii_nf head target _ _ _ _ _ _ _ _ _ _ hII hsp
    rw [hf] at hII ⊢
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ hII hsp _ rfl hge
  case vc7.step.isTrue.isTrue.pre =>
    rename_i hf hst
    have hr := ‹range 0 n = _ ++ _ :: _›
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp [range_length] at hl e
    subst e
    rw [hf] at hOI ⊢
    exact ii_root head target _ _ P _ _ _ _ _ _ hOI (by omega) hst
  case vc8.step.isTrue.isTrue.post.success => assumption
  case vc9.step.isTrue.isFalse =>
    rename_i hf hst
    have hr := ‹range 0 n = _ ++ _ :: _›
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp [range_length] at hl e
    subst e
    exact oi_skip head target _ _ _ _ _ _ _ _ _ hOI (by omega) (fun _ => hst)
  case vc10.step.isFalse =>
    rename_i hf
    have hr := ‹range 0 n = _ ++ _ :: _›
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp [range_length] at hl e
    subst e
    exact oi_skip head target _ _ _ _ _ _ _ _ _ hOI (by omega) (fun h => absurd h hf)
  case vc11.pre =>
    rename_i c hc
    subst hc
    exact oi_init head target _ _ _ _ _ ⟨hs.1, hs.2.1, hs.2.2.1⟩ (fun v hv => h0 v (by omega))
  case vc13.step.isTrue =>
    rename_i hfsp hjw
    obtain ⟨j0, h1, h2, h3, h4⟩ := ‹∃ j0 : Nat, _ ∧ _ ∧ _ ∧ _›
    exact ⟨by omega, h2, by simpa [get] using hjw, by omega⟩
  case vc14.step.isFalse =>
    rename_i hfsp hne
    obtain ⟨j0, h1, h2, h3, h4⟩ := ‹∃ j0 : Nat, _ ∧ _ ∧ _ ∧ _›
    rcases Int.lt_or_eq_of_le h1 with hlt | heq
    · exact ⟨⟨j0, by omega, by omega, h3, by omega⟩, by omega⟩
    · exfalso; apply hne; rw [← heq]; simpa [get] using h3
  case vc15.post.success.isTrue.pre =>
    rename_i hfsp
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    simp [range_length] at hOI
    obtain ⟨F, -⟩ := oi_fd head target _ _ _ _ _ _ _ _ _ hOI hfsp
    obtain ⟨j0, hj0, hjw⟩ := found_mem head target _ _ _ _ F
    have hfn := F.2.2.2.2.fsp_le
    refine ⟨⟨j0, hj0, hjw⟩, ?_⟩
    have hb := P.bound
    have h64 : n.toNat < fuel := by simp only [fuel]; omega
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) hfn) h64
  case vc16.step =>
    rename_i hfsp
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    simp [range_length] at hOI
    obtain ⟨F, -⟩ := oi_fd head target _ _ _ _ _ _ _ _ _ hOI hfsp
    have hfn := F.2.2.2.2.fsp_le
    obtain ⟨hj0, hj1, -, -⟩ := ‹0 ≤ (_ : Int) ∧ (_ : Int) < _ ∧ _ ∧ _›
    obtain ⟨hsz, hcp, hc⟩ := ‹Array.size _ = n.toNat ∧ _ ∧ _›
    have hr := ‹range 0 _ = _ ++ _ :: _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp +zetaDelta [range_length] at hl e
    subst e
    obtain ⟨-, c2⟩ := copy_step _ _ _ _ _ hsz (copy_bound _ _ _ _ _ hj0 hfn hl) hcp
    exact ⟨hsz, c2, by omega⟩
  case vc17.post.success.isTrue.post.success.pre => exact hs.2.2.2
  case vc18.post.success.isTrue.post.success.post.success =>
    rename_i hfsp
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    simp [range_length] at hOI
    obtain ⟨F, hc0⟩ := oi_fd head target _ _ _ _ _ _ _ _ _ hOI hfsp
    have hfn := F.2.2.2.2.fsp_le
    obtain ⟨hj0, hj1, hjw, hc1⟩ := ‹0 ≤ (_ : Int) ∧ (_ : Int) < _ ∧ _ ∧ _›
    obtain ⟨hsz, hcp, hc⟩ := ‹Array.size _ = n.toNat ∧ _ ∧ _›
    simp [range_length] at hcp hc
    have hP := p0_le head target _ P
    exact ⟨out_found head target _ _ _ _ F _ hj0 hj1 hjw _ hsz (fun t ht => hcp t (lt_of_toNat_lt _ _ ht)),
      cost_found _ _ _ _ _ _ _ _ _ hfsp hj0 hj1 hfn hc0 hP hc1 hc⟩
  case vc20.post.success.isFalse =>
    rename_i hfsp
    have hOI := ‹OI _ _ _ _ _ _ _ _ _ _ _›
    simp [range_length] at hOI
    obtain ⟨st, I, hsp, hall, hc⟩ := oi_nf head target _ _ _ _ _ _ _ _ _ hOI hfsp
    have hP := p0_le head target _ P
    exact ⟨out_none head target _ P st I hsp hall cyc, by omega⟩

end Proofs.Cpp.FindCycle
