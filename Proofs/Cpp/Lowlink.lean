import Proofs.Cpp.Gen.Lowlink
import Proofs.Cpp.Lib.Basic
import Proofs.LowlinkSpec
import Proofs.LowlinkPhiMath

/-! # `lowlink` (library/graph/lowlink.hpp)

The translated model refines the machine `St` of `Proofs.LowlinkInv` (invariant `MInv`; one step is `rootS`, `pushS`,
`scanS` or `popS`, and `Proofs.LowlinkSpec.lowlink_spec` gives the meaning of the final state). The arrays of the C++
state are the fields of `St` on `0 .. n-1` (`Abs`); the ghost fields `Fi`, `Vis` exist (`∃ st`). The potential `phi`
(unscanned arcs, unvisited vertices, the stack) bounds the iterations. -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.LowlinkInv Proofs.LowlinkGraph Proofs.LowlinkFinal Proofs.LowlinkPhiMath
open Proofs.LowlinkPush Proofs.LowlinkPop Proofs.LowlinkScan Proofs.LowlinkRoot

namespace Proofs.Cpp.Lowlink

/-- The CSR arrays as functions. -/
def hdF (head : Array Int) : Nat → Nat := fun v => head[v]!.toNat
def tgF (target : Array Int) : Nat → Nat := fun q => target[q]!.toNat

/-- The C++ arrays hold the fields of `st` on the vertices `0 .. n-1`. -/
def Abs (n : Nat) (ord low par sep it stk : Array Int) (cnt sp : Int) (st : St) : Prop :=
  ord.size = n ∧ low.size = n ∧ par.size = n ∧ sep.size = n ∧ it.size = n ∧ stk.size = n ∧
  (∀ v, v < n → ord[v]! = st.O v ∧ low[v]! = st.L v ∧ par[v]! = st.P v ∧ sep[v]! = st.Sp v ∧ it[v]! = st.It v) ∧
  (∀ i, i < st.sp → stk[i]! = (st.Sk i : Int)) ∧ sp = st.sp ∧ cnt = st.Vis.length

/-- The initial potential: all arcs and all vertices. -/
def P0 (head : Array Int) (n : Nat) : Nat := ((List.range n).map (fun a => hdF head (a + 1) - hdF head a)).sum + n

/-- The invariant of the outer loop after the roots `0 .. k-1`. -/
def OI (head target : Array Int) (n k : Nat) (ord low par sep it stk : Array Int) (cnt : Int) (c t0 : Nat) : Prop :=
  ∃ st, MInv n (hdF head) (tgF target) st ∧ Abs n ord low par sep it stk cnt 0 st ∧ st.sp = 0 ∧
    (∀ v, v < k → v ∈ st.Vis) ∧ c + phi n (hdF head) st ≤ t0 + 1 + 2 * k + P0 head n

/-- The invariant of the depth-first search from the root `k`. -/
def II (head target : Array Int) (n k : Nat) (ord low par sep it stk : Array Int) (cnt sp : Int) (c t0 : Nat) : Prop :=
  ∃ st, MInv n (hdF head) (tgF target) st ∧ Abs n ord low par sep it stk cnt sp st ∧
    (∀ v, v < k + 1 → v ∈ st.Vis) ∧ c + phi n (hdF head) st ≤ t0 + 1 + 2 * k + 1 + P0 head n

/-- `phi` computed from the C++ state. -/
def phiC (head : Array Int) (n : Nat) (ord it : Array Int) (cnt sp : Int) : Nat :=
  ((List.range n).map (fun a => hdF head (a + 1) - (if 0 ≤ ord[a]! then it[a]!.toNat else hdF head a))).sum +
    (n - cnt.toNat) + sp.toNat

/-- The preconditions on the CSR graph. -/
structure Pre (head target : Array Int) (n : Nat) : Prop where
  hsize : head.size = n + 1
  hnn : ∀ v, v ≤ n → 0 ≤ head[v]!
  G : GH n (hdF head) (tgF target)
  tnn : ∀ x q, x < n → hdF head x ≤ q → q < hdF head (x + 1) → 0 ≤ target[q]!
  bound : hdF head n + 3 * n < 2 ^ 62

theorem head_eq (head : Array Int) (v : Nat) (h : 0 ≤ head[v]!) : head[v]! = (hdF head v : Int) := by
  unfold hdF; omega

theorem get_set (A : Array Int) (i : Int) (x : Int) (hi0 : 0 ≤ i) (hi : i.toNat < A.size) (v : Nat) :
    (set A i x)[v]! = upd (fun u => A[u]!) i.toNat x v := by
  rw [getElemBang_set _ _ _ _ hi]; unfold upd; rfl

theorem vis_len_lt (n : Nat) (Vis : List Nat) (hnd : Vis.Nodup) (hlt : ∀ v ∈ Vis, v < n) (k : Nat) (hk : k < n)
    (hkV : k ∉ Vis) : Vis.length < n := by
  have h := List.Nodup.length_le_of_subset (l₁ := k :: Vis) (l₂ := List.range n) (List.nodup_cons.mpr ⟨hkV, hnd⟩)
    (fun x hx => by
      rcases List.mem_cons.mp hx with e | e
      · subst e; simpa using hk
      · simpa using hlt x e)
  simp at h; omega

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

theorem phi_le (head target : Array Int) (n : Nat) (P : Pre head target n) (st : St)
    (I : MInv n (hdF head) (tgF target) st) : phi n (hdF head) st ≤ hdF head n + 2 * n := by
  unfold phi unsc
  have h1 : ((List.range n).map (fun a => hdF head (a + 1) - itN (hdF head) st a)).sum ≤
      ((List.range n).map (fun a => hdF head (a + 1) - hdF head a)).sum := by
    apply sum_map_le
    intro a _
    unfold itN
    split
    · rename_i ha; have := (I.it_rng a ha).1; omega
    · omega
  have h2 := tele (hdF head) n (fun x hx => P.G.mono x hx)
  have h3 := I.sp_le
  have h4 := I.vis_len_le
  omega

theorem phiC_eq (head target : Array Int) (n : Nat) (st : St) (I : MInv n (hdF head) (tgF target) st)
    (ord low par sep it stk : Array Int) (cnt sp : Int) (A : Abs n ord low par sep it stk cnt sp st) :
    phiC head n ord it cnt sp = phi n (hdF head) st := by
  obtain ⟨-, -, -, -, -, -, hv, -, hsp, hcnt⟩ := A
  unfold phiC phi unsc
  have e : (List.range n).map (fun a => hdF head (a + 1) - (if 0 ≤ ord[a]! then it[a]!.toNat else hdF head a)) =
      (List.range n).map (fun a => hdF head (a + 1) - itN (hdF head) st a) := by
    apply List.map_congr_left
    intro a ha
    have ha' : a < n := List.mem_range.mp ha
    obtain ⟨e1, -, -, -, e5⟩ := hv a ha'
    unfold itN
    rw [e1, e5]
    by_cases hV : a ∈ st.Vis
    · rw [if_pos (I.ord_lt_len hV).1, if_pos hV]
    · rw [if_neg (by rw [I.unv_ord a hV]; omega), if_neg hV]
  rw [e, hsp, hcnt]
  simp

theorem oi_init (head target : Array Int) (n : Nat) (ord low par sep it stk : Array Int) (t0 : Nat)
    (hs : ord.size = n ∧ low.size = n ∧ par.size = n ∧ sep.size = n ∧ it.size = n ∧ stk.size = n)
    (hord : ∀ v, v < n → ord[v]! = -1) (hpar : ∀ v, v < n → par[v]! = -1) (hsep : ∀ v, v < n → sep[v]! = 0) :
    OI head target n 0 ord low par sep it stk 0 (t0 + 1) t0 := by
  refine ⟨initS (fun v => low[v]!) (fun v => it[v]!) (fun _ => 0), inv_init _ _ _ _ _ _, ?_, rfl,
    fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    exact ⟨h1, h2, h3, h4, h5, h6, fun v hv => ⟨hord v hv, rfl, hpar v hv, hsep v hv, rfl⟩,
      fun i hi => absurd hi (by simp [initS]), by simp [initS], by simp [initS]⟩
  · have : phi n (hdF head) (initS (fun v => low[v]!) (fun v => it[v]!) (fun _ => 0)) = P0 head n := by
      simp [phi, unsc, itN, initS, P0]
    omega

theorem oi_skip (head target : Array Int) (n k : Nat) (ord low par sep it stk : Array Int) (cnt : Int) (c t0 : Nat)
    (H : OI head target n k ord low par sep it stk cnt c t0) (hk : k < n) (h : 0 ≤ get ord (k : Int)) :
    OI head target n (k + 1) ord low par sep it stk cnt (c + 1) t0 := by
  obtain ⟨st, I, A, hsp, hvis, hc⟩ := H
  have hO : 0 ≤ st.O k := by have := (A.2.2.2.2.2.2.1 k hk).1; simp [get] at h; omega
  refine ⟨st, I, A, hsp, fun v hv => ?_, by omega⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h' | h'
  · exact hvis v h'
  · subst h'; exact I.vis_of_nn hO

theorem ii_exit (head target : Array Int) (n k : Nat) (ord low par sep it stk : Array Int) (cnt sp : Int) (c t0 : Nat)
    (H : II head target n k ord low par sep it stk cnt sp c t0) (h : sp ≤ 0) :
    OI head target n (k + 1) ord low par sep it stk cnt (c + 1) t0 := by
  obtain ⟨st, I, A, hvis, hc⟩ := H
  have hsp : st.sp = 0 := by have := A.2.2.2.2.2.2.2.2.1; omega
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A
  exact ⟨st, I, ⟨a1, a2, a3, a4, a5, a6, a7, a8, by rw [hsp]; rfl, a10⟩, hsp, hvis, by omega⟩

theorem ii_root (head target : Array Int) (n k : Nat) (P : Pre head target n) (ord low par sep it stk : Array Int)
    (cnt : Int) (c t0 : Nat) (H : OI head target n k ord low par sep it stk cnt c t0) (hk : k < n)
    (h : get ord (k : Int) < 0) :
    II head target n k (set ord k cnt) (set low k cnt) par sep (set it k (get head k)) (set stk 0 k) (cnt + 1) 1
      (c + 1) t0 ∧
    phiC head n (set ord k cnt) (set it k (get head k)) (cnt + 1) 1 < fuel := by
  obtain ⟨st, I, A, hsp, hvis, hc⟩ := H
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A
  have hO : st.O k < 0 := by have := (a7 k hk).1; simp [get] at h; omega
  have hkV : k ∉ st.Vis := fun hv => by have := (I.ord_lt_len hv).1; omega
  have I' := inv_root P.G I hsp hk hO
  have hlen := vis_len_lt n st.Vis I.vis_nd I.vis_lt k hk hkV
  have hph := phi_root n (hdF head) st k hkV hlen hsp
  have hhk : get head (k : Int) = (hdF head k : Int) := by simp [get]; exact head_eq head k (P.hnn k (by omega))
  have A' : Abs n (set ord k cnt) (set low k cnt) par sep (set it k (get head k)) (set stk 0 k) (cnt + 1) 1
      (rootS (hdF head) st k) := by
    refine ⟨by simp [a1], by simp [a2], a3, a4, by simp [a5], by simp [a6], fun v hv => ?_, fun i hi => ?_,
      by simp [rootS], by simp [rootS, a10]⟩
    · obtain ⟨b1, b2, b3, b4, b5⟩ := a7 v hv
      refine ⟨?_, ?_, b3, b4, ?_⟩
      · rw [get_set _ _ _ (by omega) (by simp; omega)]; simp only [Int.toNat_natCast, rootS]
        unfold upd; split
        · exact a10
        · exact b1
      · rw [get_set _ _ _ (by omega) (by simp; omega)]; simp only [Int.toNat_natCast, rootS]
        unfold upd; split
        · exact a10
        · exact b2
      · rw [get_set _ _ _ (by omega) (by simp; omega), hhk]; simp only [Int.toNat_natCast, rootS]
        unfold upd; split
        · rfl
        · exact b5
    · simp [rootS] at hi; subst hi
      rw [get_set _ _ _ (by omega) (by simp; omega)]; simp [rootS, upd]
  have hp := phi_le head target n P _ I'
  refine ⟨⟨_, I', A', fun v hv => ?_, by omega⟩, ?_⟩
  · simp only [rootS, List.mem_append, List.mem_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h' | h'
    · exact Or.inl (hvis v h')
    · exact Or.inr h'
  · rw [phiC_eq head target n _ I' _ _ _ _ _ _ _ _ A']
    have := P.bound; simp only [fuel]; omega

/-- The facts about the top of the stack and the arc at its cursor. -/
theorem top_facts (head target : Array Int) (n : Nat) (P : Pre head target n) (st : St)
    (I : MInv n (hdF head) (tgF target) st) (ord low par sep it stk : Array Int) (cnt sp : Int)
    (A : Abs n ord low par sep it stk cnt sp st) (hsp : 0 < sp) :
    0 < st.sp ∧ get stk (sp - 1) = (st.Sk (st.sp - 1) : Int) ∧ st.Sk (st.sp - 1) ∈ st.Vis ∧
      st.Fi (st.Sk (st.sp - 1)) < 0 ∧ st.Sk (st.sp - 1) < n := by
  obtain ⟨-, -, -, -, -, -, -, a8, a9, -⟩ := A
  have h0 : 0 < st.sp := by omega
  have hm := I.sk_mem (st.sp - 1) (by omega)
  refine ⟨h0, ?_, hm.1, hm.2, I.vis_lt _ hm.1⟩
  have e : (sp - 1).toNat = st.sp - 1 := by omega
  simp only [get, e]; exact a8 _ (by omega)

theorem arc_facts (head target : Array Int) (n : Nat) (P : Pre head target n) (st : St)
    (I : MInv n (hdF head) (tgF target) st) (v : Nat) (hvV : v ∈ st.Vis) (hvn : v < n) (itv : Int)
    (hitv : itv = st.It v) (hlt : itv < get head ((v : Int) + 1)) :
    (hdF head v : Int) ≤ st.It v ∧ st.It v < (hdF head (v + 1) : Int) ∧ 0 ≤ itv ∧
      get target itv = (tgF target itv.toNat : Int) ∧ AdjH (hdF head) (tgF target) v (tgF target itv.toNat) ∧
      tgF target itv.toNat < n := by
  have hr := I.it_rng v hvV
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

theorem ii_push (head target : Array Int) (n k : Nat) (P : Pre head target n) (ord low par sep it stk : Array Int)
    (cnt sp : Int) (c t0 : Nat) (H : II head target n k ord low par sep it stk cnt sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) (hu : get ord w < 0) :
    II head target n k (set ord w cnt) (set low w cnt) (set par w v) sep (set (set it v (e + 1)) w (get head w))
      (set stk sp w) (cnt + 1) (sp + 1) (c + 1) t0 ∧
    phiC head n (set ord w cnt) (set (set it v (e + 1)) w (get head w)) (cnt + 1) (sp + 1) <
      phiC head n ord it cnt sp := by
  obtain ⟨st, I, A, hvis, hc⟩ := H
  obtain ⟨h0, hstk, hvV, hfv, hvn⟩ := top_facts head target n P st I _ _ _ _ _ _ _ _ A hsp
  have A0 := A
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A
  generalize hvN : st.Sk (st.sp - 1) = vN at hstk hvV hfv hvn
  rw [hstk] at hv
  subst hv
  obtain ⟨b1, b2, b3, b4, b5⟩ := a7 _ hvn
  have hitv : get it (vN : Int) = st.It vN := by simpa [get] using b5
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := arc_facts head target n P st I _ hvV hvn _ hitv hlt
  rw [← he] at f3 f4 f5 f6 hitv
  rw [f4] at hw
  subst hw
  generalize hwN : tgF target e.toNat = wN at f5 f6 hu
  have hOw : st.O wN < 0 := by have := (a7 wN f6).1; simp [get] at hu; omega
  have hwV : wN ∉ st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
  have hqe : ((e.toNat : Nat) : Int) = st.It vN := by omega
  have I' := inv_push P.G I h0 hvN hqe (by omega) hwN hOw
  have hlen := vis_len_lt n st.Vis I.vis_nd I.vis_lt wN f6 hwV
  have hph := phi_push n (hdF head) st vN wN hvn hvV hwV hlen f1 f2
  have hvw : vN ≠ wN := fun h => hwV (h ▸ hvV)
  have hhw : get head (wN : Int) = (hdF head wN : Int) := by
    simp only [get, Int.toNat_natCast]; exact head_eq head wN (P.hnn wN (by omega))
  have hspn : sp.toNat < n := by have := I.sp_le; omega
  have A' : Abs n (set ord wN cnt) (set low wN cnt) (set par wN vN) sep
      (set (set it vN (e + 1)) wN (get head wN)) (set stk sp wN) (cnt + 1) (sp + 1)
      (pushS (hdF head) st vN wN) := by
    refine ⟨by simp [a1], by simp [a2], by simp [a3], a4, by simp [a5], by simp [a6], fun u hu => ?_, fun i hi => ?_,
      by simp [pushS, a9], by simp [pushS, a10]⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := a7 u hu
      refine ⟨?_, ?_, ?_, c4, ?_⟩
      · rw [get_set ord wN cnt (by omega) (by simp [a1]; omega)]; simp only [Int.toNat_natCast, pushS]
        unfold upd; split
        · exact a10
        · exact c1
      · rw [get_set low wN cnt (by omega) (by simp [a2]; omega)]; simp only [Int.toNat_natCast, pushS]
        unfold upd; split
        · exact a10
        · exact c2
      · rw [get_set par wN vN (by omega) (by simp [a3]; omega)]; simp only [Int.toNat_natCast, pushS]
        unfold upd; split
        · rfl
        · exact c3
      · rw [get_set _ wN _ (by omega) (by simp [a5]; omega), hhw]
        simp only [Int.toNat_natCast, pushS]
        unfold upd; split
        · rfl
        · beta_reduce
          rw [get_set it vN (e + 1) (by omega) (by simp [a5]; omega)]; simp only [Int.toNat_natCast]
          unfold upd; split
          · rename_i hh; subst hh; rw [hitv]
          · exact c5
    · simp only [pushS] at hi
      rw [get_set stk sp wN (by omega) (by simp [a6]; omega)]
      simp only [pushS]; unfold upd
      have e9 : sp.toNat = st.sp := by omega
      rw [e9]
      split
      · rfl
      · exact a8 i (by omega)
  have hp := phi_le head target n P _ I'
  refine ⟨⟨_, I', A', fun u hu => by simp only [pushS, List.mem_append]; exact Or.inl (hvis u hu), by omega⟩, ?_⟩
  rw [phiC_eq head target n _ I' _ _ _ _ _ _ _ _ A', phiC_eq head target n _ I _ _ _ _ _ _ _ _ A0]
  omega

theorem ii_scan (head target : Array Int) (n k : Nat) (P : Pre head target n) (ord low par sep it stk : Array Int)
    (cnt sp : Int) (c t0 : Nat) (H : II head target n k ord low par sep it stk cnt sp c t0) (hsp : 0 < sp)
    (v e w : Int) (hv : v = get stk (sp - 1)) (he : e = get it v) (hw : w = get target e)
    (hlt : get it v < get head (v + 1)) (hu : 0 ≤ get ord w) (low' : Array Int)
    (hlow : low' = if w ≠ get par v ∧ get ord w < get low v then set low v (get ord w) else low) :
    II head target n k ord low' par sep (set it v (e + 1)) stk cnt sp (c + 1) t0 ∧
    phiC head n ord (set it v (e + 1)) cnt sp < phiC head n ord it cnt sp := by
  obtain ⟨st, I, A, hvis, hc⟩ := H
  obtain ⟨h0, hstk, hvV, hfv, hvn⟩ := top_facts head target n P st I _ _ _ _ _ _ _ _ A hsp
  have A0 := A
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A
  generalize hvN : st.Sk (st.sp - 1) = vN at hstk hvV hfv hvn
  rw [hstk] at hv
  subst hv
  obtain ⟨b1, b2, b3, b4, b5⟩ := a7 _ hvn
  have hitv : get it (vN : Int) = st.It vN := by simpa [get] using b5
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := arc_facts head target n P st I _ hvV hvn _ hitv hlt
  rw [← he] at f3 f4 f5 f6 hitv
  rw [f4] at hw
  subst hw
  generalize hwN : tgF target e.toNat = wN at f5 f6 hu hlow
  have hOw : 0 ≤ st.O wN := by have := (a7 wN f6).1; simp [get] at hu; omega
  have gO : get ord (wN : Int) = st.O wN := by simpa [get] using (a7 wN f6).1
  have gP : get par (vN : Int) = st.P vN := by simpa [get] using b3
  have gL : get low (vN : Int) = st.L vN := by simpa [get] using b2
  rw [gO, gP, gL] at hlow
  have hqe : ((e.toNat : Nat) : Int) = st.It vN := by omega
  have hll := I.low_le vN hvV
  let Lnew : Nat → Int := if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L
  have I' := inv_scan I Lnew hvV hfv hqe (by omega) hwN hOw
    (fun u => by
      show (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) u ≤ st.L u
      split
      · unfold upd; split
        · rename_i hc' hh; subst hh; omega
        · exact Int.le_refl _
      · exact Int.le_refl _)
    (fun u hu' => by
      show (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) u = st.L u
      split
      · exact upd_ne _ _ _ _ hu'
      · rfl)
    (by
      show 0 ≤ (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) vN
      split
      · rw [upd_same]; exact hOw
      · exact hll.1)
    (by
      show (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) vN = st.L vN ∨
        (st.P vN ≠ (wN : Int) ∧ (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) vN
          = st.O wN)
      split
      · rename_i hc'; rw [upd_same]; exact Or.inr ⟨fun h => hc'.1 h.symm, rfl⟩
      · exact Or.inl rfl)
    (fun hne => by
      show (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) vN ≤ st.O wN
      split
      · rw [upd_same]
      · rename_i hc'
        have : ¬ st.O wN < st.L vN := fun h => hc' ⟨fun h' => hne h'.symm, h⟩
        omega)
  have hph := phi_scan n (hdF head) st vN Lnew hvn hvV f1 f2
  have A' : Abs n ord low' par sep (set it vN (e + 1)) stk cnt sp (scanS st vN Lnew) := by
    refine ⟨a1, ?_, a3, a4, by simp [a5], a6, fun u hu' => ?_, a8, a9, a10⟩
    · rw [hlow]; split <;> simp [a2]
    · obtain ⟨c1, c2, c3, c4, c5⟩ := a7 u hu'
      refine ⟨c1, ?_, c3, c4, ?_⟩
      · rw [hlow]
        show _ = (if (wN : Int) ≠ st.P vN ∧ st.O wN < st.L vN then upd st.L vN (st.O wN) else st.L) u
        split
        · rw [get_set low vN _ (by omega) (by simp [a2]; omega)]; simp only [Int.toNat_natCast]
          unfold upd; split
          · rfl
          · exact c2
        · exact c2
      · rw [get_set it vN (e + 1) (by omega) (by simp [a5]; omega)]; simp only [Int.toNat_natCast, scanS]
        unfold upd; split
        · rename_i hh; subst hh; rw [hitv]
        · exact c5
  refine ⟨⟨_, I', A', fun u hu' => hvis u hu', by omega⟩, ?_⟩
  rw [phiC_eq head target n _ I' _ _ _ _ _ _ _ _ A', phiC_eq head target n _ I _ _ _ _ _ _ _ _ A0]
  omega

theorem ii_pop (head target : Array Int) (n k : Nat) (P : Pre head target n) (ord low par sep it stk : Array Int)
    (cnt sp : Int) (c t0 : Nat) (H : II head target n k ord low par sep it stk cnt sp c t0) (hsp : 0 < sp)
    (v : Int) (hv : v = get stk (sp - 1)) (hge : get head (v + 1) ≤ get it v) (low' sep' : Array Int)
    (hpop : (sp - 1 ≤ 0 ∧ low' = low ∧ sep' = sep) ∨
      (0 < sp - 1 ∧ ∃ p, p = get stk (sp - 1 - 1) ∧
        low' = (if get low v < get low p then set low p (get low v) else low) ∧
        sep' = (if get ord p ≤ get low' v then set sep p (get sep p + 1) else sep))) :
    II head target n k ord low' par sep' it stk cnt (sp - 1) (c + 1) t0 ∧
    phiC head n ord it cnt (sp - 1) < phiC head n ord it cnt sp := by
  obtain ⟨st, I, A, hvis, hc⟩ := H
  obtain ⟨h0, hstk, hvV, hfv, hvn⟩ := top_facts head target n P st I _ _ _ _ _ _ _ _ A hsp
  have A0 := A
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A
  generalize hvN : st.Sk (st.sp - 1) = vN at hstk hvV hfv hvn
  rw [hstk] at hv
  subst hv
  obtain ⟨b1, b2, b3, b4, b5⟩ := a7 _ hvn
  have hr := I.it_rng vN hvV
  have hh : get head ((vN : Int) + 1) = (hdF head (vN + 1) : Int) := by
    have e : ((vN : Int) + 1).toNat = vN + 1 := by omega
    simp only [get, e]; exact head_eq head (vN + 1) (P.hnn (vN + 1) (by omega))
  have gI : get it (vN : Int) = st.It vN := by simpa [get] using b5
  rw [hh, gI] at hge
  have hit : st.It vN = (hdF head (vN + 1) : Int) := by omega
  have I' := inv_pop I h0 hvN hit
  have hph := phi_pop n (hdF head) st vN h0
  have gL : get low (vN : Int) = st.L vN := by simpa [get] using b2
  -- the parent of `vN` as seen by `popS`
  have key : ∀ u, u < n → low'[u]! = (popS st vN).L u ∧ sep'[u]! = (popS st vN).Sp u := by
    intro u hu
    obtain ⟨c1, c2, c3, c4, c5⟩ := a7 u hu
    rcases hpop with ⟨hs1, hl, hs⟩ | ⟨hs1, p, hp, hl, hs⟩
    · have hsp1 : st.sp = 1 := by omega
      have hroot := I.sk_root h0
      have e0 : st.Sk 0 = vN := by rw [← hvN, hsp1]
      rw [e0] at hroot
      have hne : st.P vN ≠ (u : Int) := by omega
      subst hl; subst hs
      simp only [popS, if_neg hne]
      exact ⟨c2, c4⟩
    · have hpar := I.sk_par (st.sp - 2) (by omega)
      have e1 : st.sp - 2 + 1 = st.sp - 1 := by omega
      rw [e1, hvN] at hpar
      have hstk2 : get stk (sp - 1 - 1) = (st.Sk (st.sp - 2) : Int) := by
        have e : (sp - 1 - 1).toNat = st.sp - 2 := by omega
        simp only [get, e]; exact a8 _ (by omega)
      rw [hstk2] at hp
      subst hp
      generalize hpN : st.Sk (st.sp - 2) = pN at hpar hl hs
      have hpV := (I.par_ok _ _ hpar).1
      have hpn := I.vis_lt _ hpV
      have hOpv := (I.par_ok _ _ hpar).2.2
      have hvp : vN ≠ pN := fun h => by subst h; omega
      obtain ⟨d1, d2, d3, d4, d5⟩ := a7 pN hpn
      have gLp : get low (pN : Int) = st.L pN := by simpa [get] using d2
      have gOp : get ord (pN : Int) = st.O pN := by simpa [get] using d1
      have gSp : get sep (pN : Int) = st.Sp pN := by simpa [get] using d4
      have gLv' : get low' (vN : Int) = st.L vN := by
        rw [hl]; split
        · simp only [get, Int.toNat_natCast]
          rw [get_set low pN _ (by omega) (by simp [a2]; omega)]; simp only [Int.toNat_natCast]
          unfold upd; rw [if_neg hvp]; exact b2
        · exact gL
      rw [gL, gLp] at hl
      rw [gOp, gLv', gSp] at hs
      have hPu : st.P vN = (u : Int) ↔ u = pN := by
        constructor
        · intro h; rw [hpar] at h; omega
        · intro h; subst h; exact hpar
      simp only [popS]
      by_cases hup : u = pN
      · subst hup
        rw [if_pos hpar, if_pos hpar]
        constructor
        · rw [hl]; split
          · rw [get_set low u _ (by omega) (by simp [a2]; omega)]; simp only [Int.toNat_natCast, upd_same]
            rw [min_def]; split <;> omega
          · rw [min_def]; split <;> omega
        · rw [hs]; split
          · rw [get_set sep u _ (by omega) (by simp [a4]; omega)]; simp only [Int.toNat_natCast, upd_same]
          · omega
      · rw [if_neg (fun h => hup (hPu.mp h)), if_neg (fun h => hup (hPu.mp h))]
        constructor
        · rw [hl]; split
          · rw [get_set low pN _ (by omega) (by simp [a2]; omega)]; simp only [Int.toNat_natCast]
            unfold upd; rw [if_neg hup]; exact c2
          · exact c2
        · rw [hs]; split
          · rw [get_set sep pN _ (by omega) (by simp [a4]; omega)]; simp only [Int.toNat_natCast]
            unfold upd; rw [if_neg hup]; exact c4
          · exact c4
  have hsz : low'.size = n ∧ sep'.size = n := by
    rcases hpop with ⟨-, hl, hs⟩ | ⟨-, p, -, hl, hs⟩
    · subst hl; subst hs; exact ⟨a2, a4⟩
    · constructor
      · rw [hl]; split <;> simp [a2]
      · rw [hs]; split <;> simp [a4]
  have A' : Abs n ord low' par sep' it stk cnt (sp - 1) (popS st vN) := by
    refine ⟨a1, hsz.1, a3, hsz.2, a5, a6, fun u hu => ?_, fun i hi => ?_, by simp [popS]; omega, by simp [popS, a10]⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := a7 u hu
      exact ⟨c1, (key u hu).1, c3, (key u hu).2, c5⟩
    · simp only [popS] at hi ⊢; exact a8 i (by omega)
  refine ⟨⟨_, I', A', fun u hu => by simp only [popS]; exact hvis u hu, by omega⟩, ?_⟩
  rw [phiC_eq head target n _ I' _ _ _ _ _ _ _ _ A', phiC_eq head target n _ I _ _ _ _ _ _ _ _ A0]
  omega

open Proofs.PrimMath (Rtc) in
/-- The meaning of the arrays after the search (`Proofs.LowlinkSpec.lowlink_spec`) and the work bound. -/
def Post (head target : Array Int) (n : Nat) (ord low par sep : Array Int) : Prop :=
  (∀ v, v < n → 0 ≤ ord[v]! ∧ ord[v]! < n) ∧
  (∀ u v, u < n → v < n → ord[u]! = ord[v]! → u = v) ∧
  (∀ v, v < n → par[v]! = -1 ∨
    ∃ p : Nat, p < n ∧ par[v]! = (p : Int) ∧ AdjH (hdF head) (tgF target) p v ∧ ord[p]! < ord[v]!) ∧
  (∀ v p : Nat, v < n → par[v]! = (p : Int) →
    (low[v]! = ord[v]! ↔ ¬ Rtc (LlFinal.EB (AdjH (hdF head) (tgF target)) p v) p v)) ∧
  (∀ v, v < n → (((par[v]! < 0 ∧ 2 ≤ sep[v]!) ∨ (0 ≤ par[v]! ∧ 1 ≤ sep[v]!)) ↔
    ∃ a b, AdjH (hdF head) (tgF target) v a ∧ AdjH (hdF head) (tgF target) v b ∧
      ¬ Rtc (LlFinal.EV (AdjH (hdF head) (tgF target)) v) a b))

theorem oi_final (head target : Array Int) (n : Nat) (P : Pre head target n) (ord low par sep it stk : Array Int)
    (cnt : Int) (c t0 : Nat) (H : OI head target n n ord low par sep it stk cnt c t0) :
    Post head target n ord low par sep ∧ c ≤ t0 + 1 + 3 * n + hdF head n := by
  obtain ⟨st, I, A, hsp, hvis, hc⟩ := H
  obtain ⟨-, -, -, -, -, -, a7, -, -, -⟩ := A
  obtain ⟨s1, s2, s3, s4, s5⟩ := Proofs.LowlinkSpec.lowlink_spec P.G I hsp hvis
  have hP0 : P0 head n ≤ hdF head n + n := by
    have := tele (hdF head) n (fun x hx => P.G.mono x hx); unfold P0; omega
  refine ⟨⟨fun v hv => ?_, fun u v hu hv h => ?_, fun v hv => ?_, fun v p hv h => ?_, fun v hv => ?_⟩, by omega⟩
  · rw [(a7 v hv).1]; exact s1 v hv
  · rw [(a7 u hu).1, (a7 v hv).1] at h; exact s2 u v hu hv h
  · rw [(a7 v hv).2.2.1]
    rcases s3 v hv with e | ⟨p, hp, e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr ⟨p, hp, e1, e2, by rw [(a7 p hp).1, (a7 v hv).1]; exact e3⟩
  · rw [(a7 v hv).2.2.1] at h
    rw [(a7 v hv).2.1, (a7 v hv).1]; exact s4 v p hv h
  · rw [(a7 v hv).2.2.1, (a7 v hv).2.2.2.1]; exact s5 v hv

/-- `lowlink` on a simple symmetric CSR graph with `n` vertices: the arrays satisfy `Post` (DFS order, parents,
bridges `low[v] = ord[v]`, articulation points by `sep`), in `O(n + m)` ticks. -/
theorem lowlink_spec (head target ord low par sep it stk : Array Int) (n : Int) (hn : 0 ≤ n)
    (P : Pre head target n.toNat)
    (hs : ord.size = n.toNat ∧ low.size = n.toNat ∧ par.size = n.toNat ∧ sep.size = n.toNat ∧ it.size = n.toNat ∧
      stk.size = n.toNat)
    (hord : ∀ v, v < n.toNat → ord[v]! = -1) (hpar : ∀ v, v < n.toNat → par[v]! = -1)
    (hsep : ∀ v, v < n.toNat → sep[v]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.lowlink head target ord low par sep it stk n
    ⦃⇓ r c => ⌜Post head target n.toNat r.1 r.2.1 r.2.2.1 r.2.2.2.1 ∧
      c ≤ t0 + 1 + 3 * n.toNat + hdF head n.toNat⌝⦄ := by
  mvcgen [cp.lowlink]
  case inv1 =>
    exact ⇓⟨xs, ord, low, par, sep, it, stk, cnt⟩ c =>
      ⌜OI head target n.toNat xs.prefix.length ord low par sep it stk cnt c t0⌝
  case vc1.inv =>
    rename_i pref _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨fun ⟨ord, low, par, sep, it, stk, cnt, sp⟩ c =>
        ⌜II head target n.toNat pref.length ord low par sep it stk cnt sp c t0⌝,
      fun ⟨ord, low, par, sep, it, stk, cnt, _⟩ c => ⌜OI head target n.toNat (pref.length + 1) ord low par sep it stk cnt c t0⌝,
      fun ⟨ord, _, _, _, it, _, cnt, sp⟩ => phiC head n.toNat ord it cnt sp⟩
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    rename_i h
    exact ii_exit head target _ _ _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› h
  case vc3.step.isFalse.isTrue.isTrue =>
    rename_i hsp hlt hu
    exact ii_push head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ _ _ rfl rfl rfl hlt hu
  case vc4.step.isFalse.isTrue.isFalse.isTrue.isTrue =>
    rename_i hsp hlt hu hne hlo
    exact ii_scan head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ _ _ rfl rfl rfl hlt hu _
      (by rw [if_pos ⟨hne, hlo⟩])
  case vc5.step.isFalse.isTrue.isFalse.isTrue.isFalse =>
    rename_i hsp hlt hu hne hlo
    exact ii_scan head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ _ _ rfl rfl rfl hlt hu _
      (by rw [if_neg (fun h => absurd h.2 (Int.not_lt.mpr hlo))])
  case vc6.step.isFalse.isTrue.isFalse.isFalse =>
    rename_i hsp hlt hu heq
    exact ii_scan head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ _ _ rfl rfl rfl hlt hu _
      (by rw [if_neg (fun h => h.1 heq)])
  case vc7.step.isFalse.isFalse.isTrue.isTrue.isTrue =>
    rename_i hsp hge hsp1 hA hB
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ rfl hge _ _
      (Or.inr ⟨by omega, _, rfl, by rw [if_pos hA], by rw [if_pos hB]⟩)
  case vc8.step.isFalse.isFalse.isTrue.isTrue.isFalse =>
    rename_i hsp hge hsp1 hA hB
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ rfl hge _ _
      (Or.inr ⟨by omega, _, rfl, by rw [if_pos hA], by rw [if_neg (Int.not_le.mpr hB)]⟩)
  case vc9.step.isFalse.isFalse.isTrue.isFalse.isTrue =>
    rename_i hsp hge hsp1 hA hB
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ rfl hge _ _
      (Or.inr ⟨by omega, _, rfl, by rw [if_neg (Int.not_lt.mpr hA)], by rw [if_pos hB]⟩)
  case vc10.step.isFalse.isFalse.isTrue.isFalse.isFalse =>
    rename_i hsp hge hsp1 hA hB
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ rfl hge _ _
      (Or.inr ⟨by omega, _, rfl, by rw [if_neg (Int.not_lt.mpr hA)], by rw [if_neg (Int.not_le.mpr hB)]⟩)
  case vc11.step.isFalse.isFalse.isFalse =>
    rename_i hsp hge hsp1
    exact ii_pop head target _ _ P _ _ _ _ _ _ _ _ _ _ ‹II _ _ _ _ _ _ _ _ _ _ _ _ _ _› hsp _ rfl hge _ _
      (Or.inl ⟨by omega, rfl, rfl⟩)
  case vc12.step.isTrue.pre =>
    rename_i h
    have hr := ‹range 0 n = _ ++ _ :: _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp [range_length] at hl e
    subst e
    exact ii_root head target _ _ P _ _ _ _ _ _ _ _ _ ‹OI _ _ _ _ _ _ _ _ _ _ _ _ _› (by omega) h
  case vc13.step.isTrue.post.success => exact ‹OI _ _ _ _ _ _ _ _ _ _ _ _ _›
  case vc14.step.isFalse =>
    rename_i h
    have hr := ‹range 0 n = _ ++ _ :: _›
    have e := range_cursor hr
    have hl := congrArg List.length hr
    simp [range_length] at hl e
    subst e
    exact oi_skip head target _ _ _ _ _ _ _ _ _ _ _ ‹OI _ _ _ _ _ _ _ _ _ _ _ _ _› (by omega) h
  case vc15.pre =>
    rename_i h
    subst h
    exact oi_init head target _ _ _ _ _ _ _ _ hs (fun v hv => hord v (by omega)) (fun v hv => hpar v (by omega))
      (fun v hv => hsep v (by omega))
  case vc16.post.success =>
    have H := ‹OI _ _ _ _ _ _ _ _ _ _ _ _ _›
    rw [range_length] at H
    simp only [Int.sub_zero] at H
    exact oi_final head target _ P _ _ _ _ _ _ _ _ _ H

end Proofs.Cpp.Lowlink
