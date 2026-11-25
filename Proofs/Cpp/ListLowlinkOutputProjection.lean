import Proofs.Cpp.ListLowlinkVisitProjection
import Proofs.Cpp.ListLowlinkResults

namespace Proofs.Cpp.ListLowlink

open Proofs.LowlinkInv Proofs.LowlinkPop Proofs.LowlinkFinal Proofs.LowlinkGraph
open Proofs.LowlinkMultigraph
open Proofs.PrimMath (Rtc)

theorem earlier_neighbor_ancestor {n : Nat} {hd tg : Nat → Nat} {st : St}
    (G : GH n hd tg) (I : MInv n hd tg st) {x w : Nat} (hx : x ∈ st.Vis)
    (hw : w ∈ st.Vis) (ha : AdjH hd tg x w) (hlt : st.O w < st.O x) :
    DescM st.P w x := by
  refine (I.interval w hw x hx).mpr ⟨by omega, ?_⟩
  by_cases hf : 0 ≤ st.Fi w
  · simpa [finE, hf] using (I.nbr_fin w hw hf x (G.sym x w ha)).2
  · simpa [finE, hf] using (I.ord_lt_len hx).2

/-- A root's children all count towards its separating-child counter, including while the
root's own frame is still active. -/
theorem root_child_separates {n : Nat} {hd tg : Nat → Nat} {st : St}
    (G : GH n hd tg) (I : MInv n hd tg st) {p v : Nat}
    (hroot : st.P p = -1) (hp : Pr st.P p v) : st.O p ≤ st.L v := by
  have hv := I.par_vis hp
  have hpVis := (I.par_ok p v hp).1
  have hpOrd := (I.par_ok p v hp).2.2
  by_contra hlt
  rcases I.low_mem v hv with he | ⟨x, w, hdesc, hAdj, _, hw⟩
  · omega
  have hx := I.desc_vis hv hdesc
  have hvx := I.desc_ord hv hdesc
  have hw0 := (I.low_le v hv).1
  have hwVis := I.vis_of_nn (v := w) (by omega)
  have hwx := earlier_neighbor_ancestor G I hx hwVis hAdj (by omega)
  have hpx := Rtc.head hp hdesc
  have hwp : DescM st.P w p := by
    rcases desc_comparable (desc_iff_m.mpr hwx) (desc_iff_m.mpr hpx) with he | he
    · exact desc_iff_m.mp he
    · have := I.desc_ord hpVis (desc_iff_m.mp he)
      omega
  rcases desc_last_aux hwp with he | ⟨u, _, hu⟩
  · subst w; omega
  · unfold Pr at hu
    rw [hroot] at hu
    omega

def PointTest (st : St) (v : Nat) : Prop :=
  if st.P v = -1 then 2 ≤ st.Sp v else 1 ≤ st.Sp v

def BridgeTest (targets : Nat → List Nat) (st : St) (p v : Nat) : Prop :=
  st.P v = (p : Int) ∧ st.O p < st.L v ∧ (targets v).count p < 2

def EmitsPoint (st : St) (v : Nat) : Prop := 0 ≤ st.Fi v ∧ PointTest st v

def EmitsBridge (targets : Nat → List Nat) (st : St) (p v : Nat) : Prop :=
  0 ≤ st.Fi v ∧ BridgeTest targets st p v

theorem root_sep_count {n : Nat} {hd tg : Nat → Nat} {st : St}
    (G : GH n hd tg) (I : MInv n hd tg st) {v : Nat} (hv : v ∈ st.Vis) (hr : st.P v = -1) :
    st.Sp v = ((st.Vis.filter (fun c => decide (Pr st.P v c ∧ 0 ≤ st.Fi c))).length : Int) := by
  rw [I.sep_cnt v hv]
  congr 2
  apply List.filter_congr
  intro c _
  by_cases h : Pr st.P v c
  · simp [root_child_separates G I hr h]
  · simp [h]

/-- The mathematical output at a completed search uses the same root and internal-vertex
conditions as the C++ articulation test. -/
theorem point_test_final {edges : List Edge} {n : Nat} {targets : Nat → List Nat}
    (H : RowsRepresent edges n targets) {st : St}
    (I : MInv n (offsets (rows n targets)) (endpoints (rows n targets)) st)
    (hsp : st.sp = 0) (hall : ∀ x, x < n → x ∈ st.Vis) {v : Nat} (hv : v < n) :
    EmitsPoint st v ↔ ∃ a b, v ≠ a ∧ v ≠ b ∧ Adj edges v a ∧ Adj edges v b ∧
      ¬ Rtc (LlFinal.EV (Adj edges) v) a b := by
  have L := H.final I hsp hall
  have hvV := hall v hv
  have hfin := fin_all I hsp v hvV
  have hsep : 0 ≤ st.Sp v := by rw [I.sep_cnt v hvV]; exact Int.natCast_nonneg _
  have hnone : parO st.P v = none ↔ st.P v = -1 := by
    unfold parO
    split
    · simp_all
      omega
    · simp only [true_iff]
      exact I.par_neg v (by omega)
  have h1 : 1 ≤ (st.Sp v).toNat ↔ 1 ≤ st.Sp v := by omega
  have h2 : 2 ≤ (st.Sp v).toNat ↔ 2 ≤ st.Sp v := by omega
  rw [← articulation_iff L hv]
  simp only [EmitsPoint, hfin, true_and, Art, hnone, Ne, h1, h2, PointTest]
  split <;> simp_all


def bridgeKey (p v : Nat) : Int × Int := (min (p : Int) (v : Int), max (p : Int) (v : Int))

theorem bridgeKey_symm (p v : Nat) : bridgeKey p v = bridgeKey v p := by
  simp [bridgeKey, Int.min_comm, Int.max_comm]

/-- In a completed forest the two normalized endpoints identify at most one directed tree edge. -/
theorem bridgeKey_injective {n : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) {p v p' v' : Nat}
    (hp : Pr st.P p v) (hp' : Pr st.P p' v')
    (hk : bridgeKey p v = bridgeKey p' v') : p = p' ∧ v = v' := by
  have ho := (I.par_ok p v hp).2.2
  have ho' := (I.par_ok p' v' hp').2.2
  have ha := congrArg Prod.fst hk
  have hb := congrArg Prod.snd hk
  change min (p : Int) (v : Int) = min (p' : Int) (v' : Int) at ha
  change max (p : Int) (v : Int) = max (p' : Int) (v' : Int) at hb
  have hpair : (p = p' ∧ v = v') ∨ (p = v' ∧ v = p') := by omega
  rcases hpair with h | ⟨he, he'⟩
  · exact h
  · subst p'; subst v'
    omega

def OccurrenceBridge (edges : List Edge) (key : Int × Int) : Prop :=
  ∃ before after a b, edges = before ++ (a, b) :: after ∧ bridgeKey a b = key ∧
    ¬ Rtc (Adj (before ++ after)) a b

theorem occurrence_emission {before after : List Edge} {n a b : Nat} {targets : Nat → List Nat}
    (H : RowsRepresent (before ++ (a, b) :: after) n targets) {st : St}
    (I : MInv n (offsets (rows n targets)) (endpoints (rows n targets)) st)
    (hsp : st.sp = 0) (hall : ∀ x, x < n → x ∈ st.Vis) :
    (¬ Rtc (Adj (before ++ after)) a b) ↔ EmitsBridge targets st a b ∨ EmitsBridge targets st b a := by
  have L := H.final I hsp hall
  have hag : Adj (before ++ (a, b) :: after) a b := Or.inl (by simp)
  have ha := H.range b a (hag.elim Or.inr Or.inl)
  have hb := H.range a b hag
  have hcast (p v : Nat) (hp : p < n) (hv : v < n) (hpar : Pr st.P p v) :
      st.O p < st.L v ↔ (st.L v).toNat = (st.O v).toNat := by
    have hp0 := (I.ord_lt_len (hall p hp)).1
    have hl0 := (I.low_le v (hall v hv)).1
    have hc : st.O p < st.L v ↔ (st.O p).toNat < (st.L v).toNat := by omega
    exact hc.trans (parent_order_lt_low L (parO_some.mpr hpar))
  have hcounts (p v : Nat) (hv : v < n) (hne : v ≠ p)
      (he : copies (before ++ (a, b) :: after) v p = copies (before ++ (a, b) :: after) a b) :
      (targets v).count p < 2 ↔ ¬ Adj (before ++ after) a b := by
    rw [H.count v p hv hne, he, ← copies_parallel]
    omega
  have hdir : ∀ u v : Nat, u < n → v < n →
      copies (before ++ (a, b) :: after) v u = copies (before ++ (a, b) :: after) a b →
      (EmitsBridge targets st u v ↔ ¬ Adj (before ++ after) a b ∧
        parO st.P v = some u ∧ (st.L v).toNat = (st.O v).toNat) := by
    intro u v hu hv he
    have hf := fin_all I hsp v (hall v hv)
    simp only [EmitsBridge, BridgeTest, hf, true_and, parO_some]
    by_cases hp : st.P v = (u : Int)
    · have hord := (I.par_ok u v hp).2.2
      have hne : v ≠ u := by intro h; subst v; omega
      rw [hcast u v hu hv hp, hcounts u v hv hne he]
      simp [hp, and_comm]
    · simp [hp]
  rw [occurrence_bridge_iff before after a b L,
    hdir a b ha hb (copies_swap _ _ _), hdir b a hb ha rfl]
  tauto

theorem bridge_test_final {edges : List Edge} {n : Nat} {targets : Nat → List Nat}
    (H : RowsRepresent edges n targets) {st : St}
    (I : MInv n (offsets (rows n targets)) (endpoints (rows n targets)) st)
    (hsp : st.sp = 0) (hall : ∀ x, x < n → x ∈ st.Vis) (key : Int × Int) :
    (∃ p v, EmitsBridge targets st p v ∧ bridgeKey p v = key) ↔ OccurrenceBridge edges key := by
  constructor
  · rintro ⟨p, v, he, hk⟩
    have ha := (I.par_ok p v he.2.1).2.1
    rw [H.view.2] at ha
    rcases ha.2 with h | h
    · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp h
      subst edges
      exact ⟨before, after, p, v, rfl, hk, (occurrence_emission H I hsp hall).mpr (Or.inl he)⟩
    · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp h
      subst edges
      exact ⟨before, after, v, p, rfl, (bridgeKey_symm v p).trans hk,
        (occurrence_emission H I hsp hall).mpr (Or.inr he)⟩
  · rintro ⟨before, after, a, b, rfl, hk, h⟩
    rcases (occurrence_emission H I hsp hall).mp h with he | he
    · exact ⟨a, b, he, hk⟩
    · exact ⟨b, a, he, (bridgeKey_symm b a).trans hk⟩


def PointMember (st : St) (pending : Option Nat) (x : Int) : Prop :=
  ∃ u : Nat, (u : Int) = x ∧ (EmitsPoint st u ∨ pending = some u ∧ PointTest st u)

def BridgeMember (targets : Nat → List Nat) (st : St) (key : Int × Int) : Prop :=
  ∃ p v, EmitsBridge targets st p v ∧ bridgeKey p v = key

def PointsMatch (st : St) (pending : Option Nat) (out : Array Int) : Prop :=
  out.toList.Nodup ∧ ∀ x, x ∈ out.toList ↔ PointMember st pending x

def BridgesMatch (targets : Nat → List Nat) (st : St) (out : Array (Int × Int)) : Prop :=
  out.toList.Nodup ∧ ∀ k, k ∈ out.toList ↔ BridgeMember targets st k

theorem point_pending {st : St} (v : Nat) (points : Array Int) (hfin : st.Fi v < 0)
    (A : PointsMatch st none points) (emit : Bool) (he : emit = true ↔ PointTest st v) :
    PointsMatch st (some v) (if emit then points.push v else points) := by
  cases emit with
  | false =>
    have hn : ¬ PointTest st v := by simp at he; exact he
    refine ⟨A.1, fun x => (A.2 x).trans ?_⟩
    simp only [PointMember, reduceCtorEq, false_and, or_false, Option.some.injEq]
    constructor
    · rintro ⟨u, hu, hp⟩; exact ⟨u, hu, Or.inl hp⟩
    · rintro ⟨u, hu, hp | ⟨rfl, hf⟩⟩
      · exact ⟨u, hu, hp⟩
      · exact False.elim (hn hf)
  | true =>
    have hv := he.mp rfl
    have hmem : (v : Int) ∉ points.toList := by
      intro hx
      obtain ⟨u, hu, ht | ⟨he, _⟩⟩ := (A.2 _).mp hx
      · have hui : u = v := by omega
        subst u
        exact (not_le_of_gt hfin) ht.1
      · cases he
    simp only [ite_true, PointsMatch, Array.toList_push]
    refine ⟨List.nodup_append.mpr ⟨A.1, (by simp), ?_⟩, fun x => ?_⟩
    · intro a ha b hb hab
      have hb' : b = (v : Int) := by simpa using hb
      exact hmem ((hab.trans hb') ▸ ha)
    · rw [List.mem_append, A.2]
      simp only [PointMember, List.mem_singleton, reduceCtorEq, false_and, or_false, Option.some.injEq]
      constructor
      · rintro (⟨u, hu, hp⟩ | hx)
        · exact ⟨u, hu, Or.inl hp⟩
        · exact ⟨v, hx.symm, Or.inr ⟨rfl, hv⟩⟩
      · rintro ⟨u, hu, hp | ⟨rfl, _⟩⟩
        · exact Or.inl ⟨u, hu, hp⟩
        · exact Or.inr hu.symm

theorem point_pop {n v : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (points : Array Int) (A : PointsMatch st (some v) points) :
    PointsMatch (popS st v) none points := by
  have hold := pop_preserves_finished I hsp htop
  have hv := (I.sk_mem (st.sp - 1) (by omega)).2
  rw [htop] at hv
  have hself : st.P v ≠ (v : Int) := fun he => (Int.lt_irrefl _) ((I.par_ok v v he).2.2)
  refine ⟨A.1, fun x => (A.2 x).trans ?_⟩
  simp only [PointMember, reduceCtorEq, false_and, or_false, Option.some.injEq, EmitsPoint]
  apply exists_congr
  intro u
  apply and_congr_right
  intro _
  by_cases hu : u = v
  · subst u
    simp [PointTest, popS, upd_same, hself, show ¬0 ≤ st.Fi v by omega]
  · have hf : (popS st v).Fi u = st.Fi u := upd_ne _ _ _ _ hu
    have hne : v ≠ u := Ne.symm hu
    by_cases hfin : 0 ≤ st.Fi u
    · obtain ⟨_, _, hp, hs, _⟩ := hold u hfin
      simp [hf, hfin, hne, PointTest, hp, hs]
    · simp [hf, hfin, hne]

theorem bridge_pop {n v : Nat} {hd tg : Nat → Nat} {st : St}
    (I : MInv n hd tg st) (hsp : 0 < st.sp) (htop : st.Sk (st.sp - 1) = v)
    (targets : Nat → List Nat) (bridges : Array (Int × Int)) (A : BridgesMatch targets st bridges) :
    BridgesMatch targets (popS st v)
      (if 0 ≤ st.P v ∧ st.O (st.P v).toNat < st.L v ∧ (targets v).count (st.P v).toNat < 2
        then bridges.push (bridgeKey (st.P v).toNat v) else bridges) := by
  have hv := (I.sk_mem (st.sp - 1) (by omega)).2
  rw [htop] at hv
  have hself : st.P v ≠ (v : Int) := fun he => (Int.lt_irrefl _) ((I.par_ok v v he).2.2)
  have hold := pop_preserves_finished I hsp htop
  have membership (k : Int × Int) : BridgeMember targets (popS st v) k ↔
      BridgeMember targets st k ∨ ∃ p, BridgeTest targets st p v ∧ bridgeKey p v = k := by
    constructor
    · rintro ⟨p, u, he, hk⟩
      have ht := he.1
      change 0 ≤ upd st.Fi v (st.Vis.length : Int) u at ht
      by_cases hu : u = v
      · subst u
        exact Or.inr ⟨p, by simpa [BridgeTest, popS, hself] using he.2, hk⟩
      · rw [upd_ne _ _ _ _ hu] at ht
        have hl := (hold u ht).2.1
        have hb := he.2
        change st.P u = (p : Int) ∧ st.O p < (popS st v).L u ∧ _ at hb
        rw [hl] at hb
        exact Or.inl ⟨p, u, ⟨ht, hb⟩, hk⟩
    · rintro (⟨p, u, he, hk⟩ | ⟨p, he, hk⟩)
      · obtain ⟨_, hl, _, _, hf⟩ := hold u he.1
        exact ⟨p, u, ⟨by simpa [hf] using he.1, by
          change st.P u = (p : Int) ∧ st.O p < (popS st v).L u ∧ _
          rw [hl]
          exact he.2⟩, hk⟩
      · exact ⟨p, v, ⟨by simp [popS, upd_same], by simpa [BridgeTest, popS, hself] using he⟩, hk⟩
  have event (k : Int × Int) :
      (∃ p, BridgeTest targets st p v ∧ bridgeKey p v = k) ↔
        (0 ≤ st.P v ∧ st.O (st.P v).toNat < st.L v ∧ (targets v).count (st.P v).toNat < 2) ∧
        bridgeKey (st.P v).toNat v = k := by
    constructor
    · rintro ⟨p, ⟨hp, ho, hc⟩, hk⟩
      simp only [hp, Int.toNat_natCast, Int.natCast_nonneg, true_and]
      exact ⟨⟨ho, hc⟩, hk⟩
    · rintro ⟨⟨hp, ho, hc⟩, hk⟩
      exact ⟨_, ⟨by omega, ho, hc⟩, hk⟩
  split
  · rename_i he
    have hpar : Pr st.P (st.P v).toNat v := by unfold Pr; omega
    have fresh : bridgeKey (st.P v).toNat v ∉ bridges.toList := by
      intro hk
      obtain ⟨p, u, hu, hk⟩ := (A.2 _).mp hk
      have hEq := (bridgeKey_injective I hu.2.1 hpar hk).2
      subst u
      exact (not_le_of_gt hv) hu.1
    rw [BridgesMatch, Array.toList_push]
    refine ⟨List.nodup_append.mpr ⟨A.1, (by simp), ?_⟩, fun k => ?_⟩
    · intro a ha b hb hab
      have hb' : b = bridgeKey (st.P v).toNat v := by simpa using hb
      exact fresh ((hab.trans hb') ▸ ha)
    · rw [List.mem_append, A.2, membership, event]
      simp [he, eq_comm]
  · rename_i he
    exact ⟨A.1, fun k => (A.2 k).trans (by rw [membership, event]; simp [he])⟩


/-- Starting or scanning a frame can modify active vertices but cannot make an output ready. -/
theorem output_unchanged {n : Nat} {hd tg : Nat → Nat} {before after : St}
    (I : MInv n hd tg before) (stable : PreservesFinished before after)
    (hfin : after.Fi = before.Fi) (hord : ∀ x ∈ before.Vis, after.O x = before.O x)
    (targets : Nat → List Nat) (points : Array Int) (bridges : Array (Int × Int))
    (P : PointsMatch before none points) (B : BridgesMatch targets before bridges) :
    PointsMatch after none points ∧ BridgesMatch targets after bridges := by
  have point (x : Nat) : EmitsPoint after x ↔ EmitsPoint before x := by
    unfold EmitsPoint
    rw [hfin]
    apply and_congr_right
    intro h
    obtain ⟨_, _, hp, hs, _⟩ := stable x h
    simp [PointTest, hp, hs]
  have bridge (p v : Nat) : EmitsBridge targets after p v ↔ EmitsBridge targets before p v := by
    unfold EmitsBridge
    rw [hfin]
    apply and_congr_right
    intro h
    obtain ⟨_, hl, hp, _, _⟩ := stable v h
    unfold BridgeTest
    rw [hp, hl]
    apply and_congr_right
    intro hv
    rw [hord p (I.par_ok p v hv).1]
  exact ⟨⟨P.1, fun x => (P.2 x).trans (by simp [PointMember, point])⟩,
    ⟨B.1, fun k => (B.2 k).trans (by simp [BridgeMember, bridge])⟩⟩

/-- The root uses its number of children. For an internal vertex the flag tracks whether one
of its already completed children separates it from an ancestor. -/
def ArtFrame (st : St) (v : Nat) (flag : Bool) (children : Int) : Prop :=
  (flag = true ↔ st.P v ≠ -1 ∧ 1 ≤ st.Sp v) ∧ (st.P v = -1 → children = st.Sp v)

theorem art_frame_enter (st : St) (v : Nat) (hz : st.Sp v = 0) : ArtFrame st v false 0 := by
  simp [ArtFrame, hz]

theorem art_frame_advance (st : St) (v w : Nat) (flag : Bool) (children : Int)
    (H : ArtFrame st v flag children) : ArtFrame (advanceVisited st v w) v flag children := by
  unfold advanceVisited
  split
  · exact H
  · exact H

theorem art_frame_return {n p v : Nat} {hd tg : Nat → Nat} {st : St}
    (G : GH n hd tg) (I : MInv n hd tg st) (hpar : st.P v = (p : Int))
    (flag : Bool) (children : Int) (H : ArtFrame st p flag children) (parallel : Bool) :
    let childLow := effectiveLow (st.L v) (if parallel then some (st.O p) else none)
    let flag' := if decide (st.P p ≠ -1) && decide (st.O p ≤ childLow) then true else flag
    ArtFrame (popS st v) p flag' (children + 1) := by
  obtain ⟨_, hsep, _, _, _⟩ := pop_child_values I hpar none parallel
  have hs : 0 ≤ st.Sp p := by
    rw [I.sep_cnt p (I.par_ok p v hpar).1]
    exact Int.natCast_nonneg _
  have hSp : (popS st v).Sp p = st.Sp p + (if st.O p ≤ st.L v then 1 else 0) := by
    simp only [popS, ite_eq_left hpar]
  have hchild := (effective_return (st.O p) (st.L p) (st.L v) none parallel
    (I.low_le p (I.par_ok p v hpar).1).2).2.1
  simp only [ArtFrame, hSp]
  by_cases hr : st.P p = -1
  · have hroot := root_child_separates G I hr hpar
    have hf : flag ≠ true := fun h => (H.1.mp h).1 hr
    have hPar : (popS st v).P p = -1 := hr
    simp [hr, hPar, hroot, hf, H.2 hr]
  · have hPar : (popS st v).P p ≠ -1 := hr
    simp only [hr, ne_eq, not_false_eq_true, decide_true, Bool.true_and, hPar, true_and, false_implies, and_true]
    simp only [hchild]
    split
    · rename_i he
      simp only [decide_eq_true_eq] at he
      simp [he]
      omega
    · rename_i he
      simp only [decide_eq_true_eq] at he
      simpa [he, hr] using H.1

theorem art_frame_exit (st : St) (v : Nat) (flag : Bool) (children : Int)
    (H : ArtFrame st v flag children) :
    (if decide (st.P v = -1) && decide (2 ≤ children) then true else flag) = true ↔ PointTest st v := by
  by_cases hr : st.P v = -1
  · have hf : flag ≠ true := fun h => (H.1.mp h).1 hr
    simp [PointTest, hr, H.2 hr, hf]
  · simp [PointTest, hr, H.1]

end Proofs.Cpp.ListLowlink
