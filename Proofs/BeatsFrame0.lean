import Proofs.BeatsDownF
import Proofs.BeatsAssemble
import Proofs.BeatsSums2
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

abbrev Stp0 (qa qb : Nat) (x : Int) := stepF (clsMin qa qb x) (fun _ => Cellh.capMaxC x)

theorem cls_stop0 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMin qa qb x nd lo hi = Cls.stop) :
    stopP 0 qa qb x nd lo hi := by
  have : clsOf 0 qa qb x nd lo hi = Cls.stop := by simpa [clsOf] using h
  exact (clsOf_stop_iff 0 qa qb x nd lo hi (by decide)).mp this

theorem cls_whole0 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMin qa qb x nd lo hi = Cls.whole) :
    ¬ stopP 0 qa qb x nd lo hi ∧ wholeP 0 qa qb x nd lo hi := by
  have : clsOf 0 qa qb x nd lo hi = Cls.whole := by simpa [clsOf] using h
  exact (clsOf_whole_iff 0 qa qb x nd lo hi (by decide)).mp this

theorem cls_down0 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMin qa qb x nd lo hi = Cls.down) :
    ¬ stopP 0 qa qb x nd lo hi ∧ ¬ wholeP 0 qa qb x nd lo hi := by
  constructor
  · intro hs
    have := (clsOf_stop_iff 0 qa qb x nd lo hi (by decide)).mpr hs
    simp [clsOf, h] at this
  · intro hw
    by_cases hs : stopP 0 qa qb x nd lo hi
    · have := (clsOf_stop_iff 0 qa qb x nd lo hi (by decide)).mpr hs
      simp [clsOf, h] at this
    · have := (clsOf_whole_iff 0 qa qb x nd lo hi (by decide)).mpr ⟨hs, hw⟩
      simp [clsOf, h] at this

/-- The statement proved for the subtree `t` at the heap node `k` covering `[lo, hi)` (continuation-passing). -/
def InSks : Sk → Nat → Nat → Prop
  | .leaf, _, _ => False
  | .node l r, k, e => e = k ∨ InSks l (2 * k + 1) e ∨ InSks r (2 * k + 2) e

/-- `e` is an inner node of the subtree `t` rooted at index `k`. -/
def InSk (t : BT) (k e : Nat) : Prop := InSks t.skel k e

theorem InSk_applyTag (tg : Tag) (nd : Nd) (l : BT) (k e : Nat) : InSk (applyTag tg nd l) k e ↔ InSk l k e := by
  unfold InSk; rw [skel_applyTag]

theorem InSks_lt : ∀ (s : Sk) (k L e : Nat), IdxOKs s k L → InSks s k e → 2 * e + 2 < L
  | .leaf, k, L, e, _, h => by cases h
  | .node l r, k, L, e, hI, h => by
    rcases h with h | h | h
    · rw [h]; exact hI.1
    · exact InSks_lt l _ L e hI.2.1 h
    · exact InSks_lt r _ L e hI.2.2 h

def FrameI (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → chminSafe qa qb x t lo hi →
    HRel inf b H → ValidOK b → Lens b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → EntRep b ne E → sp + t.height + 2 ≤ L → ne + innerOf t + 1 < L → (lo ≤ hi ∧ 2 * hi < M31) →
    (∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp0 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk t k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) t lo hi) k → Enew.length ≤ innerOf t →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 0 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) →
    ∃ bf nef F, F ≤ F0 + nodesOf t ∧ RunsE mv F P pre inf n 0 qa qb x b sp ne bf nef (nodesOf t * 117614 + C0) (nodesOf t * 47 + Wc) ∧ Fin bf nef

def FrameP (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap),
    FrameI mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H

theorem stateOK_of {b : BS} {inf : Int} {sp ne L k lo hi : Nat} {S : List Fr} {E : List Nat} {H : Heap} {t : BT}
    (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t k L) (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hH : HRel inf b H) (hsp : sp + t.height + 2 ≤ L) (hne : ne + innerOf t + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31) :
    StateOK b inf sp ne L k lo hi S E H := by
  refine ⟨hV, hLens, ?_, ?_, by omega, by omega, by have := hlh.1; have := hlh.2; omega, hstk, hent, hH⟩
  · cases t with
    | leaf nd => exact hidx
    | node nd tg l r => exact hidx.1
  · have := hstk.1
    simp at this
    omega

theorem runsE_weaken {mv : MV} {fu : Nat} {P pre : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {b : BS} {sp ne : Nat}
    {bf : BS} {nef C W C' W' : Nat} (h : RunsE mv fu P pre inf n op qa qb x b sp ne bf nef C W) (hc : C ≤ C') (hw : W ≤ W') :
    RunsE mv fu P pre inf n op qa qb x b sp ne bf nef C' W' := by
  obtain ⟨r, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨r, h1, h2, h3, h4, le_trans h5 hc, le_trans h6 hw⟩

theorem travBT_stop (cls : Nd → Nat → Nat → Cls) (actBT : BT → BT) (t : BT) (lo hi : Nat) (hc : cls t.nd lo hi = Cls.stop) :
    travBT cls actBT t lo hi = t := by
  cases t with
  | leaf nd => simp only [BT.nd] at hc; unfold travBT; rw [hc]
  | node nd tg l r => simp only [BT.nd] at hc; unfold travBT; rw [hc]

theorem travBT_whole (cls : Nd → Nat → Nat → Cls) (actBT : BT → BT) (t : BT) (lo hi : Nat) (hc : cls t.nd lo hi = Cls.whole) :
    travBT cls actBT t lo hi = actBT t := by
  cases t with
  | leaf nd => simp only [BT.nd] at hc; unfold travBT; rw [hc]
  | node nd tg l r => simp only [BT.nd] at hc; unfold travBT; rw [hc]

theorem frame0_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hnd : clsMin qa qb x t.nd lo hi ≠ Cls.down) : FrameI mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by
    have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev.hLM; omega
  have hn1 : 1 ≤ nodesOf t := by cases t <;> (show 1 ≤ nodesS _; unfold nodesS; first | omega | (split <;> omega))
  have hcost : 117614 + C0 ≤ nodesOf t * 117614 + C0 := by have := Nat.mul_le_mul_right 117614 hn1; omega
  have hwk : 47 + Wc ≤ nodesOf t * 47 + Wc := by have := Nat.mul_le_mul_right 47 hn1; omega
  -- the traversal at this node is not a descent
  cases hc : clsMin qa qb x t.nd lo hi with
  | down => exact absurd hc hnd
  | stop =>
    have hst := cls_stop0 qa qb x t.nd lo hi hc
    rw [← hnd0] at hst
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_stop Ev St hst (by decide)
    have hK := K b' ne H [] h1 h2 (by simpa using h3) h4 h5 (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial (fun _ _ => rfl)
      (by rw [travBT_stop _ _ t lo hi hc]; simpa [upPhase] using hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 0 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    refine ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩
  | whole =>
    have hwh := cls_whole0 qa qb x t.nd lo hi hc
    rw [← hnd0] at hwh
    have hxne : x ≠ inf := by rw [Ev.hinfI]; exact Int.ne_of_lt hx.2
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_whole0 Ev St hwh.1 hwh.2 rfl hxne
    have hK := K b' ne (H.set k (Cellh.capMaxC x (H k))) [] h1 h2 (by simpa using h3) h4 h5
      (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial
      (fun j hj => Heap.set_ne _ _ _ _ (fun e => hj (e ▸ descN_self _)))
      (by rw [travBT_whole _ _ t lo hi hc]; simpa [upPhase] using agree_capMaxBT H t k x hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 0 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    exact ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩

theorem SameLen_trans {b b' b'' : BS} (h1 : SameLen b b') (h2 : SameLen b' b'') : SameLen b b'' :=
  ⟨by rw [h2.l0, h1.l0], by rw [h2.l1, h1.l1], by rw [h2.l2, h1.l2], by rw [h2.l3, h1.l3], by rw [h2.l4, h1.l4],
   by rw [h2.l5, h1.l5], by rw [h2.l6, h1.l6], by rw [h2.l7, h1.l7], by rw [h2.l8, h1.l8], by rw [h2.l9, h1.l9],
   by rw [h2.l10, h1.l10], by rw [h2.l11, h1.l11], by rw [h2.l12, h1.l12], by rw [h2.l13, h1.l13], by rw [h2.l14, h1.l14],
   by rw [h2.leneq, h1.leneq]⟩

theorem LenOKs_of_eq {b b' : BS} (h : b'.len = b.len) : ∀ (sk : Sk) (k lo hi : Nat), LenOKs b sk k lo hi → LenOKs b' sk k lo hi
  | .leaf, k, lo, hi, hk => by unfold LenOKs at hk ⊢; rw [h]; exact hk
  | .node l r, k, lo, hi, hk => by
    unfold LenOKs at hk ⊢
    exact ⟨by rw [h]; exact hk.1, LenOKs_of_eq h l _ _ _ hk.2.1, LenOKs_of_eq h r _ _ _ hk.2.2⟩

end Proofs.BeatsRep
