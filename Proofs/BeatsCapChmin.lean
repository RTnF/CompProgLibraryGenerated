import Proofs.BeatsCapCtor

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec

variable {K : Nat}
structure EnvK (K : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (x : Int) (L : Nat) : Prop where
  hnv : mv.nv = 15
  hty : ∀ v, v < 9 → mv.ty v = s64
  hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32
  hinf : s64.valid inf = true
  hninf : s64.valid (-inf) = true
  hnM : n < M31
  hopM : op < M31
  hqaM : qa < M31
  hqbM : qb < M31
  hx : s64.valid x = true
  hLM : L < M31
  hinfI : inf = INF
  hKM : K < M31

/-- The facts about the current state that every iteration needs. -/
structure StateOKK (K : Nat) (b : BS) (inf : Int) (sp ne : Nat) (L : Nat) (W0 W1 W2 : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop where
  hV : ValidOK b
  hLens : CapS K b L
  hk : 2 * W0 + 2 < L
  hsp : 0 < sp
  hspL : sp + 2 ≤ K
  hneL : ne + 1 < L
  hlohi : W1 + W2 < M31
  hstk : StkRep b sp (⟨W0, W1, W2⟩ :: S)
  hent : EntRep b ne E
  hH : HRel inf b H

theorem step_stop {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK K mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOKK K b inf sp ne L W0 W1 W2 S E H) (hstop : stopP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧
      ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_stop mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hstop hop H St.hH
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_whole0 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK K mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOKK K b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hwhole : wholeP op qa qb x (decNd b W0) W1 W2) (hop0 : op = 0) (hxne : x ≠ inf) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' (H.set W0 (Cellh.capMaxC x (H W0))) ∧
      StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_whole0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hnot hwhole hop0 hxne H St.hH
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_down_set {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK K mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOKK K b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hnotw : ¬ wholeP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) (hmode : b.lval.getD W0 0 ≠ inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)) (hint : b.len.getD W0 0 ≠ 1) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1 + 2) (ne + 1) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧
      EntRep b' (ne + 1) (W0 :: E) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : ne + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_down_set mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent
    hnot hnotw hop hne1 hsp2 Ev.hinfI hmode hlenL hlenR hmode H St.hH hint
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩

theorem step_down_add {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK K mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOKK K b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hnotw : ¬ wholeP op qa qb x (decNd b W0) W1 W2) (hop : op < 4) (hmode : b.lval.getD W0 0 = inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int))
    (hZ3 : b.mxv.getD W0 0 ≠ inf) (hZ5 : b.mnv.getD W0 0 ≠ inf)
    (hlv1 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0 ≠ inf)
    (hlv2 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0 ≠ inf)
    (hint : b.len.getD W0 0 ≠ 1)
    (hS0 : s64.valid (b.mxv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS1 : b.smx.getD (2 * W0 + 1) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS2 : s64.valid (b.mnv.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS3 : b.smn.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS4 : (b.lval.getD (2 * W0 + 1) 0 = inf ∧ b.len.getD (2 * W0 + 1) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS5 : b.lval.getD (2 * W0 + 1) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 1) 0 + b.ladd.getD W0 0) = true)
    (hS6 : s64.valid (b.mxv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS7 : b.smx.getD (2 * W0 + 2) 0 ≠ -inf → s64.valid (b.smx.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS8 : s64.valid (b.mnv.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS9 : b.smn.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.smn.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS10 : (b.lval.getD (2 * W0 + 2) 0 = inf ∧ b.len.getD (2 * W0 + 2) 0 ≠ 1) → s64.valid (b.ladd.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true)
    (hS11 : b.lval.getD (2 * W0 + 2) 0 ≠ inf → s64.valid (b.lval.getD (2 * W0 + 2) 0 + b.ladd.getD W0 0) = true) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1 + 2) (ne + 1) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧
      EntRep b' (ne + 1) (W0 :: E) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : ne + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_down_add mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent
    hnot hnotw hop hne1 hsp2 Ev.hinfI hmode hlenL hlenR hZ3 hZ5 hlv1 hlv2 H St.hH hint hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9 hS10 hS11
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩


end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
variable {SC : Nat}
def FrameI (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → chminSafe qa qb x t lo hi →
    HRel inf b H → ValidOK b → CapS SC b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → EntRep b ne E → sp + t.height + 2 ≤ SC → ne + innerOf t + 1 < L → (lo ≤ hi ∧ 2 * hi < M31) →
    (∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp0 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk t k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) t lo hi) k → Enew.length ≤ innerOf t →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 0 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) →
    ∃ bf nef F, F ≤ F0 + nodesOf t ∧ RunsE mv F P pre inf n 0 qa qb x b sp ne bf nef (nodesOf t * 117614 + C0) (nodesOf t * 47 + Wc) ∧ Fin bf nef


def FrameP (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap),
    FrameI SC mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H


theorem stateOK_of {b : BS} {inf : Int} {sp ne L k lo hi : Nat} {S : List Fr} {E : List Nat} {H : Heap} {t : BT}
    (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t k L) (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hH : HRel inf b H) (hsp : sp + t.height + 2 ≤ SC) (hne : ne + innerOf t + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31) :
    StateOKK SC b inf sp ne L k lo hi S E H := by
  refine ⟨hV, hLens, ?_, ?_, by omega, by omega, by have := hlh.1; have := hlh.2; omega, hstk, hent, hH⟩
  · cases t with
    | leaf nd => exact hidx
    | node nd tg l r => exact hidx.1
  · have := hstk.1
    simp at this
    omega


theorem frame0_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hnd : clsMin qa qb x t.nd lo hi ≠ Cls.down) : FrameI SC mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by
    have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev.hKM; omega
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


end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
variable {SC : Nat}
theorem frame0_down_rec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx1 : -INF < x) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP SC mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP SC mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (xl xr : List Int) (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hsafel : chminSafe qa qb x (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : chminSafe qa qb x (applyTag tg nd r) ((lo + hi) / 2) hi)
    (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ SC) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsMin qa qb x nd lo hi = Cls.down) (hroot : (H k).1 = nd)
    (b1 : BS) (hit : Iter mv P pre inf n 0 qa qb x b sp ne b1 (sp - 1 + 2) (ne + 1))
    (hHR1 : HRel inf b1 (pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int)))
    (hstk1 : StkRep b1 (sp - 1 + 2) (⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S))
    (hent1 : EntRep b1 (ne + 1) (k :: E)) (hV1 : ValidOK b1) (hS1 : SameLen b b1)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp0 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 0 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 0 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
      Fin bf nef := by
  obtain ⟨hlo, hshl, hshr⟩ := hsh
  obtain ⟨hlfl, hlfr⟩ := hlf
  have hag2 := (agree_node H nd tg l r k).mp hag
  have hlsize : ((lo + hi) / 2 - lo : Nat) = l.size := by rw [BT.size_skel, hshl.size]
  have hrsize : (hi - (lo + hi) / 2 : Nat) = r.size := by rw [BT.size_skel, hshr.size]
  have hpush := agree_pushBT H nd tg l r k hag
  rw [← hlsize, ← hrsize] at hpush
  simp only [pushBT] at hpush
  have hp2 := (agree_node _ nd noTag _ _ k).mp hpush
  have hstep : stepF (clsMin qa qb x) (fun _ => Cellh.capMaxC x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ =
      ⟨pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int),
        ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, k :: E⟩ := by
    simp [stepF, hroot, hcd]
  obtain ⟨H0, hH0⟩ : ∃ H0, H0 = pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int) := ⟨_, rfl⟩
  rw [← hH0] at hstep hp2 hpush hHR1
  have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
  have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
  have hht : BT.height (.node nd tg l r) = max l.height r.height + 1 := rfl
  have hml : l.height ≤ max l.height r.height := Nat.le_max_left _ _
  have hmr : r.height ≤ max l.height r.height := Nat.le_max_right _ _
  have hsp0 : 0 < sp := by have := hstk.1; simp at this; omega
  have hinn : innerOf (.node nd tg l r) = innerOf l + innerOf r + 1 := rfl
  have hnod : nodesOf (.node nd tg l r) = nodesOf l + nodesOf r + 1 := rfl
  have hLens1 : CapS SC b1 L := Capacities.of_same hLens hS1
  have hlen1 : b1.len = b.len := hS1.leneq
  -- the left child
  have hLl := LenOKs_of_eq hlen1
  have hlenL' : LenOK b1 (applyTag tg nd l) (2 * k + 1) lo ((lo + hi) / 2) := by
    show LenOKs b1 (applyTag tg nd l).skel _ _ _
    rw [skel_applyTag]; exact hLl _ _ _ _ hlen.2.1
  have hlenR' : LenOK b1 (applyTag tg nd r) (2 * k + 2) ((lo + hi) / 2) hi := by
    show LenOKs b1 (applyTag tg nd r).skel _ _ _
    rw [skel_applyTag]; exact hLl _ _ _ _ hlen.2.2
  have hidxl : IdxOK (applyTag tg nd l) (2 * k + 1) L := by
    show IdxOKs (applyTag tg nd l).skel _ _
    rw [skel_applyTag]; exact hidx.2.1
  have hidxr : IdxOK (applyTag tg nd r) (2 * k + 2) L := by
    show IdxOKs (applyTag tg nd r).skel _ _
    rw [skel_applyTag]; exact hidx.2.2
  have hnl : nodesOf (applyTag tg nd l) = nodesOf l := by show nodesS (applyTag tg nd l).skel = _; rw [skel_applyTag]
  have hnr : nodesOf (applyTag tg nd r) = nodesOf r := by show nodesS (applyTag tg nd r).skel = _; rw [skel_applyTag]
  have hil : innerOf (applyTag tg nd l) = innerOf l := by show innerS (applyTag tg nd l).skel = _; rw [skel_applyTag]
  have hir : innerOf (applyTag tg nd r) = innerOf r := by show innerS (applyTag tg nd r).skel = _; rw [skel_applyTag]
  have hhl := height_applyTag tg nd l
  have hhr := height_applyTag tg nd r
  have hres := ihl (2 * k + 1) lo ((lo + hi) / 2) xl b1 (sp - 1 + 2) (ne + 1) (⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S) (k :: E) H0
    hp2.2.1 hshl' (LeafOK_applyTag tg nd l hlfl) hinvl hsafel hHR1 hV1 hLens1 hidxl hlenL' hstk1 hent1
    (by rw [hhl]; omega) (by rw [hil]; omega) (by have := hlh.1; have := hlh.2; omega) (by
      intro bK neK H1 E1 hHR hS hE hVK hSL hst1 hE1 hI1 hq1 hfr1 hag1 hlE
      have e : sp - 1 + 2 - 1 = sp := by omega
      rw [e] at hS
      have hLensK : CapS SC bK L := Capacities.of_same hLens1 hSL
      have hlenK : bK.len = b.len := hSL.leneq.trans hlen1
      have hag_r : Agree H1 (applyTag tg nd r) (2 * k + 2) :=
        agree_of_eqOn hp2.2.2 (fun j hj => (hfr1 j (fun hd => descN_disjoint k j hd hj)).symm)
      have hneK : neK = ne + 1 + E1.length := by
        have h1 := hE.1; have h0 := hent.1; simp at h1; omega
      have hlenR'' : LenOK bK (applyTag tg nd r) (2 * k + 2) ((lo + hi) / 2) hi := by
        show LenOKs bK (applyTag tg nd r).skel _ _ _
        rw [skel_applyTag]; exact LenOKs_of_eq hlenK _ _ _ _ hlen.2.2
      have h5 : E1.length ≤ innerOf l := by have := hlE; rwa [hil] at this
      have h6 : neK + innerOf (applyTag tg nd r) + 1 < L := by
        rw [hir, hneK]; have h7 := hne; rw [hinn] at h7; omega
      have hKres := ihr (2 * k + 2) ((lo + hi) / 2) hi xr bK sp neK S (E1 ++ k :: E) H1 hag_r hshr'
        (LeafOK_applyTag tg nd r hlfr) hinvr hsafer hHR hVK hLensK hidxr hlenR'' hS hE
        (by rw [hhr]; omega) h6 (by have := hlh.1; have := hlh.2; omega) (by
          intro bK2 neK2 H2 E2 hHR2 hS2 hE2 hV2 hSL2 hst2 hEn2 hI2 hq2 hfr2 hag2 hlE2
          have hbig := down_assemble (clsMin qa qb x) (fun _ => Cellh.capMaxC x) (capMaxBT x) nd tg l r k lo hi H H0 H1 H2 S E E1 E2
            hH0 hstep hpush hst1 hE1 hfr1 hag1 hst2 hEn2 hfr2 hag2 hcd hroot
          obtain ⟨c1, c2, c3, c4⟩ := hbig
          have hIall : ∀ e ∈ E2 ++ E1 ++ [k], InSk (.node nd tg l r) k e := by
            intro e he
            simp only [List.mem_append, List.mem_singleton] at he
            show e = k ∨ InSk l (2 * k + 1) e ∨ InSk r (2 * k + 2) e
            rcases he with (he | he) | he
            · right; right; exact (InSk_applyTag tg nd r _ e).mp (hI2 e he)
            · right; left; exact (InSk_applyTag tg nd l _ e).mp (hI1 e he)
            · left; exact he
          have hq3 : SumsOK (E2 ++ E1 ++ [k]) H2 := by
            have hdl : ∀ j, descN (2 * k + 1) j → H1 j = upPhase E2 H2 j := by
              intro j hj
              rw [upPhase_frame E2 (2 * k + 2) hEn2 H2 j (fun hd => descN_disjoint k j hj hd)]
              exact (hfr2 j (fun hd => descN_disjoint k j hj hd)).symm
            have hdl' : EqOn (2 * k + 1) H1 (upPhase E2 H2) := hdl
            rw [SumsOK_append, SumsOK_append]
            refine ⟨⟨hq2, SumsOK_congr (2 * k + 1) E1 hE1 H1 _ hdl' hq1⟩, ?_, trivial⟩
            refine sumOK_node qa qb x hx1 nd tg l r k lo hi xl xr hinvl hinvr hshl' hshr' hsafel hsafer hlh _ ?_ ?_
            · rw [upPhase_append]
              exact agree_of_eqOn hag1 (upPhase_local E1 (2 * k + 1) hE1 _ _ hdl')
            · rw [upPhase_append]
              exact agree_of_eqOn hag2 (fun j hj => (upPhase_frame E1 (2 * k + 1) hE1 _ j (fun hd => descN_disjoint k j hd hj)).symm)
          refine K bK2 neK2 H2 (E2 ++ E1 ++ [k]) hHR2 hS2 (by simpa [List.append_assoc] using hE2) hV2
            (SameLen_trans hS1 (SameLen_trans hSL hSL2)) c1 c2 hIall hq3 c3 c4 ?_
          have a1 : E1.length ≤ innerOf l := by have := hlE; rwa [hil] at this
          have a2 : E2.length ≤ innerOf r := by have := hlE2; rwa [hir] at this
          rw [hinn]
          simp only [List.length_append, List.length_singleton]
          omega)
      rw [hnr] at hKres
      rw [e]; exact hKres)
  obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hres
  rw [hnl] at hFle hr
  have hspM : sp < M31 := by have := Ev.hKM; omega
  have hr' := runs_of_iter mv Ev.hnv P pre inf n 0 qa qb x b b1 sp ne (sp - 1 + 2) (ne + 1) hspM hsp0 hit F bf nef _ _ hr
  refine ⟨bf, nef, F + 1, by rw [hnod]; omega, runsE_weaken hr' (by rw [hnod]; omega) (by rw [hnod]; omega), hF⟩

theorem frame0_down {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx1 : -INF < x) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP SC mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP SC mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hinv : BeatsModel.Inv (.node nd tg l r) ys) (hsafe : chminSafe qa qb x (.node nd tg l r) lo hi)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ SC) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsMin qa qb x nd lo hi = Cls.down)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp0 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 0 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 0 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
      Fin bf nef := by
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH _ k lo hi hag hsh hlen
  have hnd' : decNd b k = nd := hnd0
  have hroot : (H k).1 = nd := by have := hH k; rw [← this.1]; exact hnd'
  have hdown := cls_down0 qa qb x nd lo hi hcd
  rw [← hnd'] at hdown
  obtain ⟨hps, hsl, hsr⟩ := chminSafe_down qa qb x nd tg l r lo hi hcd hsafe
  obtain ⟨xl, xr, hinvl, hinvr, hys⟩ := Inv.push_parts hinv hps
  have hlfl := hlf
  cases htg : tg.lval with
  | none =>
    have F := down_add_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen hps htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_add Ev St hdown.1 hdown.2 (by decide) F.hmode F.hlenL F.hlenR F.hZ3 F.hZ5
      F.hlv1 F.hlv2 F.hint F.hS0 F.hS1 F.hS2 F.hS3 F.hS4 F.hS5 F.hS6 F.hS7 F.hS8 F.hS9 F.hS10 F.hS11
    exact frame0_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K
  | some v =>
    have F := down_set_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen v htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_set Ev St hdown.1 hdown.2 (by decide) F.hmode F.hlenL F.hlenR F.hint
    exact frame0_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K

theorem leaf_not_down0 (qa qb : Nat) (x : Int) (hx : -INF < x) (nd : Nd) (lo hi : Nat) (hhi : hi = lo + 1) (h1 : nd.smx = -INF)
    (h2 : nd.smn = INF) (h3 : nd.mn = nd.mx) : clsMin qa qb x nd lo hi ≠ Cls.down := by
  intro hd
  unfold clsMin at hd
  by_cases hc : qb ≤ lo ∨ hi ≤ qa ∨ nd.mx ≤ x
  · rw [if_pos hc] at hd; cases hd
  · rw [if_neg hc] at hd
    by_cases hc2 : qa ≤ lo ∧ hi ≤ qb ∧ nd.smx < x
    · rw [if_pos hc2] at hd; cases hd
    · exact hc2 ⟨by omega, by omega, by omega⟩

theorem frame0_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ F0 C0 Wc, FrameP SC mv pre P inf n qa qb x L Fin F0 C0 Wc t := by
  intro h
  induction h with
  | zero =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame0_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down0 qa qb x hx.1 nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      simp [BT.height] at ht
  | succ h ih =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame0_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down0 qa qb x hx.1 nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      intro k lo hi ys b sp ne S E H
      by_cases hcd : clsMin qa qb x nd lo hi = Cls.down
      · intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
        have hht : (BT.node nd tg l r).height = max l.height r.height + 1 := rfl
        have hl : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_left l.height r.height; omega
        have hr : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_right l.height r.height; omega
        exact frame0_down Ev hx.1 Fin F0 C0 Wc nd tg l r (ih _ hl _ _ _) (ih _ hr _ _ _) k lo hi ys b sp ne S E H hag hsh hlf hinv hsafe hH hV
          hLens hidx hlen hstk hent hsp hne hlh hcd K
      · exact frame0_nodown Ev hx Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp ne S E H hcd

end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec

variable {SC : Nat}
theorem iter_upd (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (b : BS) (P : List Cell) (inf : Int) (n op qa qb sp ne : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hneM : ne < M31) (hx : s64.valid x = true)
    (L : Nat) (hV : ValidOK b) (hLens : CapS SC b L) (hLM : L < M31) (e : Nat) (E : List Nat) (hent : EntRep b ne (e :: E))
    (he : 2 * e + 2 < L) (hneL : ne ≤ L)
    (hmc : s64.valid (b.mxc.getD (2 * e + 1) 0 + b.mxc.getD (2 * e + 2) 0) = true)
    (hnc : s64.valid (b.mnc.getD (2 * e + 1) 0 + b.mnc.getD (2 * e + 2) 0) = true) (H : Heap) (hH : HRel inf b H) :
    ∃ b' : BS, HRel inf b' (updateH H e) ∧ EntRep b' (ne - 1) E ∧ ValidOK b' ∧ SameLen b b' ∧ b'.sk = b.sk ∧ b'.sl = b.sl ∧ b'.sr = b.sr ∧
      ∀ fu : Nat, ∃ r : PRM, pexecM mv fu (.sequence (.scope (UpdLoopBody (mv.nv + pre.length))) Sk)
        (gS P (pre ++ LCells inf n op qa qb x sp ne)) (VVB b) = some r ∧ r.ret = none ∧
        r.ps = gS P (pre ++ LCells inf n op qa qb x sp (ne - 1)) ∧ r.vv = VVB b' ∧ r.cost ≤ 24790 ∧ r.wk ≤ 6 := by
  classical
  have hpos : 0 < ne := by have := hent.1; simp at this; omega
  have hDe : b.ent.getD (ne - 1) 0 = (e : Int) := by simpa using hent.2 0 e rfl
  have hl := hLens
  have hk1 : 2 * e + 1 < M31 := by omega
  have hk2 : 2 * e + 2 < M31 := by omega
  have hNe : e < M31 := by omega

  obtain ⟨Z1, hD_Z1⟩ : ∃ Z1 : Int, b.mxv.getD (2 * e + 1) 0 = Z1 := ⟨_, rfl⟩
  obtain ⟨Z2, hD_Z2⟩ : ∃ Z2 : Int, b.mxv.getD (2 * e + 2) 0 = Z2 := ⟨_, rfl⟩
  obtain ⟨Z3, hD_Z3⟩ : ∃ Z3 : Int, b.smx.getD (2 * e + 1) 0 = Z3 := ⟨_, rfl⟩
  obtain ⟨Z4, hD_Z4⟩ : ∃ Z4 : Int, b.smx.getD (2 * e + 2) 0 = Z4 := ⟨_, rfl⟩
  obtain ⟨Z5, hD_Z5⟩ : ∃ Z5 : Int, b.mxc.getD (2 * e + 1) 0 = Z5 := ⟨_, rfl⟩
  obtain ⟨Z6, hD_Z6⟩ : ∃ Z6 : Int, b.mxc.getD (2 * e + 2) 0 = Z6 := ⟨_, rfl⟩
  obtain ⟨Z7, hD_Z7⟩ : ∃ Z7 : Int, b.mnv.getD (2 * e + 1) 0 = Z7 := ⟨_, rfl⟩
  obtain ⟨Z8, hD_Z8⟩ : ∃ Z8 : Int, b.mnv.getD (2 * e + 2) 0 = Z8 := ⟨_, rfl⟩
  obtain ⟨Z9, hD_Z9⟩ : ∃ Z9 : Int, b.smn.getD (2 * e + 1) 0 = Z9 := ⟨_, rfl⟩
  obtain ⟨Z10, hD_Z10⟩ : ∃ Z10 : Int, b.smn.getD (2 * e + 2) 0 = Z10 := ⟨_, rfl⟩
  obtain ⟨Z11, hD_Z11⟩ : ∃ Z11 : Int, b.mnc.getD (2 * e + 1) 0 = Z11 := ⟨_, rfl⟩
  obtain ⟨Z12, hD_Z12⟩ : ∃ Z12 : Int, b.mnc.getD (2 * e + 2) 0 = Z12 := ⟨_, rfl⟩
  have vZ1 : s64.valid Z1 = true := by rw [← hD_Z1]; exact getD_mem_valid b.mxv _ (by have := hl.l0; omega) hV.v0
  have vZ2 : s64.valid Z2 = true := by rw [← hD_Z2]; exact getD_mem_valid b.mxv _ (by have := hl.l0; omega) hV.v0
  have vZ3 : s64.valid Z3 = true := by rw [← hD_Z3]; exact getD_mem_valid b.smx _ (by have := hl.l1; omega) hV.v1
  have vZ4 : s64.valid Z4 = true := by rw [← hD_Z4]; exact getD_mem_valid b.smx _ (by have := hl.l1; omega) hV.v1
  have vZ5 : s64.valid Z5 = true := by rw [← hD_Z5]; exact getD_mem_valid b.mxc _ (by have := hl.l2; omega) hV.v2
  have vZ6 : s64.valid Z6 = true := by rw [← hD_Z6]; exact getD_mem_valid b.mxc _ (by have := hl.l2; omega) hV.v2
  have vZ7 : s64.valid Z7 = true := by rw [← hD_Z7]; exact getD_mem_valid b.mnv _ (by have := hl.l3; omega) hV.v3
  have vZ8 : s64.valid Z8 = true := by rw [← hD_Z8]; exact getD_mem_valid b.mnv _ (by have := hl.l3; omega) hV.v3
  have vZ9 : s64.valid Z9 = true := by rw [← hD_Z9]; exact getD_mem_valid b.smn _ (by have := hl.l4; omega) hV.v4
  have vZ10 : s64.valid Z10 = true := by rw [← hD_Z10]; exact getD_mem_valid b.smn _ (by have := hl.l4; omega) hV.v4
  have vZ11 : s64.valid Z11 = true := by rw [← hD_Z11]; exact getD_mem_valid b.mnc _ (by have := hl.l5; omega) hV.v5
  have vZ12 : s64.valid Z12 = true := by rw [← hD_Z12]; exact getD_mem_valid b.mnc _ (by have := hl.l5; omega) hV.v5
  rw [hD_Z5, hD_Z6] at hmc
  rw [hD_Z11, hD_Z12] at hnc
  obtain ⟨X0, hX0⟩ : ∃ X0 : Int, X0 = (if (Z1 < Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1 : Int, X1 = (if (Z1 > Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X2 : Int, X2 = (if (Z1 = Z2) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ X3 : Int, X3 = (if (X0 = 1) then Z2 else Z1) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ X4 : Int, X4 = (if (X0 = 1) then Z6 else Z5) := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ X5 : Int, X5 = (if (X2 = 1) then (Z5 + Z6) else X4) := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ X6 : Int, X6 = (if (X0 = 1) then Z1 else Z3) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ X7 : Int, X7 = (if (X1 = 1) then Z2 else X6) := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ X8 : Int, X8 = (if (X1 = 1) then Z3 else Z4) := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ X9 : Int, X9 = (if (X7 < X8) then X8 else X7) := ⟨_, rfl⟩
  obtain ⟨X10, hX10⟩ : ∃ X10 : Int, X10 = (if (Z7 < Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X11, hX11⟩ : ∃ X11 : Int, X11 = (if (Z7 > Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X12, hX12⟩ : ∃ X12 : Int, X12 = (if (Z7 = Z8) then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨X13, hX13⟩ : ∃ X13 : Int, X13 = (if (X11 = 1) then Z8 else Z7) := ⟨_, rfl⟩
  obtain ⟨X14, hX14⟩ : ∃ X14 : Int, X14 = (if (X11 = 1) then Z12 else Z11) := ⟨_, rfl⟩
  obtain ⟨X15, hX15⟩ : ∃ X15 : Int, X15 = (if (X12 = 1) then (Z11 + Z12) else X14) := ⟨_, rfl⟩
  obtain ⟨X16, hX16⟩ : ∃ X16 : Int, X16 = (if (X10 = 1) then Z8 else Z9) := ⟨_, rfl⟩
  obtain ⟨X17, hX17⟩ : ∃ X17 : Int, X17 = (if (X11 = 1) then Z7 else X16) := ⟨_, rfl⟩
  obtain ⟨X18, hX18⟩ : ∃ X18 : Int, X18 = (if (X10 = 1) then Z9 else Z10) := ⟨_, rfl⟩
  obtain ⟨X19, hX19⟩ : ∃ X19 : Int, X19 = (if (X18 < X17) then X18 else X17) := ⟨_, rfl⟩
  have vX0 : s64.valid X0 = true := by rw [hX0]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX1 : s64.valid X1 = true := by rw [hX1]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX2 : s64.valid X2 = true := by rw [hX2]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX3 : s64.valid X3 = true := by rw [hX3]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX4 : s64.valid X4 = true := by rw [hX4]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX5 : s64.valid X5 = true := by rw [hX5]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX6 : s64.valid X6 = true := by rw [hX6]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX7 : s64.valid X7 = true := by rw [hX7]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX8 : s64.valid X8 = true := by rw [hX8]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX9 : s64.valid X9 = true := by rw [hX9]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX10 : s64.valid X10 = true := by rw [hX10]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX11 : s64.valid X11 = true := by rw [hX11]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX12 : s64.valid X12 = true := by rw [hX12]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX13 : s64.valid X13 = true := by rw [hX13]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX14 : s64.valid X14 = true := by rw [hX14]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX15 : s64.valid X15 = true := by rw [hX15]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX16 : s64.valid X16 = true := by rw [hX16]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX17 : s64.valid X17 = true := by rw [hX17]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX18 : s64.valid X18 = true := by rw [hX18]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have vX19 : s64.valid X19 = true := by rw [hX19]; (repeat' split) <;> first | assumption | exact hmc | exact hnc | decide
  have key : (⟨X3, X9, X5, X13, X19, X15⟩ : Nd) = mergeNd ⟨Z1, Z3, Z5, Z7, Z9, Z11⟩ ⟨Z2, Z4, Z6, Z8, Z10, Z12⟩ := by
    subst hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13 hX14 hX15 hX16 hX17 hX18 hX19
    unfold mergeNd mergeMax negNd
    simp only [Nd.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Int.neg_neg, Prod.fst, Prod.snd])
    all_goals (repeat' split)
    all_goals simp only []
    all_goals omega
  have hc1 : (H (2 * e + 1)).1 = ⟨Z1, Z3, Z5, Z7, Z9, Z11⟩ := by
    rw [← (hH _).1]; unfold decNd; rw [hD_Z1, hD_Z3, hD_Z5, hD_Z7, hD_Z9, hD_Z11]
  have hc2 : (H (2 * e + 2)).1 = ⟨Z2, Z4, Z6, Z8, Z10, Z12⟩ := by
    rw [← (hH _).1]; unfold decNd; rw [hD_Z2, hD_Z4, hD_Z6, hD_Z8, hD_Z10, hD_Z12]
  have hUC := HRel_UC inf b H e hH (by have := hl.l0; omega) (by have := hl.l1; omega) (by have := hl.l2; omega) (by have := hl.l3; omega)
    (by have := hl.l4; omega) (by have := hl.l5; omega) X3 X5 X9 X13 X15 X19 (by rw [hc1, hc2]; exact key)
  have hvalid := UC_valid b e X3 X5 X9 X13 X15 X19 hV vX3 vX5 vX9 vX13 vX15 vX19
  refine ⟨UC b e X3 X5 X9 X13 X15 X19, hUC, ?_, hvalid, UC_sameLen b e _ _ _ _ _ _, rfl, rfl, rfl, ?_⟩
  · refine ⟨by have := hent.1; simp at this ⊢; omega, ?_⟩
    intro j e' hj
    have h1 := hent.2 (j + 1) e' (by simpa using hj)
    rw [UC_ent]
    have : ne - 1 - 1 - j = ne - 1 - (j + 1) := by omega
    rw [this]
    exact h1
  · intro fu
    obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ := UpdLoop_body mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM hneM hpos hx hV.v0 hV.v1 hV.v2 hV.v3 hV.v4 hV.v5 hV.v14 e hNe hDe Z1 hD_Z1 Z2 hD_Z2 Z3 hD_Z3 Z4 hD_Z4 Z5 hD_Z5 Z6 hD_Z6 Z7 hD_Z7 Z8 hD_Z8 Z9 hD_Z9 Z10 hD_Z10 Z11 hD_Z11 Z12 hD_Z12 (by have := hl.lent; omega) (by have := hl.l0; omega) (by have := hl.l0; omega) (by have := hl.l1; omega) (by have := hl.l1; omega) (by have := hl.l2; omega) (by have := hl.l2; omega) (by have := hl.l0; omega) (by have := hl.l2; omega) (by have := hl.l1; omega) (by have := hl.l3; omega) (by have := hl.l3; omega) (by have := hl.l4; omega) (by have := hl.l4; omega) (by have := hl.l5; omega) (by have := hl.l5; omega) (by have := hl.l3; omega) (by have := hl.l5; omega) (by have := hl.l4; omega) hk1 hk2 X0 hX0 X1 hX1 X2 hX2 X3 hX3 X4 hX4 X5 hX5 X6 hX6 X7 hX7 X8 hX8 X9 hX9 X10 hX10 X11 hX11 X12 hX12 X13 hX13 X14 hX14 X15 hX15 X16 hX16 X17 hX17 X18 hX18 X19 hX19 (by rw [sub_one_cast _ hpos]; exact i32_valid_nat _ (by omega)) (fun _ => hmc) (fun _ => hnc) fu
    have a3 := pexecM_scope mv fu _ _ _ r0 h0
    have tk : (⟨r0.ps.mem.take (gS P (pre ++ LCells inf n op qa qb x sp ne)).mem.length,
        r0.ps.bs.take (gS P (pre ++ LCells inf n op qa qb x sp ne)).bs.length⟩ : PS) = gS P (pre ++ LCells inf n op qa qb x sp (ne - 1)) := by
      rw [hp0]; exact scope_take P pre (LCells inf n op qa qb x sp ne) (LCells inf n op qa qb x sp (ne - 1)) [(⟨i32, (e : Int)⟩ : Cell), (⟨s64, inf⟩ : Cell), (⟨i32, (n : Int)⟩ : Cell), (⟨i32, (e : Int)⟩ : Cell), (⟨i32, (((2 * e + 1) : Nat) : Int)⟩ : Cell), (⟨i32, (((2 * e + 2) : Nat) : Int)⟩ : Cell), (⟨s64, Z1⟩ : Cell), (⟨s64, Z2⟩ : Cell), (⟨s64, Z3⟩ : Cell), (⟨s64, Z4⟩ : Cell), (⟨s64, Z5⟩ : Cell), (⟨s64, Z6⟩ : Cell), (⟨i32, X0⟩ : Cell), (⟨i32, X1⟩ : Cell), (⟨i32, X2⟩ : Cell), (⟨s64, X3⟩ : Cell), (⟨s64, X5⟩ : Cell), (⟨s64, X9⟩ : Cell), (⟨s64, X8⟩ : Cell), (⟨s64, Z7⟩ : Cell), (⟨s64, Z8⟩ : Cell), (⟨s64, Z9⟩ : Cell), (⟨s64, Z10⟩ : Cell), (⟨s64, Z11⟩ : Cell), (⟨s64, Z12⟩ : Cell), (⟨i32, X10⟩ : Cell), (⟨i32, X11⟩ : Cell), (⟨i32, X12⟩ : Cell), (⟨s64, X13⟩ : Cell), (⟨s64, X15⟩ : Cell), (⟨s64, X19⟩ : Cell), (⟨s64, X18⟩ : Cell)] (by rfl)
    rw [tk, hv0] at a3
    have a4 := seqM_some a3 hr0 (pexecM_skip mv fu (gS P (pre ++ LCells inf n op qa qb x sp (ne - 1))) (VVB (UC b e X3 X5 X9 X13 X15 X19)))
    refine ⟨_, a4, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · simp; omega
    · simp; omega

end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec

variable {SC : Nat}
theorem upd_all (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32)
    (P : List Cell) (inf : Int) (n op qa qb sp : Nat) (x : Int) (hinf : s64.valid inf = true)
    (hnM : n < M31) (hopM : op < M31) (hqaM : qa < M31) (hqbM : qb < M31) (hspM : sp < M31) (hx : s64.valid x = true)
    (L : Nat) (hLM : L < M31) :
    ∀ (E : List Nat) (b : BS) (ne : Nat) (H : Heap), EntRep b ne E → ValidOK b → CapS SC b L → (∀ e ∈ E, 2 * e + 2 < L) → ne ≤ L →
      SumsOK E H → HRel inf b H →
      ∃ b' : BS, ∃ F, F ≤ E.length + 1 ∧
        RunsU mv F P pre inf n op qa qb x b sp ne (gS P (pre ++ LCells inf n op qa qb x sp 0)) (VVB b') (E.length * 24794 + 4) (E.length * 6) ∧
        HRel inf b' (upPhase E H) ∧ ValidOK b' ∧ SameLen b b' ∧ b'.sk = b.sk ∧ b'.sl = b.sl ∧ b'.sr = b.sr := by
  intro E
  induction E with
  | nil =>
    intro b ne H hent hV hLens hE hne hS hH
    have h0 : ne = 0 := by have := hent.1; simp at this; omega
    subst h0
    refine ⟨b, 0 + 1, by simp, ?_, hH, hV, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    simpa using runsU_exit mv hnv 0 P pre inf n op qa qb x b sp
  | cons e E ih =>
    intro b ne H hent hV hLens hE hne hS hH
    have hne0 : 0 < ne := by have := hent.1; simp at this; omega
    have hS1 : SumOK H e := hS.1
    have hmc : s64.valid (b.mxc.getD (2 * e + 1) 0 + b.mxc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.1; rw [← a, ← c] at h1; exact h1
    have hnc : s64.valid (b.mnc.getD (2 * e + 1) 0 + b.mnc.getD (2 * e + 2) 0) = true := by
      have a := (hH (2 * e + 1)).1; have c := (hH (2 * e + 2)).1
      have h1 := hS1.2; rw [← a, ← c] at h1; exact h1
    obtain ⟨b1, hH1, hent1, hV1, hSL1, hsk1, hsl1, hsr1, hit⟩ :=
      iter_upd mv hnv pre hty hty32 b P inf n op qa qb sp ne x hinf hnM hopM hqaM hqbM hspM (by omega) hx L hV hLens hLM e E hent
        (hE e (by simp)) hne hmc hnc H hH
    obtain ⟨b2, F, hF, hrun, hH2, hV2, hSL2, hsk2, hsl2, hsr2⟩ :=
      ih b1 (ne - 1) (updateH H e) hent1 hV1 (Capacities.of_same hLens hSL1) (fun e' he' => hE e' (by simp [he'])) (by omega) hS.2 hH1
    refine ⟨b2, F + 1, by simp at hF ⊢; omega, ?_, ?_, hV2, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r1, h1, hret, hps, hvv, hc, hw⟩ := hit (F + 1)
      have := runsU_step mv hnv F P pre inf n op qa qb x b b1 sp ne (ne - 1) (by omega) hne0 r1 h1 hret hps hvv 24790 6 hc hw _ _ _ _ hrun
      refine runsU_weaken_p this ?_ ?_ <;> simp <;> omega
    · rw [upPhase_cons]; exact hH2
    · exact ⟨by rw [hSL2.l0, hSL1.l0], by rw [hSL2.l1, hSL1.l1], by rw [hSL2.l2, hSL1.l2], by rw [hSL2.l3, hSL1.l3],
        by rw [hSL2.l4, hSL1.l4], by rw [hSL2.l5, hSL1.l5], by rw [hSL2.l6, hSL1.l6], by rw [hSL2.l7, hSL1.l7],
        by rw [hSL2.l8, hSL1.l8], by rw [hSL2.l9, hSL1.l9], by rw [hSL2.l10, hSL1.l10], by rw [hSL2.l11, hSL1.l11],
        by rw [hSL2.l12, hSL1.l12], by rw [hSL2.l13, hSL1.l13], by rw [hSL2.l14, hSL1.l14], by rw [hSL2.leneq, hSL1.leneq]⟩
    · rw [hsk2, hsk1]
    · rw [hsl2, hsl1]
    · rw [hsr2, hsr1]


end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)

variable {SC : Nat}
theorem loop0_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (ne : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chminSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hstk : StkRep b 1 [⟨0, 0, n⟩]) (hent : EntRep b 0 []) (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L)
    (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ bf nef F, F ≤ 1 + nodesOf t ∧ RunsE mv F P pre inf n 0 qa qb x b 1 0 bf nef (nodesOf t * 117614 + 4) (nodesOf t * 47 + 0) ∧
      ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp0 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H' := by
  have key := frame0_all Ev hx (fun bf nef => ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp0 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H') t.height t (le_refl _) 1 4 0
  have := key 0 0 n ys b 1 0 [] [] H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh
    (by
      intro bK neK H' Enew hH' hst hen hV' hSL hStar _ hIn hSm _ hAg hlen'
      refine ⟨bK, neK, 1, le_refl _, ?_, H', Enew, hH', by simpa using hen, hV', hSL, hAg, hlen', hIn, by simpa using hStar, by simpa using hSm⟩
      exact runs_exit mv Ev.hnv 0 P pre inf n 0 qa qb x bK neK)
  exact this

end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec

variable {SC : Nat}
theorem apply0_exec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chminSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31)
:
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (ApplyOpCmd (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci 0, ci qa, ci qb, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P (pre ++ LCells inf n 0 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 ∧ r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0 := by
  have hL0 : 0 < L := by omega
  have hlk : 0 < b.sk.length := by have := hLens.lsk; omega
  have hll : 0 < b.sl.length := by have := hLens.lsl; omega
  have hlr : 0 < b.sr.length := by have := hLens.lsr; omega
  have hHI : HRel inf (initB b n) H := HRel_stable inf b (initB b n) H hH (fun i => ⟨rfl, rfl⟩) rfl
  have hlenI : LenOK (initB b n) t 0 0 n := LenOKs_of_eq (b := b) (b' := initB b n) rfl _ _ _ _ hlen
  have hSLI := initB_sameLen b n
  have hLensI := Capacities.of_same hLens hSLI
  have hVI := initB_valid b n Ev.hnM hV
  have hEntI : EntRep (initB b n) 0 [] := ⟨rfl, by intro j e h; simp at h⟩
  obtain ⟨bf, nef, F1, hF1, hRun, H', Enew, hHR', hEnt, hVf, hSLf, hAg, hlenE, hIn, hStar, hSm⟩ :=
    loop0_all Ev hx t ys (initB b n) 0 H hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initB_stk b n hlk hll hlr) hEntI hsp hne hlh
  have hLensf : CapS SC bf L := Capacities.of_same hLensI hSLf
  have hEL : ∀ e ∈ Enew, 2 * e + 2 < L := fun e he => InSks_lt t.skel 0 L e hidx (hIn e he)
  have hnefL : nef ≤ L := by have := hEnt.1; omega
  obtain ⟨bf2, F2, hF2, hRunU, hHR2, hV2, hSL2, -, -, -⟩ :=
    upd_all mv Ev.hnv pre Ev.hty Ev.hty32 P inf n 0 qa qb 0 x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM (by decide) Ev.hx L Ev.hLM
      Enew bf nef H' hEnt hVf hLensf hEL hnefL hSm hHR'
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hRunU
  have h1' := pexecM_mono mv _ _ _ r1 F1 F2 h1
  have h2' := pexecM_mono mv _ _ _ r2 F2 F1 h2
  rw [Nat.add_comm F2 F1] at h2'
  have h2'' : pexecM mv (F1 + F2) (ULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2'
  have hseq := seqM_some h1' hr1 (seqM_some h2'' hr2 (pexecM_skip mv (F1 + F2) r2.ps r2.vv))
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    ApInit_ch0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n 0 qa qb x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx hV.v11 hV.v12 hV.v13
      hlk hll hlr 1 rfl (F1 + F2) (.sequence (ALoop (mv.nv + pre.length)) (.sequence (ULoop (mv.nv + pre.length)) Sk))
      _ hseq (by simpa using hr2)
  have hlE : Enew.length ≤ innerOf t := hlenE
  refine ⟨bf2, upPhase Enew H', F1 + F2, r0, h0, hr0, ?_, ?_, ?_, ?_, hHR2, hV2, SameLen_trans hSLI (SameLen_trans hSLf hSL2), hAg⟩
  · rw [hp0]; exact hp2
  · rw [hv0]; exact hv2
  · have : r0.cost ≤ 2520 + (r1.cost + (r2.cost + 0)) := hc0
    have h3 : Enew.length * 24794 ≤ innerOf t * 24794 := Nat.mul_le_mul_right _ hlE
    omega
  · have : r0.wk ≤ 3 + (r1.wk + (r2.wk + 0)) := hw0
    have h3 : Enew.length * 6 ≤ innerOf t * 6 := Nat.mul_le_mul_right _ hlE
    omega


end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.BellmanFordExec

variable {SC : Nat}
theorem chmin_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chminSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_chmin.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 0 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0 ∧ bf.len = b.len := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := apply0_exec Ev hx t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hne hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_chmin
  have hWf : Wf (W6 0 T) = true := hbT ▸ wf_chmin
  have hNb : Nb (W6 0 T) ≤ 335 := hbT ▸ nb_chmin
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap_gen mv hnv P (VVB b) inf x n qa qb 0 Ev.hinf Ev.hx Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim (by decide +kernel) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 0 T) = true := hbT ▸ (by decide +kernel : noWr 6 SegmentTreeBeats_chmin.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', F', r', by rw [hbT]; exact g1, g2, g3, g4', g5, g6, g7, q1, q2, q3, q4, hlen⟩


end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec (M31 cs)

variable {SC : Nat}
theorem chmin_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H) (hsafe : chminSafe qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_chmin.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 0 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRepS n L SC (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    chmin_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsMin qa qb x) (capMaxBT x) (skel_capMaxBT x) (LeafOK_capMaxBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [chminBT_eq]
  have hinv := Inv.chmin qa qb x hx.1 t 0 n ys R.inv R.shape hsafe
  rw [chminBT_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRepS.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen


end Proofs.BeatsSeparate
