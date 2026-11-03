import Proofs.BeatsCapChmin

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
theorem Env_withX {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) (x' : Int) (hx' : s64.valid x' = true) : EnvK SC mv pre P inf n op qa qb x' L :=
  { Ev with hx := hx' }

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
theorem cstep_stop {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOKK SC b inf sp 0 L W0 W1 W2 S [] H) (hstop : qb ≤ W1 ∨ W2 ≤ qa) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_stop mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hstop H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_whole0 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOKK SC b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hcov : qa ≤ W1 ∧ W2 ≤ qb) (hop0 : op = 0) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp (if x < b.mxv.getD W0 0 then b.mxv.getD W0 0 else x) b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_whole0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hnot hcov hop0 H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_whole1 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOKK SC b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hcov : qa ≤ W1 ∧ W2 ≤ qb) (hop1 : op = 1) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp (if b.mnv.getD W0 0 < x then b.mnv.getD W0 0 else x) b' (sp - 1) ∧ HRel inf b' H ∧ StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_whole1 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent hnot hcov hop1 H St.hH
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_down_set {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOKK SC b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hnotc : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) (hmode : b.lval.getD W0 0 ≠ inf)
    (hlenL : b.len.getD (2 * W0 + 1) 0 = ((((W1 + W2) / 2) - W1 : Nat) : Int))
    (hlenR : b.len.getD (2 * W0 + 2) 0 = ((W2 - ((W1 + W2) / 2) : Nat) : Int)) (hint : b.len.getD W0 0 ≠ 1) :
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1 + 2) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_down_set mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent
    hnot hnotc hne1 hsp2 Ev.hinfI hmode hlenL hlenR hmode H St.hH hint
  exact ⟨b', h6, h1, h2, h4, h5⟩

theorem cstep_down_add {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap}
    (St : StateOKK SC b inf sp 0 L W0 W1 W2 S [] H) (hnot : ¬ (qb ≤ W1 ∨ W2 ≤ qa)) (hnotc : ¬ (qa ≤ W1 ∧ W2 ≤ qb)) (hmode : b.lval.getD W0 0 = inf)
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
    ∃ b', IterC mv P pre inf n op qa qb x b sp x b' (sp - 1 + 2) ∧
      HRel inf b' (pushH H W0 ((((W1 + W2) / 2 - W1 : Nat)) : Int) ((W2 - (W1 + W2) / 2 : Nat) : Int)) ∧
      StkRep b' (sp - 1 + 2) (⟨2 * W0 + 1, W1, (W1 + W2) / 2⟩ :: ⟨2 * W0 + 2, (W1 + W2) / 2, W2⟩ :: S) ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp 0 x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  have hne1 : 0 + 1 < M31 := by have := St.hneL; have := Ev.hLM; omega
  have hsp2 : sp - 1 + 2 < M31 := by have := St.hspL; have := Ev.hKM; omega
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := citer_down_add mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp 0 x S [] W0 W1 W2 C St.hstk St.hent
    hnot hnotc hne1 hsp2 Ev.hinfI hmode hlenL hlenR hZ3 hZ5 hlv1 hlv2 H St.hH hint hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9 hS10 hS11
  exact ⟨b', h6, h1, h2, h4, h5⟩

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
theorem calc_stateOK {b : BS} {inf : Int} {sp L k lo hi : Nat} {S : List Fr} {H : Heap} {t : BT}
    (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t k L) (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S))
    (hH : HRel inf b H) (hsp : sp + t.height + 2 ≤ SC) (hlh : lo ≤ hi ∧ 2 * hi < M31) :
    StateOKK SC b inf sp 0 L k lo hi S [] H := by
  have hkroom : 2*k+2 < L := by
    cases t with
    | leaf nd => exact hidx
    | node nd tg l r => exact hidx.1
  refine ⟨hV, hLens, ?_, ?_, by omega, by omega, by have := hlh.1; have := hlh.2; omega, hstk, ⟨rfl, by intro j e h; simp at h⟩, hH⟩
  · cases t with
    | leaf nd => exact hidx
    | node nd tg l r => exact hidx.1
  · have := hstk.1
    simp at this
    omega

/-- The data of one of the two queries (maximum / minimum). -/
def WholeStep (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb L : Nat) (sp_ : CSpec qa qb) : Prop :=
  ∀ (x : Int), EnvK SC mv pre P inf n op qa qb x L → ∀ {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap},
    StateOKK SC b inf sp 0 L W0 W1 W2 S [] H → ¬ (qb ≤ W1 ∨ W2 ≤ qa) → (qa ≤ W1 ∧ W2 ≤ qb) →
    ∃ b', IterC mv P pre inf n op qa qb x b sp (sp_.comb x (sp_.val (decNd b W0))) b' (sp - 1) ∧ HRel inf b' H ∧
      StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b'

def FrameCI (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (L : Nat) (sp_ : CSpec qa qb) (Fin : BS → Int → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → calcSafe qa qb t lo hi →
    HRel inf b H → ValidOK b → CapS SC b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → sp + t.height + 2 ≤ SC → (lo ≤ hi ∧ 2 * hi < M31) → s64.valid r = true → sp_.RB r →
    (∀ (bK : BS) (H' : Heap) (rK : Int), HRel inf bK H' → StkRep bK (sp - 1) S → ValidOK bK → SameLen b bK →
      Star (stepC qa qb sp_) ⟨H, ⟨k, lo, hi⟩ :: S, r⟩ ⟨H', S, rK⟩ → (∀ j, ¬ descN k j → H' j = H j) →
      Agree H' (sp_.calcF t lo hi).1 k → rK = sp_.comb r (sp_.calcF t lo hi).2 → s64.valid rK = true →
      ∃ bf xf F, F ≤ F0 ∧ RunsCE mv F P pre inf n op qa qb rK bK (sp - 1) bf xf C0 Wc ∧ Fin bf xf) →
    ∃ bf xf F, F ≤ F0 + nodesOf t ∧ RunsCE mv F P pre inf n op qa qb r b sp bf xf (nodesOf t * 72254 + C0) (nodesOf t * 24 + Wc) ∧ Fin bf xf

def FrameCP (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (L : Nat) (sp_ : CSpec qa qb) (Fin : BS → Int → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int),
    FrameCI SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t k lo hi ys b sp S H r


theorem frameC_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep SC mv pre P inf n op qa qb L sp_) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int)
    (hnd : clsRange qa qb t.nd lo hi ≠ Cls.down) : FrameCI SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t k lo hi ys b sp S H r := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hsp hlh hvr hRB K
  have Ev := Env_withX Ev0 r hvr
  have St := calc_stateOK hV hLens hidx hstk hH hsp hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev0.hKM; omega
  have hn1 : 1 ≤ nodesOf t := by cases t <;> (show 1 ≤ nodesS _; unfold nodesS; first | omega | (split <;> omega))
  have hcost : 72254 + C0 ≤ nodesOf t * 72254 + C0 := by have := Nat.mul_le_mul_right 72254 hn1; omega
  have hwk : 24 + Wc ≤ nodesOf t * 24 + Wc := by have := Nat.mul_le_mul_right 24 hn1; omega
  cases hc : clsRange qa qb t.nd lo hi with
  | down => exact absurd hc hnd
  | stop =>
    have hs := clsR_stop qa qb t.nd lo hi hc
    obtain ⟨b', hit, h1, h2, h4, h5⟩ := cstep_stop Ev St hs
    have hcalc := sp_.hstop t lo hi hc
    have hK := K b' H r h1 h2 h4 h5 (Star.one (by simp [stepCalc, hroot, hc])) (fun _ _ => rfl)
      (by rw [hcalc]; exact hag) (by rw [hcalc]; exact (sp_.hid r hRB).symm) hvr
    obtain ⟨bf, xf, F, hFle, hr, hF⟩ := hK
    have hr' := runsC_of_iter mv Ev0.hnv P pre inf n op qa qb r r b b' sp (sp - 1) hspM hsp0 hit F bf xf C0 Wc hr
    exact ⟨bf, xf, F + 1, by omega, runsC_weaken hr' hcost hwk, hF⟩
  | whole =>
    obtain ⟨hn, hcov⟩ := clsR_whole qa qb t.nd lo hi hc
    obtain ⟨b', hit, h1, h2, h4, h5⟩ := hW r Ev St hn hcov
    have hcalc := sp_.hwhole t lo hi hc
    have hxv : s64.valid (sp_.comb r (sp_.val (decNd b k))) = true :=
      sp_.hvalid r _ hvr (sp_.hvalNd b k hV (by have := hLens.l0; have := St.hk; omega) (by have := hLens.l3; have := St.hk; omega))
    have hK := K b' H (sp_.comb r (sp_.val (decNd b k))) h1 h2 h4 h5 (Star.one (by simp [stepCalc, hroot, hc, hnd0])) (fun _ _ => rfl)
      (by rw [hcalc]; exact hag) (by rw [hcalc]; show _ = sp_.comb r (sp_.val t.nd); rw [← hnd0]) hxv
    obtain ⟨bf, xf, F, hFle, hr, hF⟩ := hK
    have hr' := runsC_of_iter mv Ev0.hnv P pre inf n op qa qb r _ b b' sp (sp - 1) hspM hsp0 hit F bf xf C0 Wc hr
    exact ⟨bf, xf, F + 1, by omega, runsC_weaken hr' hcost hwk, hF⟩


theorem frameC_down_rec {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameCP SC mv pre P inf n op qa qb L sp_ Fin (F0 + nodesOf r) (nodesOf r * 72254 + C0) (nodesOf r * 24 + Wc) (applyTag tg nd l))
    (ihr : FrameCP SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (xl xr : List Int) (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (rr : Int)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hsafel : calcSafe qa qb (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : calcSafe qa qb (applyTag tg nd r) ((lo + hi) / 2) hi)
    (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S))
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ SC) (hlh : lo ≤ hi ∧ 2 * hi < M31) (hvr : s64.valid rr = true) (hRB : sp_.RB rr)
    (hcd : clsRange qa qb nd lo hi = Cls.down) (hroot : (H k).1 = nd)
    (b1 : BS) (hit : IterC mv P pre inf n op qa qb rr b sp rr b1 (sp - 1 + 2))
    (hHR1 : HRel inf b1 (pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int)))
    (hstk1 : StkRep b1 (sp - 1 + 2) (⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S))
    (hV1 : ValidOK b1) (hS1 : SameLen b b1)
    (K : ∀ (bK : BS) (H' : Heap) (rK : Int), HRel inf bK H' → StkRep bK (sp - 1) S → ValidOK bK → SameLen b bK →
      Star (stepC qa qb sp_) ⟨H, ⟨k, lo, hi⟩ :: S, rr⟩ ⟨H', S, rK⟩ → (∀ j, ¬ descN k j → H' j = H j) →
      Agree H' (sp_.calcF (.node nd tg l r) lo hi).1 k → rK = sp_.comb rr (sp_.calcF (.node nd tg l r) lo hi).2 → s64.valid rK = true →
      ∃ bf xf F, F ≤ F0 ∧ RunsCE mv F P pre inf n op qa qb rK bK (sp - 1) bf xf C0 Wc ∧ Fin bf xf) :
    ∃ bf xf F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsCE mv F P pre inf n op qa qb rr b sp bf xf (nodesOf (.node nd tg l r) * 72254 + C0) (nodesOf (.node nd tg l r) * 24 + Wc) ∧
      Fin bf xf := by
  obtain ⟨hlo, hshl, hshr⟩ := hsh
  obtain ⟨hlfl, hlfr⟩ := hlf
  have hag2 := (agree_node H nd tg l r k).mp hag
  have hlsize : ((lo + hi) / 2 - lo : Nat) = l.size := by rw [BT.size_skel, hshl.size]
  have hrsize : (hi - (lo + hi) / 2 : Nat) = r.size := by rw [BT.size_skel, hshr.size]
  have hpush := agree_pushBT H nd tg l r k hag
  rw [← hlsize, ← hrsize] at hpush
  simp only [pushBT] at hpush
  have hp2 := (agree_node _ nd noTag _ _ k).mp hpush
  have hstep : stepCalc (clsRange qa qb) sp_.val sp_.comb ⟨H, ⟨k, lo, hi⟩ :: S, rr⟩ =
      ⟨pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int),
        ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, rr⟩ := by
    simp [stepCalc, hroot, hcd]
  obtain ⟨H0, hH0⟩ : ∃ H0, H0 = pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int) := ⟨_, rfl⟩
  rw [← hH0] at hstep hp2 hpush hHR1
  have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
  have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
  have hht : BT.height (.node nd tg l r) = max l.height r.height + 1 := rfl
  have hml : l.height ≤ max l.height r.height := Nat.le_max_left _ _
  have hmr : r.height ≤ max l.height r.height := Nat.le_max_right _ _
  have hsp0 : 0 < sp := by have := hstk.1; simp at this; omega
  have hnod : nodesOf (.node nd tg l r) = nodesOf l + nodesOf r + 1 := rfl
  have hLens1 : CapS SC b1 L := Capacities.of_same hLens hS1
  have hlen1 : b1.len = b.len := hS1.leneq
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
  have hhl := height_applyTag tg nd l
  have hhr := height_applyTag tg nd r
  have hres := ihl (2 * k + 1) lo ((lo + hi) / 2) xl b1 (sp - 1 + 2) (⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S) H0 rr
    hp2.2.1 hshl' (LeafOK_applyTag tg nd l hlfl) hinvl hsafel hHR1 hV1 hLens1 hidxl hlenL' hstk1
    (by rw [hhl]; omega) (by have := hlh.1; have := hlh.2; omega) hvr hRB (by
      intro bK H1 rK1 hHR hS hVK hSL hst1 hfr1 hag1 hrK1 hvK1
      have e : sp - 1 + 2 - 1 = sp := by omega
      rw [e] at hS
      have hLensK : CapS SC bK L := Capacities.of_same hLens1 hSL
      have hlenK : bK.len = b.len := hSL.leneq.trans hlen1
      have hag_r : Agree H1 (applyTag tg nd r) (2 * k + 2) :=
        agree_of_eqOn hp2.2.2 (fun j hj => (hfr1 j (fun hd => descN_disjoint k j hd hj)).symm)
      have hlenR'' : LenOK bK (applyTag tg nd r) (2 * k + 2) ((lo + hi) / 2) hi := by
        show LenOKs bK (applyTag tg nd r).skel _ _ _
        rw [skel_applyTag]; exact LenOKs_of_eq hlenK _ _ _ _ hlen.2.2
      have hRB1 : sp_.RB rK1 := by rw [hrK1]; exact sp_.hRB _ _ hRB
      have hKres := ihr (2 * k + 2) ((lo + hi) / 2) hi xr bK sp S H1 rK1 hag_r hshr'
        (LeafOK_applyTag tg nd r hlfr) hinvr hsafer hHR hVK hLensK hidxr hlenR'' hS
        (by rw [hhr]; omega) (by have := hlh.1; have := hlh.2; omega) hvK1 hRB1 (by
          intro bK2 H2 rK2 hHR2 hS2 hV2 hSL2 hst2 hfr2 hag2' hrK2 hvK2
          have hfull : Star (stepC qa qb sp_) ⟨H, ⟨k, lo, hi⟩ :: S, rr⟩ ⟨H2, S, rK2⟩ :=
            Star.trans (Star.one hstep.symm) (Star.trans hst1 hst2)
          have hjframe : ∀ j, ¬ descN k j → H2 j = H j := by
            intro j hj
            have hjl : ¬ descN (2 * k + 1) j := fun hd => hj (descN_child k j hd)
            have hjr : ¬ descN (2 * k + 2) j := fun hd => hj (descN_child2 k j hd)
            have hjk : j ≠ k := fun e => hj (e ▸ descN_self _)
            have hj1 : j ≠ 2 * k + 1 := fun e => hj (descN_child k j (e ▸ descN_self _))
            have hj2 : j ≠ 2 * k + 2 := fun e => hj (descN_child2 k j (e ▸ descN_self _))
            rw [hfr2 j hjr, hfr1 j hjl, hH0]
            unfold pushH
            rw [Heap.set_ne _ _ _ _ hjk, Heap.set_ne _ _ _ _ hj2, Heap.set_ne _ _ _ _ hj1]
          have hagA : Agree H2 (sp_.calcF (.node nd tg l r) lo hi).1 k := by
            rw [sp_.hdown nd tg l r lo hi hcd]
            have hlnot : ∀ j, descN (2 * k + 1) j → ¬ descN (2 * k + 2) j := fun j h1 h2 => descN_disjoint k j h1 h2
            have hagL := agree_of_eqOn hag1 (fun j hj => (hfr2 j (hlnot j hj)).symm)
            have hkk : H2 k = (nd, noTag) := by
              have n1 : ¬ descN (2 * k + 1) k := fun hd => by have := descN_ge _ _ hd; omega
              have n2 : ¬ descN (2 * k + 2) k := fun hd => by have := descN_ge _ _ hd; omega
              rw [hfr2 k n2, hfr1 k n1]
              exact hp2.1
            exact (agree_node _ nd noTag _ _ k).mpr ⟨hkk, hagL, hag2'⟩
          have hrA : rK2 = sp_.comb rr (sp_.calcF (.node nd tg l r) lo hi).2 := by
            rw [sp_.hdown nd tg l r lo hi hcd]
            show rK2 = sp_.comb rr (sp_.comb _ _)
            rw [hrK2, hrK1, sp_.hassoc]
          exact K bK2 H2 rK2 hHR2 hS2 hV2 (SameLen_trans hS1 (SameLen_trans hSL hSL2)) hfull hjframe hagA hrA hvK2)
      rw [hnr] at hKres
      rw [e]; exact hKres)
  obtain ⟨bf, xf, F, hFle, hr, hF⟩ := hres
  rw [hnl] at hFle hr
  have hspM : sp < M31 := by have := Ev0.hKM; omega
  have hr' := runsC_of_iter mv Ev0.hnv P pre inf n op qa qb rr rr b b1 sp (sp - 1 + 2) hspM hsp0 hit F bf xf _ _ hr
  refine ⟨bf, xf, F + 1, by rw [hnod]; omega, runsC_weaken hr' (by rw [hnod]; omega) (by rw [hnod]; omega), hF⟩


theorem frameC_down {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameCP SC mv pre P inf n op qa qb L sp_ Fin (F0 + nodesOf r) (nodesOf r * 72254 + C0) (nodesOf r * 24 + Wc) (applyTag tg nd l))
    (ihr : FrameCP SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (applyTag tg nd r))
    :
    ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (rr : Int),
      clsRange qa qb nd lo hi = Cls.down →
      FrameCI SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp S H rr := by
  intro k lo hi ys b sp S H rr hcd
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hsp hlh hvr hRB K
  have Ev := Env_withX Ev0 rr hvr
  have St := calc_stateOK hV hLens hidx hstk hH hsp hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH _ k lo hi hag hsh hlen
  have hnd' : decNd b k = nd := hnd0
  have hroot : (H k).1 = nd := by have := hH k; rw [← this.1]; exact hnd'
  obtain ⟨hn, hnc⟩ := clsR_down qa qb nd lo hi hcd
  obtain ⟨hps, hsl, hsr⟩ := calcSafe_down qa qb nd tg l r lo hi hcd hsafe
  obtain ⟨xl, xr, hinvl, hinvr, hys⟩ := Inv.push_parts hinv hps
  cases htg : tg.lval with
  | none =>
    have F := down_add_facts inf Ev0.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen hps htg
    obtain ⟨b1, hit, h1, h2, h3, h4⟩ := cstep_down_add Ev St hn hnc F.hmode F.hlenL F.hlenR F.hZ3 F.hZ5
      F.hlv1 F.hlv2 F.hint F.hS0 F.hS1 F.hS2 F.hS3 F.hS4 F.hS5 F.hS6 F.hS7 F.hS8 F.hS9 F.hS10 F.hS11
    exact frameC_down_rec Ev0 sp_ Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp S H rr hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hsp hlh hvr hRB hcd hroot b1 hit h1 h2 h3 h4 K
  | some v =>
    have F := down_set_facts inf Ev0.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen v htg
    obtain ⟨b1, hit, h1, h2, h3, h4⟩ := cstep_down_set Ev St hn hnc F.hmode F.hlenL F.hlenR F.hint
    exact frameC_down_rec Ev0 sp_ Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp S H rr hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hsp hlh hvr hRB hcd hroot b1 hit h1 h2 h3 h4 K

theorem frameC_all {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep SC mv pre P inf n op qa qb L sp_) (Fin : BS → Int → Prop) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ F0 C0 Wc, FrameCP SC mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t := by
  intro h
  induction h with
  | zero =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp S H r hag hsh
      exact frameC_nodown Ev0 sp_ hW Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp S H r (clsRange_leaf qa qb nd lo hi hsh) hag hsh
    | node nd tg l r => simp [BT.height] at ht
  | succ h ih =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp S H r hag hsh
      exact frameC_nodown Ev0 sp_ hW Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp S H r (clsRange_leaf qa qb nd lo hi hsh) hag hsh
    | node nd tg l r =>
      intro k lo hi ys b sp S H rr
      by_cases hcd : clsRange qa qb nd lo hi = Cls.down
      · have hl : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_left l.height r.height; simp [BT.height] at ht; omega
        have hr : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_right l.height r.height; simp [BT.height] at ht; omega
        exact frameC_down Ev0 sp_ Fin F0 C0 Wc nd tg l r (ih _ hl _ _ _) (ih _ hr _ _ _) k lo hi ys b sp S H rr hcd
      · exact frameC_nodown Ev0 sp_ hW Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp S H rr hcd

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
theorem calc_exec {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep SC mv pre P inf n op qa qb L sp_)
    (hinit : (if (op : Int) = 1 then inf else -inf) = sp_.idv) (hvidv : s64.valid sp_.idv = true) (hRB0 : sp_.RB sp_.idv)
    (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F (CalcOpCmd (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb])) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P (pre ++ CCells inf n op qa qb xf 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 := by
  have hL0 : 0 < L := by
    cases t with
    | leaf nd => have hh : 2 < L := hidx; omega
    | node nd tg l r => have hh : 2 < L := hidx.1; omega
  have hlk : 0 < b.sk.length := by have := hLens.lsk; omega
  have hll : 0 < b.sl.length := by have := hLens.lsl; omega
  have hlr : 0 < b.sr.length := by have := hLens.lsr; omega
  have hHI : HRel inf (initC b n) H := HRel_stable inf b (initC b n) H hH (fun i => ⟨rfl, rfl⟩) rfl
  have hlenI : LenOK (initC b n) t 0 0 n := LenOKs_of_eq (b := b) (b' := initC b n) rfl _ _ _ _ hlen
  have hSLI := initC_sameLen b n
  have hLensI := Capacities.of_same hLens hSLI
  have hVI := initC_valid b n Ev0.hnM hV
  have key := frameC_all Ev0 sp_ hW (fun bf xf => ∃ H' : Heap, HRel inf bf H' ∧ ValidOK bf ∧ SameLen (initC b n) bf ∧
      Agree H' (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 ∧ s64.valid xf = true) t.height t (le_refl _) 1 4 0
  obtain ⟨bf, xf, F, hF, hRun, H', hHR', hVf, hSLf, hAg, hxf, hvf⟩ :=
    key 0 0 n ys (initC b n) 1 [] H sp_.idv hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initC_stk b n hlk hll hlr) hsp hlh hvidv hRB0
      (by
        intro bK H' rK hHR hS hV' hSL hst hfr hAg hrK hvK
        exact ⟨bK, rK, 1, le_refl _, runsC_exit mv Ev0.hnv 0 P pre inf n op qa qb rK bK, H', hHR, hV', hSL, hAg, hrK, hvK⟩)
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  have hvret : vdenM mv r1.vv (penvN mv.nv r1.ps) (.variable s64 (mv.nv + pre.length + 5)) = some xf := by
    rw [hp1]
    exact den_cellvar_t mv P _ s64 (pre.length + 5) _ (by omega) xf (cell_at0 pre (CCells inf n op qa qb xf 0) 5 (cs xf) rfl) hvf r1.vv
  have hr2 := pstmtM_ret_ok mv r1.ps r1.vv _ xf hvret
  have hex2 := seqM_ret (b := Sk) (fu := F) ((pexecM_prim mv F _ r1.ps r1.vv).trans hr2) rfl
  have hseq := seqM_some h1 hr1 hex2
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    CInit_ch0r mv Ev0.hnv pre Ev0.hty Ev0.hty32 (initC b n |> fun _ => b) P inf n op qa qb 0 Ev0.hinf Ev0.hnM Ev0.hopM Ev0.hqaM Ev0.hqbM Ev0.hx hV.v11 hV.v12 hV.v13
      hlk hll hlr sp_.idv hinit.symm 1 rfl Ev0.hninf F
      (.sequence (CLoop (mv.nv + pre.length)) (.sequence (.primitive (.ret (.variable s64 (mv.nv + pre.length + 5)))) Sk))
      _ hseq (some xf) rfl
  refine ⟨bf, H', xf, F, r0, h0, hr0, ?_, ?_, ?_, ?_, hHR', hVf, SameLen_trans hSLI hSLf, hAg, hxf⟩
  · rw [hp0]; exact hp1
  · rw [hv0]; exact hv1
  · have : r0.cost ≤ 2940 + (r1.cost + (vwp (.variable s64 (mv.nv + pre.length + 5))).1 + 1) := by
      have := hc0; simp at this ⊢; omega
    simp [vwp, NExpr.nodes] at this ⊢; omega
  · have := hw0; simp at this ⊢; omega

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
open Proofs.VectorSumCall (conv_signed)

variable {SC : Nat}
theorem calc_exec2 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : EnvK SC mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep SC mv pre P inf n op qa qb L sp_)
    (hinit : (if (op : Int) = 1 then inf else -inf) = sp_.idv) (hvidv : s64.valid sp_.idv = true) (hRB0 : sp_.RB sp_.idv)
    (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F (CalcOpCmd2 (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb])) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf]) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 ∧ s64.valid xf = true := by
  have hL0 : 0 < L := by
    cases t with
    | leaf nd => have hh : 2 < L := hidx; omega
    | node nd tg l r => have hh : 2 < L := hidx.1; omega
  have hlk : 0 < b.sk.length := by have := hLens.lsk; omega
  have hll : 0 < b.sl.length := by have := hLens.lsl; omega
  have hlr : 0 < b.sr.length := by have := hLens.lsr; omega
  have hHI : HRel inf (initC b n) H := HRel_stable inf b (initC b n) H hH (fun i => ⟨rfl, rfl⟩) rfl
  have hlenI : LenOK (initC b n) t 0 0 n := LenOKs_of_eq (b := b) (b' := initC b n) rfl _ _ _ _ hlen
  have hSLI := initC_sameLen b n
  have hLensI := Capacities.of_same hLens hSLI
  have hVI := initC_valid b n Ev0.hnM hV
  have key := frameC_all Ev0 sp_ hW (fun bf xf => ∃ H' : Heap, HRel inf bf H' ∧ ValidOK bf ∧ SameLen (initC b n) bf ∧
      Agree H' (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 ∧ s64.valid xf = true) t.height t (le_refl _) 1 4 0
  obtain ⟨bf, xf, F, hF, hRun, H', hHR', hVf, hSLf, hAg, hxf, hvf⟩ :=
    key 0 0 n ys (initC b n) 1 [] H sp_.idv hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initC_stk b n hlk hll hlr) hsp hlh hvidv hRB0
      (by
        intro bK H' rK hHR hS hV' hSL hst hfr hAg hrK hvK
        exact ⟨bK, rK, 1, le_refl _, runsC_exit mv Ev0.hnv 0 P pre inf n op qa qb rK bK, H', hHR, hV', hSL, hAg, hrK, hvK⟩)
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  have hvret : vdenM mv r1.vv (penvN mv.nv r1.ps) (.variable s64 (mv.nv + pre.length + 5)) = some xf := by
    rw [hp1]
    exact den_cellvar_t mv P _ s64 (pre.length + 5) _ (by omega) xf (cell_at0 pre (CCells inf n op qa qb xf 0) 5 (cs xf) rfl) hvf r1.vv
  have hd := gSM_decl mv P (pre ++ CCells inf n op qa qb xf 0) r1.vv s64 (.variable s64 (mv.nv + pre.length + 5)) xf xf
    (by rw [← hp1]; exact hvret) (conv_signed s64 rfl rfl _ hvf)
  rw [← hp1] at hd
  have hd' := (pexecM_prim mv F (.declare s64 true (.variable s64 (mv.nv + pre.length + 5))) r1.ps r1.vv).trans hd
  have hvret2 : vdenM mv r1.vv (penvN mv.nv (gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf]))) (.variable s64 (mv.nv + pre.length + 7)) = some xf := by
    rw [List.append_assoc]
    exact den_cellvar_t mv P _ s64 (pre.length + 7) (mv.nv + pre.length + 7) (by omega) xf (cell_at0 pre (CCells inf n op qa qb xf 0 ++ [cs xf]) 7 (cs xf) rfl) hvf r1.vv
  have hr2 := pstmtM_ret_ok mv (gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf])) r1.vv _ xf hvret2
  have hex2 := seqM_ret (b := Sk) (fu := F) ((pexecM_prim mv F _ _ r1.vv).trans hr2) rfl
  have hex3 := seqM_some hd' rfl hex2
  have hseq := seqM_some h1 hr1 hex3
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    CInit_ch0r mv Ev0.hnv pre Ev0.hty Ev0.hty32 (initC b n |> fun _ => b) P inf n op qa qb 0 Ev0.hinf Ev0.hnM Ev0.hopM Ev0.hqaM Ev0.hqbM Ev0.hx hV.v11 hV.v12 hV.v13
      hlk hll hlr sp_.idv hinit.symm 1 rfl Ev0.hninf F
      (.sequence (CLoop (mv.nv + pre.length)) (.sequence (.primitive (.declare s64 true (.variable s64 (mv.nv + pre.length + 5)))) (.sequence (.primitive (.ret (.variable s64 (mv.nv + pre.length + 7)))) Sk)))
      _ hseq (some xf) rfl
  refine ⟨bf, H', xf, F, r0, h0, hr0, ?_, ?_, ?_, ?_, hHR', hVf, SameLen_trans hSLI hSLf, hAg, hxf, hvf⟩
  · rw [hp0]
  · rw [hv0]; exact hv1
  · have := hc0; simp [vwp, NExpr.nodes] at this ⊢; omega
  · have := hw0; simp at this ⊢; omega

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
theorem wholeStep_max {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (hop : op = 0) :
    WholeStep SC mv pre P inf n op qa qb L (specMax qa qb) := by
  intro x Ev b sp W0 W1 W2 S H St hn hc
  obtain ⟨b', hit, h1, h2, h3, h4⟩ := cstep_whole0 Ev St hn hc hop
  refine ⟨b', ?_, h1, h2, h3, h4⟩
  have e : (if x < b.mxv.getD W0 0 then b.mxv.getD W0 0 else x) = max x (b.mxv.getD W0 0) := by
    by_cases h : x < b.mxv.getD W0 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [e] at hit; exact hit

theorem wholeStep_min {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (hop : op = 1) :
    WholeStep SC mv pre P inf n op qa qb L (specMin qa qb) := by
  intro x Ev b sp W0 W1 W2 S H St hn hc
  obtain ⟨b', hit, h1, h2, h3, h4⟩ := cstep_whole1 Ev St hn hc hop
  refine ⟨b', ?_, h1, h2, h3, h4⟩
  have e : (if b.mnv.getD W0 0 < x then b.mnv.getD W0 0 else x) = min x (b.mnv.getD W0 0) := by
    by_cases h : b.mnv.getD W0 0 < x
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [e] at hit; exact hit

end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)

variable {SC : Nat}
theorem calc_max_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb] P inf n 0 qa qb 0 L) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_max.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 0 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMax qa qb).calcF t 0 n).1 0 ∧
      xf = (specMax qa qb).comb (specMax qa qb).idv ((specMax qa qb).calcF t 0 n).2 ∧ bf.len = b.len ∧ s64.valid xf = true := by
  have hI := Ev.hinfI
  have hidv : (if ((0 : Nat) : Int) = 1 then inf else -inf) = (specMax qa qb).idv := by
    rw [hI]; simp [specMax]
  have hv : s64.valid (specMax qa qb).idv = true := by
    simp only [specMax]; first | exact (hI ▸ Ev.hninf) | (rw [← hI]; exact Ev.hinf)
  have hrb : (specMax qa qb).RB (specMax qa qb).idv := by simp [specMax]
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    calc_exec2 Ev (specMax qa qb) (wholeStep_max rfl) hidv hv hrb t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_calc_max
  have hWf : Wf (W5 0 T) = true := hbT ▸ wf_calc_max
  have hNb : Nb (W5 0 T) ≤ 400 := hbT ▸ nb_calc_max
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap5_gen mv hnv P (VVB b) inf n qa qb 0 Ev.hinf Ev.hnM Ev.hqaM Ev.hqbM (by decide +kernel)
    T hsim na_calc hWf hNb _ _ xf (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMax qa qb).calcF t 0 n).1 0) (CCells inf n 0 qa qb xf 0 ++ [cs xf])
    ⟨F, r, by simpa using h1, h2, by rw [h3]; simp, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W5 0 T) = true := hbT ▸ (by decide +kernel : noWr 6 SegmentTreeBeats_calc_max.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', xf, F', r', by rw [hbT]; exact g1, g2, g3, g4', by omega, g6, by omega, q1, q2, q3, q4, h11, hlen, h12⟩

end Proofs.BeatsSeparate

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)

variable {SC : Nat}
theorem calc_min_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb] P inf n 1 qa qb 0 L) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_min.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 1 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMin qa qb).calcF t 0 n).1 0 ∧
      xf = (specMin qa qb).comb (specMin qa qb).idv ((specMin qa qb).calcF t 0 n).2 ∧ bf.len = b.len ∧ s64.valid xf = true := by
  have hI := Ev.hinfI
  have hidv : (if ((1 : Nat) : Int) = 1 then inf else -inf) = (specMin qa qb).idv := by
    rw [hI]; simp [specMin]
  have hv : s64.valid (specMin qa qb).idv = true := by
    simp only [specMin]; first | exact (hI ▸ Ev.hninf) | (rw [← hI]; exact Ev.hinf)
  have hrb : (specMin qa qb).RB (specMin qa qb).idv := by simp [specMin]
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    calc_exec2 Ev (specMin qa qb) (wholeStep_min rfl) hidv hv hrb t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_calc_min
  have hWf : Wf (W5 1 T) = true := hbT ▸ wf_calc_min
  have hNb : Nb (W5 1 T) ≤ 400 := hbT ▸ nb_calc_min
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap5_gen mv hnv P (VVB b) inf n qa qb 1 Ev.hinf Ev.hnM Ev.hqaM Ev.hqbM (by decide +kernel)
    T hsim na_calc hWf hNb _ _ xf (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMin qa qb).calcF t 0 n).1 0) (CCells inf n 1 qa qb xf 0 ++ [cs xf])
    ⟨F, r, by simpa using h1, h2, by rw [h3]; simp, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W5 1 T) = true := hbT ▸ (by decide +kernel : noWr 6 SegmentTreeBeats_calc_min.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', xf, F', r', by rw [hbT]; exact g1, g2, g3, g4', by omega, g6, by omega, q1, q2, q3, q4, h11, hlen, h12⟩

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
theorem calc_max_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15) (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb] P inf n 0 qa qb 0 L)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H) (hsafe : calcSafe qa qb t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_max.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 0 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      xf = max (-INF) (rangeMaxOf 0 qa qb ys) ∧ BRepS n L SC ys bf (calcMaxBT qa qb t 0 n).1 Hf ∧ s64.valid xf = true := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, h12, hlen, hvx⟩ :=
    calc_max_exec hnv Ev t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp hlh
  have htr := calcMax_props qa qb t.height t (Nat.le_refl _) 0 n R.leaf
  obtain ⟨hinv, hval⟩ := Inv.calcMax qa qb t 0 n ys R.inv R.shape hsafe
  refine ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, hvx⟩
  · rw [h12]; simp only [specMax]; rw [hval]
  · exact BRepS.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen
theorem calc_min_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15) (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb] P inf n 1 qa qb 0 L)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H) (hsafe : calcSafe qa qb t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_min.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 1 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      xf = min INF (rangeMinOf 0 qa qb ys) ∧ BRepS n L SC ys bf (calcMinBT qa qb t 0 n).1 Hf ∧ s64.valid xf = true := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, h12, hlen, hvx⟩ :=
    calc_min_exec hnv Ev t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp hlh
  have htr := calcMin_props qa qb t.height t (Nat.le_refl _) 0 n R.leaf
  obtain ⟨hinv, hval⟩ := Inv.calcMin qa qb t 0 n ys R.inv R.shape hsafe
  refine ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, hvx⟩
  · rw [h12]; simp only [specMin]; rw [hval]
  · exact BRepS.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

end Proofs.BeatsSeparate
