import Proofs.BeatsCalcStep
import Proofs.BeatsFrame0
import Proofs.BeatsLoop8
import Proofs.BeatsCalc
import Proofs.BeatsCalcMin
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

theorem calcSafe_down (a b : Nat) (nd : Nd) (tg : Tag) (l r : BT) (lo hi : Nat)
    (hc : clsRange a b nd lo hi = Cls.down) (h : calcSafe a b (.node nd tg l r) lo hi) :
    PushSafe (.node nd tg l r) ∧ calcSafe a b (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      calcSafe a b (applyTag tg nd r) ((lo + hi) / 2) hi := by
  unfold clsRange at hc
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · rw [if_pos h1] at hc; cases hc
  · rw [if_neg h1] at hc
    by_cases h2 : a ≤ lo ∧ hi ≤ b
    · rw [if_pos h2] at hc; cases hc
    · unfold calcSafe at h
      rw [if_neg h1, if_neg h2] at h
      exact h

theorem clsR_stop (a b : Nat) (nd : Nd) (lo hi : Nat) (h : clsRange a b nd lo hi = Cls.stop) : b ≤ lo ∨ hi ≤ a := by
  unfold clsRange at h
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · exact h1
  · rw [if_neg h1] at h; split at h <;> cases h

theorem clsR_whole (a b : Nat) (nd : Nd) (lo hi : Nat) (h : clsRange a b nd lo hi = Cls.whole) :
    ¬ (b ≤ lo ∨ hi ≤ a) ∧ (a ≤ lo ∧ hi ≤ b) := by
  unfold clsRange at h
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : a ≤ lo ∧ hi ≤ b
    · exact ⟨h1, h2⟩
    · rw [if_neg h2] at h; cases h

theorem clsR_down (a b : Nat) (nd : Nd) (lo hi : Nat) (h : clsRange a b nd lo hi = Cls.down) :
    ¬ (b ≤ lo ∨ hi ≤ a) ∧ ¬ (a ≤ lo ∧ hi ≤ b) := by
  unfold clsRange at h
  by_cases h1 : b ≤ lo ∨ hi ≤ a
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : a ≤ lo ∧ hi ≤ b
    · rw [if_pos h2] at h; cases h
    · exact ⟨h1, h2⟩

theorem calc_stateOK {b : BS} {inf : Int} {sp L k lo hi : Nat} {S : List Fr} {H : Heap} {t : BT}
    (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t k L) (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S))
    (hH : HRel inf b H) (hsp : sp + t.height + 2 ≤ L) (hlh : lo ≤ hi ∧ 2 * hi < M31) :
    StateOK b inf sp 0 L k lo hi S [] H := by
  refine ⟨hV, hLens, ?_, ?_, by omega, by omega, by have := hlh.1; have := hlh.2; omega, hstk, ⟨rfl, by intro j e h; simp at h⟩, hH⟩
  · cases t with
    | leaf nd => exact hidx
    | node nd tg l r => exact hidx.1
  · have := hstk.1
    simp at this
    omega

/-- The data of one of the two queries (maximum / minimum). -/
structure CSpec (qa qb : Nat) where
  val : Nd → Int
  comb : Int → Int → Int
  calcF : BT → Nat → Nat → BT × Int
  idv : Int
  RB : Int → Prop
  hstop : ∀ t lo hi, clsRange qa qb t.nd lo hi = Cls.stop → calcF t lo hi = (t, idv)
  hwhole : ∀ t lo hi, clsRange qa qb t.nd lo hi = Cls.whole → calcF t lo hi = (t, val t.nd)
  hdown : ∀ nd tg l r lo hi, clsRange qa qb nd lo hi = Cls.down →
    calcF (.node nd tg l r) lo hi = (.node nd noTag (calcF (applyTag tg nd l) lo ((lo + hi) / 2)).1 (calcF (applyTag tg nd r) ((lo + hi) / 2) hi).1,
      comb (calcF (applyTag tg nd l) lo ((lo + hi) / 2)).2 (calcF (applyTag tg nd r) ((lo + hi) / 2) hi).2)
  hid : ∀ r, RB r → comb r idv = r
  hRB : ∀ r v, RB r → RB (comb r v)
  hassoc : ∀ r p q, comb (comb r p) q = comb r (comb p q)
  hvalid : ∀ r v, s64.valid r = true → s64.valid v = true → s64.valid (comb r v) = true
  hvalNd : ∀ (b : BS) (i : Nat), ValidOK b → i < b.mxv.length → i < b.mnv.length → s64.valid (val (decNd b i)) = true

abbrev stepC (qa qb : Nat) (sp_ : CSpec qa qb) := stepCalc (clsRange qa qb) sp_.val sp_.comb

def WholeStep (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb L : Nat) (sp_ : CSpec qa qb) : Prop :=
  ∀ (x : Int), Env mv pre P inf n op qa qb x L → ∀ {b : BS} {sp W0 W1 W2 : Nat} {S : List Fr} {H : Heap},
    StateOK b inf sp 0 L W0 W1 W2 S [] H → ¬ (qb ≤ W1 ∨ W2 ≤ qa) → (qa ≤ W1 ∧ W2 ≤ qb) →
    ∃ b', IterC mv P pre inf n op qa qb x b sp (sp_.comb x (sp_.val (decNd b W0))) b' (sp - 1) ∧ HRel inf b' H ∧
      StkRep b' (sp - 1) S ∧ ValidOK b' ∧ SameLen b b'

def FrameCI (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (L : Nat) (sp_ : CSpec qa qb) (Fin : BS → Int → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → calcSafe qa qb t lo hi →
    HRel inf b H → ValidOK b → Lens b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → sp + t.height + 2 ≤ L → (lo ≤ hi ∧ 2 * hi < M31) → s64.valid r = true → sp_.RB r →
    (∀ (bK : BS) (H' : Heap) (rK : Int), HRel inf bK H' → StkRep bK (sp - 1) S → ValidOK bK → SameLen b bK →
      Star (stepC qa qb sp_) ⟨H, ⟨k, lo, hi⟩ :: S, r⟩ ⟨H', S, rK⟩ → (∀ j, ¬ descN k j → H' j = H j) →
      Agree H' (sp_.calcF t lo hi).1 k → rK = sp_.comb r (sp_.calcF t lo hi).2 → s64.valid rK = true →
      ∃ bf xf F, F ≤ F0 ∧ RunsCE mv F P pre inf n op qa qb rK bK (sp - 1) bf xf C0 Wc ∧ Fin bf xf) →
    ∃ bf xf F, F ≤ F0 + nodesOf t ∧ RunsCE mv F P pre inf n op qa qb r b sp bf xf (nodesOf t * 72254 + C0) (nodesOf t * 24 + Wc) ∧ Fin bf xf

def FrameCP (mv : MV) (pre P : List Cell) (inf : Int) (n op qa qb : Nat) (L : Nat) (sp_ : CSpec qa qb) (Fin : BS → Int → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int),
    FrameCI mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t k lo hi ys b sp S H r


theorem frameC_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : Env mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep mv pre P inf n op qa qb L sp_) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (r : Int)
    (hnd : clsRange qa qb t.nd lo hi ≠ Cls.down) : FrameCI mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t k lo hi ys b sp S H r := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hsp hlh hvr hRB K
  have Ev := Env_withX Ev0 r hvr
  have St := calc_stateOK hV hLens hidx hstk hH hsp hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev0.hLM; omega
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


theorem frameC_down_rec {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : Env mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameCP mv pre P inf n op qa qb L sp_ Fin (F0 + nodesOf r) (nodesOf r * 72254 + C0) (nodesOf r * 24 + Wc) (applyTag tg nd l))
    (ihr : FrameCP mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (xl xr : List Int) (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (rr : Int)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hsafel : calcSafe qa qb (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : calcSafe qa qb (applyTag tg nd r) ((lo + hi) / 2) hi)
    (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S))
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ L) (hlh : lo ≤ hi ∧ 2 * hi < M31) (hvr : s64.valid rr = true) (hRB : sp_.RB rr)
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
  have hLens1 : Lens b1 L := Lens_of_same hLens hS1
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
      have hLensK : Lens bK L := Lens_of_same hLens1 hSL
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
  have hspM : sp < M31 := by have := Ev0.hLM; omega
  have hr' := runsC_of_iter mv Ev0.hnv P pre inf n op qa qb rr rr b b1 sp (sp - 1 + 2) hspM hsp0 hit F bf xf _ _ hr
  refine ⟨bf, xf, F + 1, by rw [hnod]; omega, runsC_weaken hr' (by rw [hnod]; omega) (by rw [hnod]; omega), hF⟩


theorem frameC_down {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : Env mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (Fin : BS → Int → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameCP mv pre P inf n op qa qb L sp_ Fin (F0 + nodesOf r) (nodesOf r * 72254 + C0) (nodesOf r * 24 + Wc) (applyTag tg nd l))
    (ihr : FrameCP mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (applyTag tg nd r))
    :
    ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp : Nat) (S : List Fr) (H : Heap) (rr : Int),
      clsRange qa qb nd lo hi = Cls.down →
      FrameCI mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp S H rr := by
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

theorem frameC_all {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : Env mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep mv pre P inf n op qa qb L sp_) (Fin : BS → Int → Prop) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ F0 C0 Wc, FrameCP mv pre P inf n op qa qb L sp_ Fin F0 C0 Wc t := by
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

end Proofs.BeatsRep
