import Proofs.BeatsCapChmin
import Proofs.BeatsCapUpdate1

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec

variable {SC : Nat}
theorem step_whole2 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n op qa qb x L) {b : BS} {sp ne W0 W1 W2 : Nat} {S : List Fr} {E : List Nat} {H : Heap}
    (St : StateOKK SC b inf sp ne L W0 W1 W2 S E H) (hnot : ¬ stopP op qa qb x (decNd b W0) W1 W2)
    (hwhole : wholeP op qa qb x (decNd b W0) W1 W2) (hop2 : op = 2) (hxne : x ≠ inf) (hadd7 : (b.lval.getD W0 0) ≠ inf → (b.lval.getD W0 0) + x ≠ inf)
    (hS0 : s64.valid ((b.mxv.getD W0 0) + x) = true) (hS1 : (((b.smx.getD W0 0) ≠ (-inf))) → s64.valid ((b.smx.getD W0 0) + x) = true)
    (hS2 : s64.valid ((b.mnv.getD W0 0) + x) = true) (hS3 : (((b.smn.getD W0 0) ≠ inf)) → s64.valid ((b.smn.getD W0 0) + x) = true)
    (hS4 : ((((b.lval.getD W0 0) = inf) ∧ ((b.len.getD W0 0) ≠ 1))) → s64.valid ((b.ladd.getD W0 0) + x) = true)
    (hS5 : ((((b.lval.getD W0 0) ≠ inf) ∧ ((b.len.getD W0 0) ≠ 1))) → s64.valid ((b.lval.getD W0 0) + x) = true) :
    ∃ b', Iter mv P pre inf n op qa qb x b sp ne b' (sp - 1) ne ∧ HRel inf b' (H.set W0 (Cellh.addC x (H W0))) ∧
      StkRep b' (sp - 1) S ∧ EntRep b' ne E ∧ ValidOK b' ∧ SameLen b b' := by
  have C := mk_ctx_separate b inf n op qa qb sp ne x W0 W1 W2 L Ev.hinf Ev.hninf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx St.hV St.hLens Ev.hLM Ev.hKM
    St.hk St.hsp St.hspL St.hneL St.hlohi
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := iter_whole2 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n op qa qb sp ne x S E W0 W1 W2 C St.hstk St.hent hnot hwhole hop2 hxne Ev.hinfI hadd7 H St.hH hS0 hS1 hS2 hS3 hS4 hS5
  exact ⟨b', h6, h1, h2, h3, h4, h5⟩


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
def FrameI2 (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → addSafeRec qa qb x t lo hi →
    HRel inf b H → ValidOK b → CapS SC b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → EntRep b ne E → sp + t.height + 2 ≤ SC → ne + innerOf t + 1 < L → (lo ≤ hi ∧ 2 * hi < M31) →
    (∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp2 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk t k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) t lo hi) k → Enew.length ≤ innerOf t →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 2 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) →
    ∃ bf nef F, F ≤ F0 + nodesOf t ∧ RunsE mv F P pre inf n 2 qa qb x b sp ne bf nef (nodesOf t * 117614 + C0) (nodesOf t * 47 + Wc) ∧ Fin bf nef

def FrameP2 (SC : Nat) (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap),
    FrameI2 SC mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H

theorem frame2_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hnd : clsRange qa qb t.nd lo hi ≠ Cls.down) : FrameI2 SC mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, htag0⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by
    have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev.hKM; omega
  have hn1 : 1 ≤ nodesOf t := by cases t <;> (show 1 ≤ nodesS _; unfold nodesS; first | omega | (split <;> omega))
  have hcost : 117614 + C0 ≤ nodesOf t * 117614 + C0 := by have := Nat.mul_le_mul_right 117614 hn1; omega
  have hwk : 47 + Wc ≤ nodesOf t * 47 + Wc := by have := Nat.mul_le_mul_right 47 hn1; omega
  -- the traversal at this node is not a descent
  cases hc : clsRange qa qb t.nd lo hi with
  | down => exact absurd hc hnd
  | stop =>
    have hst := cls_stop2 qa qb x t.nd lo hi hc
    rw [← hnd0] at hst
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_stop Ev St hst (by decide +kernel)
    have hK := K b' ne H [] h1 h2 (by simpa using h3) h4 h5 (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial (fun _ _ => rfl)
      (by rw [travBT_stop _ _ t lo hi hc]; simpa [upPhase] using hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 2 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    refine ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩
  | whole =>
    have hwh := cls_whole2 qa qb x t.nd lo hi hc
    rw [← hnd0] at hwh
    have hxne : x ≠ inf := by rw [Ev.hinfI]; exact Int.ne_of_lt hx.2
    have hAS : AddSafe x t := addSafe_of_whole qa qb x t lo hi hc hsafe
    have hyseq : ys = arr t := hinv.eq_arr
    obtain ⟨hS0, hS1, hS2, hS3, hS4, hS5, hadd7⟩ := child_cell_sums inf Ev.hinfI b k t ys x hinv hnd0 htag0
      (by rw [hyseq]; exact hAS.1) hAS.2.1 hAS.2.2
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_whole2 Ev St hwh.1 hwh.2 rfl hxne hadd7 hS0 hS1 hS2 hS3 hS4 (fun h => hS5 h.1)
    have hK := K b' ne (H.set k (Cellh.addC x (H k))) [] h1 h2 (by simpa using h3) h4 h5
      (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial
      (fun j hj => Heap.set_ne _ _ _ _ (fun e => hj (e ▸ descN_self _)))
      (by rw [travBT_whole _ _ t lo hi hc]; simpa [upPhase] using agree_addBT H t k x hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 2 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    exact ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩


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
theorem frame2_down_rec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx1 : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP2 SC mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP2 SC mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (xl xr : List Int) (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hsafel : addSafeRec qa qb x (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : addSafeRec qa qb x (applyTag tg nd r) ((lo + hi) / 2) hi)
    (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ SC) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsRange qa qb nd lo hi = Cls.down) (hroot : (H k).1 = nd)
    (b1 : BS) (hit : Iter mv P pre inf n 2 qa qb x b sp ne b1 (sp - 1 + 2) (ne + 1))
    (hHR1 : HRel inf b1 (pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int)))
    (hstk1 : StkRep b1 (sp - 1 + 2) (⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S))
    (hent1 : EntRep b1 (ne + 1) (k :: E)) (hV1 : ValidOK b1) (hS1 : SameLen b b1)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp2 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 2 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 2 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
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
  have hstep : stepF (clsRange qa qb) (fun _ => Cellh.addC x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ =
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
          have hbig := down_assemble (clsRange qa qb) (fun _ => Cellh.addC x) (addBT x) nd tg l r k lo hi H H0 H1 H2 S E E1 E2
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
            refine sumOK_node2 qa qb x hx1 nd tg l r k lo hi xl xr hinvl hinvr hshl' hshr' hsafel hsafer hlh _ ?_ ?_
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
  have hr' := runs_of_iter mv Ev.hnv P pre inf n 2 qa qb x b b1 sp ne (sp - 1 + 2) (ne + 1) hspM hsp0 hit F bf nef _ _ hr
  refine ⟨bf, nef, F + 1, by rw [hnod]; omega, runsE_weaken hr' (by rw [hnod]; omega) (by rw [hnod]; omega), hF⟩

theorem frame2_down {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx1 : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP2 SC mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP2 SC mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hinv : BeatsModel.Inv (.node nd tg l r) ys) (hsafe : addSafeRec qa qb x (.node nd tg l r) lo hi)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ SC) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsRange qa qb nd lo hi = Cls.down)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp2 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 2 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 2 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
      Fin bf nef := by
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH _ k lo hi hag hsh hlen
  have hnd' : decNd b k = nd := hnd0
  have hroot : (H k).1 = nd := by have := hH k; rw [← this.1]; exact hnd'
  have hdown := cls_down2 qa qb x nd lo hi hcd
  rw [← hnd'] at hdown
  obtain ⟨hps, hsl, hsr⟩ := addSafeRec_down qa qb x nd tg l r lo hi hcd hsafe
  obtain ⟨xl, xr, hinvl, hinvr, hys⟩ := Inv.push_parts hinv hps
  have hlfl := hlf
  cases htg : tg.lval with
  | none =>
    have F := down_add_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen hps htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_add Ev St hdown.1 hdown.2 (by decide +kernel) F.hmode F.hlenL F.hlenR F.hZ3 F.hZ5
      F.hlv1 F.hlv2 F.hint F.hS0 F.hS1 F.hS2 F.hS3 F.hS4 F.hS5 F.hS6 F.hS7 F.hS8 F.hS9 F.hS10 F.hS11
    exact frame2_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K
  | some v =>
    have F := down_set_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen v htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_set Ev St hdown.1 hdown.2 (by decide +kernel) F.hmode F.hlenL F.hlenR F.hint
    exact frame2_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K

theorem leaf_not_down2 (qa qb : Nat) (x : Int) (hx : -INF < x ∧ x < INF) (nd : Nd) (lo hi : Nat) (hhi : hi = lo + 1) (h1 : nd.smx = -INF)
    (h2 : nd.smn = INF) (h3 : nd.mn = nd.mx) : clsRange qa qb nd lo hi ≠ Cls.down := clsRange_leaf qa qb nd lo hi hhi

theorem frame2_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ F0 C0 Wc, FrameP2 SC mv pre P inf n qa qb x L Fin F0 C0 Wc t := by
  intro h
  induction h with
  | zero =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame2_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down2 qa qb x hx nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      simp [BT.height] at ht
  | succ h ih =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame2_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down2 qa qb x hx nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      intro k lo hi ys b sp ne S E H
      by_cases hcd : clsRange qa qb nd lo hi = Cls.down
      · intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
        have hht : (BT.node nd tg l r).height = max l.height r.height + 1 := rfl
        have hl : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_left l.height r.height; omega
        have hr : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_right l.height r.height; omega
        exact frame2_down Ev hx Fin F0 C0 Wc nd tg l r (ih _ hl _ _ _) (ih _ hr _ _ _) k lo hi ys b sp ne S E H hag hsh hlf hinv hsafe hH hV
          hLens hidx hlen hstk hent hsp hne hlh hcd K
      · exact frame2_nodown Ev hx Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp ne S E H hcd


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
theorem loop2_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (ne : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : addSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hstk : StkRep b 1 [⟨0, 0, n⟩]) (hent : EntRep b 0 []) (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L)
    (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ bf nef F, F ≤ 1 + nodesOf t ∧ RunsE mv F P pre inf n 2 qa qb x b 1 0 bf nef (nodesOf t * 117614 + 4) (nodesOf t * 47 + 0) ∧
      ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp2 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H' := by
  have key := frame2_all Ev hx (fun bf nef => ∃ (H' : Heap) (Enew : List Nat), HRel inf bf H' ∧ EntRep bf nef Enew ∧ ValidOK bf ∧ SameLen b bf ∧
        Agree (upPhase Enew H') (travBT (clsRange qa qb) (addBT x) t 0 n) 0 ∧ Enew.length ≤ innerOf t ∧ (∀ e ∈ Enew, InSk t 0 e) ∧
        Star (Stp2 qa qb x) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧ SumsOK Enew H') t.height t (le_refl _) 1 4 0
  have := key 0 0 n ys b 1 0 [] [] H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh
    (by
      intro bK neK H' Enew hH' hst hen hV' hSL hStar _ hIn hSm _ hAg hlen'
      refine ⟨bK, neK, 1, le_refl _, ?_, H', Enew, hH', by simpa using hen, hV', hSL, hAg, hlen', hIn, by simpa using hStar, by simpa using hSm⟩
      exact runs_exit mv Ev.hnv 0 P pre inf n 2 qa qb x bK neK)
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
theorem apply2_exec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : EnvK SC mv pre P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : addSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31)
:
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (ApplyOpCmd (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci 2, ci qa, ci qb, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P (pre ++ LCells inf n 2 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 ∧ r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (addBT x) t 0 n) 0 := by
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
    loop2_all Ev hx t ys (initB b n) 0 H hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initB_stk b n hlk hll hlr) hEntI hsp hne hlh
  have hLensf : CapS SC bf L := Capacities.of_same hLensI hSLf
  have hEL : ∀ e ∈ Enew, 2 * e + 2 < L := fun e he => InSks_lt t.skel 0 L e hidx (hIn e he)
  have hnefL : nef ≤ L := by have := hEnt.1; omega
  obtain ⟨bf2, F2, hF2, hRunU, hHR2, hV2, hSL2, -, -, -⟩ :=
    upd_all mv Ev.hnv pre Ev.hty Ev.hty32 P inf n 2 qa qb 0 x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM (by decide +kernel) Ev.hx L Ev.hLM
      Enew bf nef H' hEnt hVf hLensf hEL hnefL hSm hHR'
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hRunU
  have h1' := pexecM_mono mv _ _ _ r1 F1 F2 h1
  have h2' := pexecM_mono mv _ _ _ r2 F2 F1 h2
  rw [Nat.add_comm F2 F1] at h2'
  have h2'' : pexecM mv (F1 + F2) (ULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2'
  have hseq := seqM_some h1' hr1 (seqM_some h2'' hr2 (pexecM_skip mv (F1 + F2) r2.ps r2.vv))
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    ApInit_ch0 mv Ev.hnv pre Ev.hty Ev.hty32 b P inf n 2 qa qb x Ev.hinf Ev.hnM Ev.hopM Ev.hqaM Ev.hqbM Ev.hx hV.v11 hV.v12 hV.v13
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
theorem add_val_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : addSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : CapS SC b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ SC) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_add_val.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 2 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (addBT x) t 0 n) 0 ∧ bf.len = b.len := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := apply2_exec Ev hx t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hne hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_add_val
  have hWf : Wf (W6 2 T) = true := hbT ▸ wf_add_val
  have hNb : Nb (W6 2 T) ≤ 335 := hbT ▸ nb_add_val
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap_gen mv hnv P (VVB b) inf x n qa qb 2 Ev.hinf Ev.hx Ev.hnM Ev.hqaM Ev.hqbM (by decide +kernel)
    T hsim (by decide +kernel) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (addBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 2 T) = true := hbT ▸ (by decide +kernel : noWr 6 SegmentTreeBeats_add_val.body = true)
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
theorem add_val_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : EnvK SC mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H) (hsafe : addSafeRec qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_add_val.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 2 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRepS n L SC (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    add_val_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsRange qa qb) (addBT x) (skel_addBT x) (LeafOK_addBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [addRec_eq]
  have hinv := Inv.add_range qa qb x t 0 n ys R.inv R.shape hsafe
  rw [addRec_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRepS.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

end Proofs.BeatsSeparate
