import Proofs.BeatsOp3Frame
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

/-- The recursion of the descent case, once the iteration at the node has been done. -/
theorem frame3_down_rec {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 3 qa qb x L) (hx1 : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP3 mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP3 mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (xl xr : List Int) (hinvl : BeatsModel.Inv (applyTag tg nd l) xl) (hinvr : BeatsModel.Inv (applyTag tg nd r) xr)
    (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hsafel : setSafeRec qa qb x (applyTag tg nd l) lo ((lo + hi) / 2))
    (hsafer : setSafeRec qa qb x (applyTag tg nd r) ((lo + hi) / 2) hi)
    (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ L) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsRange qa qb nd lo hi = Cls.down) (hroot : (H k).1 = nd)
    (b1 : BS) (hit : Iter mv P pre inf n 3 qa qb x b sp ne b1 (sp - 1 + 2) (ne + 1))
    (hHR1 : HRel inf b1 (pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int)))
    (hstk1 : StkRep b1 (sp - 1 + 2) (⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S))
    (hent1 : EntRep b1 (ne + 1) (k :: E)) (hV1 : ValidOK b1) (hS1 : SameLen b b1)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp3 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsRange qa qb) (setBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 3 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 3 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
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
  have hstep : stepF (clsRange qa qb) (fun f c => Cellh.setC ((f.hi - f.lo : Nat) : Int) x c) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ =
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
  have hLens1 : Lens b1 L := Lens_of_same hLens hS1
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
      have hLensK : Lens bK L := Lens_of_same hLens1 hSL
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
          have hbig := down_assemble (clsRange qa qb) (fun f c => Cellh.setC ((f.hi - f.lo : Nat) : Int) x c) (setBT x) nd tg l r k lo hi H H0 H1 H2 S E E1 E2
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
            refine sumOK_node3 qa qb x hx1 nd tg l r k lo hi xl xr hinvl hinvr hshl' hshr' hsafel hsafer hlh _ ?_ ?_
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
  have hspM : sp < M31 := by have := Ev.hLM; omega
  have hr' := runs_of_iter mv Ev.hnv P pre inf n 3 qa qb x b b1 sp ne (sp - 1 + 2) (ne + 1) hspM hsp0 hit F bf nef _ _ hr
  refine ⟨bf, nef, F + 1, by rw [hnod]; omega, runsE_weaken hr' (by rw [hnod]; omega) (by rw [hnod]; omega), hF⟩

theorem frame3_down {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 3 qa qb x L) (hx1 : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (nd : Nd) (tg : Tag) (l r : BT)
    (ihl : FrameP3 mv pre P inf n qa qb x L Fin (F0 + nodesOf r) (nodesOf r * 117614 + C0) (nodesOf r * 47 + Wc) (applyTag tg nd l))
    (ihr : FrameP3 mv pre P inf n qa qb x L Fin F0 C0 Wc (applyTag tg nd r))
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hag : Agree H (.node nd tg l r) k) (hsh : Shape lo hi (BT.node nd tg l r).skel) (hlf : LeafOK (.node nd tg l r))
    (hinv : BeatsModel.Inv (.node nd tg l r) ys) (hsafe : setSafeRec qa qb x (.node nd tg l r) lo hi)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK (.node nd tg l r) k L) (hlen : LenOK b (.node nd tg l r) k lo hi)
    (hstk : StkRep b sp (⟨k, lo, hi⟩ :: S)) (hent : EntRep b ne E)
    (hsp : sp + (BT.node nd tg l r).height + 2 ≤ L) (hne : ne + innerOf (.node nd tg l r) + 1 < L) (hlh : lo ≤ hi ∧ 2 * hi < M31)
    (hcd : clsRange qa qb nd lo hi = Cls.down)
    (K : ∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp3 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk (.node nd tg l r) k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsRange qa qb) (setBT x) (.node nd tg l r) lo hi) k →
      Enew.length ≤ innerOf (.node nd tg l r) →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 3 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) :
    ∃ bf nef F, F ≤ F0 + nodesOf (.node nd tg l r) ∧
      RunsE mv F P pre inf n 3 qa qb x b sp ne bf nef (nodesOf (.node nd tg l r) * 117614 + C0) (nodesOf (.node nd tg l r) * 47 + Wc) ∧
      Fin bf nef := by
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH _ k lo hi hag hsh hlen
  have hnd' : decNd b k = nd := hnd0
  have hroot : (H k).1 = nd := by have := hH k; rw [← this.1]; exact hnd'
  have hdown := cls_down3 qa qb x nd lo hi hcd
  rw [← hnd'] at hdown
  obtain ⟨hps, hsl, hsr⟩ := setSafeRec_down qa qb x nd tg l r lo hi hcd hsafe
  obtain ⟨xl, xr, hinvl, hinvr, hys⟩ := Inv.push_parts hinv hps
  have hlfl := hlf
  cases htg : tg.lval with
  | none =>
    have F := down_add_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen hps htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_add Ev St hdown.1 hdown.2 (by decide) F.hmode F.hlenL F.hlenR F.hZ3 F.hZ5
      F.hlv1 F.hlv2 F.hint F.hS0 F.hS1 F.hS2 F.hS3 F.hS4 F.hS5 F.hS6 F.hS7 F.hS8 F.hS9 F.hS10 F.hS11
    exact frame3_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K
  | some v =>
    have F := down_set_facts inf Ev.hinfI b H hH nd tg l r k lo hi ys hinv hag hsh hlen v htg
    obtain ⟨b1, hit, h1, h2, h3, h4, h5⟩ := step_down_set Ev St hdown.1 hdown.2 (by decide) F.hmode F.hlenL F.hlenR F.hint
    exact frame3_down_rec Ev hx1 Fin F0 C0 Wc nd tg l r ihl ihr k lo hi xl xr hinvl hinvr b sp ne S E H hag hsh hlf hsl hsr hV hLens hidx hlen
      hstk hent hsp hne hlh hcd hroot b1 hit h1 h2 h3 h4 h5 K

theorem leaf_not_down3 (qa qb : Nat) (x : Int) (hx : -INF < x ∧ x < INF) (nd : Nd) (lo hi : Nat) (hhi : hi = lo + 1) (h1 : nd.smx = -INF)
    (h2 : nd.smn = INF) (h3 : nd.mn = nd.mx) : clsRange qa qb nd lo hi ≠ Cls.down := clsRange_leaf qa qb nd lo hi hhi

theorem frame3_all {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 3 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ F0 C0 Wc, FrameP3 mv pre P inf n qa qb x L Fin F0 C0 Wc t := by
  intro h
  induction h with
  | zero =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame3_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down3 qa qb x hx nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      simp [BT.height] at ht
  | succ h ih =>
    intro t ht F0 C0 Wc
    cases t with
    | leaf nd =>
      intro k lo hi ys b sp ne S E H hag hsh hlf
      exact frame3_nodown Ev hx Fin F0 C0 Wc (.leaf nd) k lo hi ys b sp ne S E H
        (leaf_not_down3 qa qb x hx nd lo hi hsh hlf.1 hlf.2.1 hlf.2.2) hag hsh hlf
    | node nd tg l r =>
      intro k lo hi ys b sp ne S E H
      by_cases hcd : clsRange qa qb nd lo hi = Cls.down
      · intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
        have hht : (BT.node nd tg l r).height = max l.height r.height + 1 := rfl
        have hl : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_left l.height r.height; omega
        have hr : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; have := Nat.le_max_right l.height r.height; omega
        exact frame3_down Ev hx Fin F0 C0 Wc nd tg l r (ih _ hl _ _ _) (ih _ hr _ _ _) k lo hi ys b sp ne S E H hag hsh hlf hinv hsafe hH hV
          hLens hidx hlen hstk hent hsp hne hlh hcd K
      · exact frame3_nodown Ev hx Fin F0 C0 Wc (.node nd tg l r) k lo hi ys b sp ne S E H hcd


end Proofs.BeatsRep
