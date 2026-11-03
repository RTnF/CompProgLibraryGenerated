import Proofs.BeatsWrap
import Proofs.BeatsAlias
import Proofs.BeatsOp1Apply
import Proofs.BeatsOp2Apply
import Proofs.BeatsOp3Apply
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

theorem tail_chmin : ∃ T, SegmentTreeBeats_chmin.body = W6 0 T ∧ Sim 5 (ApplyOpCmd 20) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_chmin : Wf SegmentTreeBeats_chmin.body = true := by decide
theorem nb_chmin : Nb SegmentTreeBeats_chmin.body ≤ 335 := by decide

set_option maxHeartbeats 64000000 in
theorem chmin_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chminSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
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
    T hsim (by decide) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMin qa qb x) (capMaxBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 0 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_chmin.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', F', r', by rw [hbT]; exact g1, g2, g3, g4', g5, g6, g7, q1, q2, q3, q4, hlen⟩

theorem tail_chmax : ∃ T, SegmentTreeBeats_chmax.body = W6 1 T ∧ Sim 5 (ApplyOpCmd 20) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_chmax : Wf SegmentTreeBeats_chmax.body = true := by decide
theorem nb_chmax : Nb SegmentTreeBeats_chmax.body ≤ 335 := by decide

set_option maxHeartbeats 64000000 in
theorem chmax_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 1 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : chmaxSafe qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_chmax.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 1 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMax qa qb x) (capMinBT x) t 0 n) 0 ∧ bf.len = b.len := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := apply1_exec Ev hx t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hne hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_chmax
  have hWf : Wf (W6 1 T) = true := hbT ▸ wf_chmax
  have hNb : Nb (W6 1 T) ≤ 335 := hbT ▸ nb_chmax
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap_gen mv hnv P (VVB b) inf x n qa qb 1 Ev.hinf Ev.hx Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim (by decide) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsMax qa qb x) (capMinBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 1 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_chmax.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', F', r', by rw [hbT]; exact g1, g2, g3, g4', g5, g6, g7, q1, q2, q3, q4, hlen⟩

theorem tail_add_val : ∃ T, SegmentTreeBeats_add_val.body = W6 2 T ∧ Sim 5 (ApplyOpCmd 20) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_add_val : Wf SegmentTreeBeats_add_val.body = true := by decide
theorem nb_add_val : Nb SegmentTreeBeats_add_val.body ≤ 335 := by decide

set_option maxHeartbeats 64000000 in
theorem add_val_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : addSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
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
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap_gen mv hnv P (VVB b) inf x n qa qb 2 Ev.hinf Ev.hx Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim (by decide) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (addBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 2 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_add_val.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', F', r', by rw [hbT]; exact g1, g2, g3, g4', g5, g6, g7, q1, q2, q3, q4, hlen⟩

theorem tail_update_val : ∃ T, SegmentTreeBeats_update_val.body = W6 3 T ∧ Sim 5 (ApplyOpCmd 20) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_update_val : Wf SegmentTreeBeats_update_val.body = true := by decide
theorem nb_update_val : Nb SegmentTreeBeats_update_val.body ≤ 335 := by decide

set_option maxHeartbeats 64000000 in
theorem update_val_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 3 qa qb x L) (hx : -INF < x ∧ x < INF) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : setSafeRec qa qb x t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hne : 0 + innerOf t + 1 < L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_update_val.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 3 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (setBT x) t 0 n) 0 ∧ bf.len = b.len := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := apply3_exec Ev hx t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hne hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_update_val
  have hWf : Wf (W6 3 T) = true := hbT ▸ wf_update_val
  have hNb : Nb (W6 3 T) ≤ 335 := hbT ▸ nb_update_val
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap_gen mv hnv P (VVB b) inf x n qa qb 3 Ev.hinf Ev.hx Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim (by decide) hWf hNb _ _ (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (travBT (clsRange qa qb) (setBT x) t 0 n) 0) _
    ⟨F, r, by simpa using h1, h2, h3, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W6 3 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_update_val.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', F', r', by rw [hbT]; exact g1, g2, g3, g4', g5, g6, g7, q1, q2, q3, q4, hlen⟩

end Proofs.BeatsRep
