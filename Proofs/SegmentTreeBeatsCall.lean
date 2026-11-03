import Proofs.BeatsCapUpdate3
import Proofs.BeatsCapCalc
import Proofs.BeatsCtorRep
import Proofs.BeatsCallGen
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec (M31 cs)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.MatMulPrepare
open Proofs.BeatsPrepare
set_option maxRecDepth 100000

theorem INF_pos : (0 : Int) < INF := by unfold INF; decide

/-- The types of the 15 vector parameters of the methods: nine `long long` vectors, six `int` vectors. -/
def bty (i : Nat) : Ty := if i < 9 then s64 else i32

/-- The 15 vectors of a tree in a caller state: distinct, writable, with the given contents. -/
structure BVecs (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) (vv : Nat → List Int) : Prop where
  ok : ∀ i, i < 15 → VOKG caller (bty i) (sl i) (vb i) (V i) (vsc i) true true (vbuf i)
  dist : ∀ j k, j < 15 → k < 15 → j ≠ k → V j ≠ V k
  items : ∀ k, k < 15 → (vbuf k).items = (vv k).map Value.integer
  valid : ∀ k, k < 15 → (vbuf k).Valid (accepts (.integer (bty k)))
  limit : ∀ k, k < 15 → (vbuf k).limit = CppVectorBindings.sizeLimit (bty k)
  owner : ∀ k, k < 15 → (vbuf k).owner = V k
  small : ∀ k, k < 15 → (vv k).length < 18446744073709551616

/-- The callee description for the 15 writable vector parameters. -/
def mvBeats (caller : NState) (V vsc : Nat → Nat) (hdist : ∀ j k, j < 15 → k < 15 → j ≠ k → V j ≠ V k) : MV :=
  mvB 15 bty (fun _ => true) (fun _ => true) V vsc (fun _ h => h) (fun j k hj hk hne _ => hdist j k hj hk hne)
    caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length

theorem Env_beats (caller : NState) (V vsc : Nat → Nat) (hdist : ∀ j k, j < 15 → k < 15 → j ≠ k → V j ≠ V k)
    {n op qa qb L : Nat} {x : Int} {pre P : List Cell} (hx : s64.valid x = true) (hn : n < M31) (hop : op < M31)
    (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) :
    Env (mvBeats caller V vsc hdist) pre P INF n op qa qb x L where
  hnv := rfl
  hty := fun v hv => by show bty v = s64; simp [bty, hv]
  hty32 := fun v h1 h2 => by show bty v = i32; simp [bty]; omega
  hinf := by unfold INF; decide
  hninf := by unfold INF; decide
  hnM := hn
  hopM := hop
  hqaM := hqa
  hqbM := hqb
  hx := hx
  hLM := hL
  hinfI := rfl


set_option maxHeartbeats 64000000 in
/-- The call of a method with the 15 tree vectors and the scalar arguments `inf, n, a, b, x` that returns nothing. -/
theorem beats_apply_call (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {vv : Nat → List Int}
    (hv : BVecs caller sl vb V vsc vbuf vv) (prog : NProgram)
    (hp : prog.parameters = vparams bty (fun _ => true) 0 15 ++
      [.scalar s64 false true, .scalar i32 false true, .scalar i32 false true, .scalar i32 false true, .scalar s64 false true])
    (hwr : WrM (fun _ => true) prog.body = true) (hres : prog.result = ResultKind.unit)
    (n qa qb : Nat) (x : Int) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x)
    (hn : n < M31) (hqa : qa < M31) (hqb : qb < M31) (hx : s64.valid x = true)
    (C W : Nat) (Q : (Nat → List Int) → Prop)
    (hX : ∃ (F : Nat) (r : PRM), pexecM (mvBeats caller V vsc hv.dist) F prog.body
        (gS (callerP caller) [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) vv = some r ∧ r.ret = none ∧
        (∃ cs', r.ps = gS (callerP caller) cs') ∧ Q r.vv ∧ r.cost ≤ C ∧ r.need ≤ (callerP caller).length + 345 ∧ r.wk ≤ W) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller prog.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      prog.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ vf, Q vf ∧ ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
        (C + 37) caller.scalars.memory W vf := by
  obtain ⟨F, r, hexec, hret, ⟨cs', hps⟩, hQ, hcost, hneed, hwk⟩ := hX
  have hI : i32.valid (n : Int) = true := Proofs.LowerBoundIndexCall.validN n hn
  have hIa : i32.valid (qa : Int) = true := Proofs.LowerBoundIndexCall.validN qa hqa
  have hIb : i32.valid (qb : Int) = true := Proofs.LowerBoundIndexCall.validN qb hqb
  have hINF : s64.valid INF = true := by unfold INF; decide
  obtain ⟨Sinit, fuel, res, hprep, hrun, post⟩ := beats_call_unit 333 caller 15 (by norm_num) bty (fun _ => true) sl vb V vsc (fun _ => true) vbuf
    hv.ok (fun _ h => h) (fun j k hj hk hne _ => hv.dist j k hj hk hne) (fun _ => true) (fun _ h => ⟨h, h⟩)
    [(e1, s64, INF), (e2, i32, (n : Int)), (e3, i32, (qa : Int)), (e4, i32, (qb : Int)), (e5, s64, x)] prog hp
    (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨hs1, ty1, v1, hINF⟩
      · exact ⟨hs2, ty2, v2, hI⟩
      · exact ⟨hs3, ty3, v3, hIa⟩
      · exact ⟨hs4, ty4, v4, hIb⟩
      · exact ⟨hs5, ty5, v5, hx⟩)
    vv hv.items hv.valid hv.limit hv.owner hv.small hwr hres F r hexec hret hneed
    (by simp) (C + 37) (by simp; omega)
  refine ⟨Sinit, fuel, res, hprep, hrun, r.vv, hQ, ?_⟩
  have hmem : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hmem] at post
  exact post.relax (by simp) (Nat.le_refl _) hwk


set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_chmin (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hn : n < M31)
    (hsafe : chminSafe qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_chmin.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_chmin.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 0) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := chmin_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_chmin rfl (by decide) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRep n L (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_chmax (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hn : n < M31)
    (hsafe : chmaxSafe qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_chmax.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_chmax.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 1) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := chmax_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_chmax rfl (by decide) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRep n L (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_add_val (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hn : n < M31)
    (hsafe : addSafeRec qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_add_val.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_add_val.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 2) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := add_val_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_add_val rfl (by decide) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRep n L (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_update_val (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hn : n < M31)
    (hsafe : setSafeRec qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_update_val.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_update_val.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 3) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := update_val_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_update_val rfl (by decide) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRep n L (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩


set_option maxHeartbeats 64000000 in
/-- The call of a method with the 15 tree vectors and the scalar arguments `inf, n, a, b` that returns a `long long`. -/
theorem beats_calc_call (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {vv : Nat → List Int}
    (hv : BVecs caller sl vb V vsc vbuf vv) (prog : NProgram)
    (hp : prog.parameters = vparams bty (fun _ => true) 0 15 ++
      [.scalar s64 false true, .scalar i32 false true, .scalar i32 false true, .scalar i32 false true])
    (hwr : WrM (fun _ => true) prog.body = true) (hres : prog.result = ResultKind.scalar s64)
    (n qa qb : Nat) (e1 e2 e3 e4 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int))
    (hn : n < M31) (hqa : qa < M31) (hqb : qb < M31)
    (C W : Nat) (Q : Int → (Nat → List Int) → Prop)
    (hX : ∃ (F : Nat) (r : PRM) (xf : Int), pexecM (mvBeats caller V vsc hv.dist) F prog.body
        (gS (callerP caller) [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb]) vv = some r ∧ r.ret = some xf ∧
        s64.valid xf = true ∧ (∃ cs', r.ps = gS (callerP caller) cs') ∧ Q xf r.vv ∧ r.cost ≤ C ∧
        r.need ≤ (callerP caller).length + 410 ∧ r.wk ≤ W) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare caller prog.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = some Sinit ∧
      prog.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = .finished (res, Ret.scalar xf) ∧
      ∃ vf, Q xf vf ∧ ScalarPostMB 400 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + e4.nodes)))
        (C + 36) caller.scalars.memory W vf := by
  obtain ⟨F, r, xf, hexec, hret, hvx, ⟨cs', hps⟩, hQ, hcost, hneed, hwk⟩ := hX
  have hI : i32.valid (n : Int) = true := Proofs.LowerBoundIndexCall.validN n hn
  have hIa : i32.valid (qa : Int) = true := Proofs.LowerBoundIndexCall.validN qa hqa
  have hIb : i32.valid (qb : Int) = true := Proofs.LowerBoundIndexCall.validN qb hqb
  have hINF : s64.valid INF = true := by unfold INF; decide
  obtain ⟨Sinit, fuel, res, hprep, hrun, post⟩ := beats_call_val 400 caller 15 (by norm_num) bty (fun _ => true) sl vb V vsc (fun _ => true) vbuf
    hv.ok (fun _ h => h) (fun j k hj hk hne _ => hv.dist j k hj hk hne) (fun _ => true) (fun _ h => ⟨h, h⟩)
    [(e1, s64, INF), (e2, i32, (n : Int)), (e3, i32, (qa : Int)), (e4, i32, (qb : Int))] prog hp
    (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨hs1, ty1, v1, hINF⟩
      · exact ⟨hs2, ty2, v2, hI⟩
      · exact ⟨hs3, ty3, v3, hIa⟩
      · exact ⟨hs4, ty4, v4, hIb⟩)
    vv hv.items hv.valid hv.limit hv.owner hv.small hwr s64 hres F r hexec xf hret hvx (by omega)
    (by simp) (C + 36) (by simp; omega)
  refine ⟨Sinit, fuel, res, xf, hprep, hrun, r.vv, hQ, ?_⟩
  have hmem : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hmem] at post
  exact post.relax (by simp) (Nat.le_refl _) hwk

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_calc_max (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) (hn : n < M31)
    (hsafe : calcSafe qa qb t 0 n) (e1 e2 e3 e4 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare caller SegmentTreeBeats_calc_max.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = some Sinit ∧
      SegmentTreeBeats_calc_max.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = .finished (res, Ret.scalar xf) ∧
      xf = max (-INF) (rangeMaxOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L ys bf (calcMaxBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + e4.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) caller.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb]) (P := callerP caller) (op := 0) (L := L) (x := 0)
    (by decide) hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, hxe, hR, hvx⟩ := calc_max_rep rfl hE R hsafe
  obtain ⟨Sinit, fuel, res, xf', hprep, hrun, vf, ⟨bf', Hf', rfl, hxe', hR'⟩, post⟩ := beats_calc_call caller sl vb V vsc vbuf hv SegmentTreeBeats_calc_max rfl (by decide) rfl
    n qa qb e1 e2 e3 e4 hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 v1 v2 v3 v4 hn hqa hqb
    (nodesOf t * 72254 + 4 + 5000 + 16 + 10) (nodesOf t * 24 + 3)
    (fun x v => ∃ bf Hf, v = VVB bf ∧ x = max (-INF) (rangeMaxOf 0 qa qb ys) ∧ BRep n L ys bf (calcMaxBT qa qb t 0 n).1 Hf)
    ⟨F, r, xf, h1, h2, hvx, ⟨_, h3⟩, ⟨bf, Hf, h4, hxe, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, xf', hprep, hrun, hxe', bf', Hf', hR', post⟩

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_calc_min (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRep n L ys b t H)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) (hn : n < M31)
    (hsafe : calcSafe qa qb t 0 n) (e1 e2 e3 e4 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare caller SegmentTreeBeats_calc_min.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = some Sinit ∧
      SegmentTreeBeats_calc_min.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = .finished (res, Ret.scalar xf) ∧
      xf = min INF (rangeMinOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L ys bf (calcMinBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + e4.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) caller.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb]) (P := callerP caller) (op := 1) (L := L) (x := 0)
    (by decide) hn (by norm_num [M31]) hqa hqb hL
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, hxe, hR, hvx⟩ := calc_min_rep rfl hE R hsafe
  obtain ⟨Sinit, fuel, res, xf', hprep, hrun, vf, ⟨bf', Hf', rfl, hxe', hR'⟩, post⟩ := beats_calc_call caller sl vb V vsc vbuf hv SegmentTreeBeats_calc_min rfl (by decide) rfl
    n qa qb e1 e2 e3 e4 hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 v1 v2 v3 v4 hn hqa hqb
    (nodesOf t * 72254 + 4 + 5000 + 16 + 10) (nodesOf t * 24 + 3)
    (fun x v => ∃ bf Hf, v = VVB bf ∧ x = min INF (rangeMinOf 0 qa qb ys) ∧ BRep n L ys bf (calcMinBT qa qb t 0 n).1 Hf)
    ⟨F, r, xf, h1, h2, hvx, ⟨_, h3⟩, ⟨bf, Hf, h4, hxe, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, xf', hprep, hrun, hxe', bf', Hf', hR', post⟩


/-- The types of the 16 vector parameters of the constructor: the 15 tree vectors and the argument array. -/
def cty (i : Nat) : Ty := if i < 9 ∨ i = 15 then s64 else i32

/-- Writable parameters: the 15 tree vectors. -/
def cw (i : Nat) : Bool := decide (i < 15)

/-- Freshly allocated tree vectors: zeroed, `lval` filled with `INF`, long enough. -/
structure BFresh (L : Nat) (b0 : BS) : Prop where
  valid : ValidOK b0
  lens : Lens b0 L
  lo : L ≤ b0.lo.length
  hi : L ≤ b0.hi.length
  mxv : ∀ j, b0.mxv.getD j 0 = 0
  smx : ∀ j, b0.smx.getD j 0 = 0
  mxc : ∀ j, b0.mxc.getD j 0 = 0
  mnv : ∀ j, b0.mnv.getD j 0 = 0
  smn : ∀ j, b0.smn.getD j 0 = 0
  mnc : ∀ j, b0.mnc.getD j 0 = 0
  len : ∀ j, b0.len.getD j 0 = 0
  ladd : ∀ j, b0.ladd.getD j 0 = 0
  lval : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF
  lov : ∀ j, b0.lo.getD j 0 = 0
  hiv : ∀ j, b0.hi.getD j 0 = 0

/-- The vector `i` of the constructor may be mutable in the caller: the 15 tree vectors always, the argument as given. -/
def cm (m15 : Bool) (i : Nat) : Bool := if i < 15 then true else m15

/-- The 16 vectors of the constructor in a caller state: the 15 tree vectors are distinct and writable, the argument is read-only. -/
structure CVecs (caller : NState) (sl vb V vsc : Nat → Nat) (m15 : Bool) (vbuf : Nat → Buffer Value) (vv : Nat → List Int) : Prop where
  ok : ∀ i, i < 16 → VOKG caller (cty i) (sl i) (vb i) (V i) (vsc i) (cw i) (if i < 15 then true else m15) (vbuf i)
  dist : ∀ j k, j < 16 → k < 15 → j ≠ k → V j ≠ V k
  items : ∀ k, k < 16 → (vbuf k).items = (vv k).map Value.integer
  valid : ∀ k, k < 16 → (vbuf k).Valid (accepts (.integer (cty k)))
  limit : ∀ k, k < 16 → (vbuf k).limit = CppVectorBindings.sizeLimit (cty k)
  owner : ∀ k, k < 16 → (vbuf k).owner = V k
  small : ∀ k, k < 16 → (vv k).length < 18446744073709551616

def mvCtor (caller : NState) (V vsc : Nat → Nat) (m15 : Bool) (hdist : ∀ j k, j < 16 → k < 15 → j ≠ k → V j ≠ V k) : MV :=
  mvB 16 cty cw (fun i => if i < 15 then true else m15) V vsc (fun k h => by simp [cw] at h; simp [h])
    (fun j k hj hk hne hw => hdist j k hj (by simpa [cw] using hw) hne)
    caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length

theorem hp_new0 : SegmentTreeBeats_new0.parameters = vparams cty cw 0 16 ++ List.map (fun x : NExpr × Ty × Int => CppVectorBindings.Parameter.scalar x.2.1 false true) [] := rfl

theorem wr_new0 : WrM cw SegmentTreeBeats_new0.body = true := by decide

/-- Abstract the work bound before arithmetic, so the certificate does not expand
    the constructor's large coefficient inside a Presburger proof. -/
private theorem new0_extra_bound {cost bound : Nat} (h : cost ≤ bound) :
    cost + 2 * 16 + 0 + 2 ≤ bound + 34 := by omega

set_option maxHeartbeats 64000000 in
theorem segment_tree_beats_new0 (caller : NState) (sl vb V vsc : Nat → Nat) (m15 : Bool) (vbuf : Nat → Buffer Value)
    (a : List Int) {b0 : BS} (hv : CVecs caller sl vb V vsc m15 vbuf (VVA a b0)) {n L : Nat}
    (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31) (hAlen : a.length = n) (hAr : InRange a) (hF : BFresh L b0) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_new0.parameters (vargs sl 0 16) = some Sinit ∧
      SegmentTreeBeats_new0.callFuel fuel caller (vargs sl 0 16) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRep n L a bf (buildBT a 0 n) Hf ∧
        ScalarPostMB 100 (mvCtor caller V vsc m15 hv.dist) caller Sinit res 0 (4 * n * 45414 + 100 + 34) caller.scalars.memory
          (4 * n * 18 + 10) (VVA a bf) := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := ctor_rep (mvCtor caller V vsc m15 hv.dist) rfl
    (fun v hv' => by show cty v = s64; simp [cty, hv']) (fun v h1 h2 => by show cty v = i32; simp [cty]; omega) (by show cty 15 = s64; simp [cty])
    (callerP caller) a n L hn hL8 hLM hAlen hAr b0 hF.valid hF.lens hF.lo hF.hi hF.mxv hF.smx hF.mxc hF.mnv hF.smn hF.mnc hF.len hF.ladd hF.lval hF.lov hF.hiv
  obtain ⟨Sinit, fuel, res, hprep, hrun, post⟩ := beats_call_unit 100 caller 16 (by norm_num) cty cw sl vb V vsc (fun i => if i < 15 then true else m15) vbuf
    hv.ok (fun k h => by simp [cw] at h; simp [h]) (fun j k hj hk hne hw => hv.dist j k hj (by simpa [cw] using hw) hne) cw (fun k h => ⟨h, by simp [cw] at h; simp [h]⟩)
    [] SegmentTreeBeats_new0 hp_new0 (by intro y hy; simp at hy)
    (VVA a b0) hv.items hv.valid hv.limit hv.owner hv.small wr_new0 rfl F r h1 h2 (by omega) (by simp)
    (4 * n * 45414 + 100 + 34) (new0_extra_bound h5)
  refine ⟨Sinit, fuel, res, hprep, hrun, bf, Hf, hR, ?_⟩
  have hmem : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [h3]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hmem, h4] at post
  exact post.relax (by simp) (Nat.le_refl _) h7

end Proofs.BeatsRep

namespace Proofs.BeatsSeparate
open Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec (M31 cs)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.MatMulPrepare
open Proofs.BeatsPrepare

variable {SC : Nat}
theorem Env_beats (caller : NState) (V vsc : Nat → Nat) (hdist : ∀ j k, j < 15 → k < 15 → j ≠ k → V j ≠ V k)
    {n op qa qb L : Nat} {x : Int} {pre P : List Cell} (hx : s64.valid x = true) (hn : n < M31) (hop : op < M31)
    (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) (hSM : SC < M31) :
    EnvK SC (mvBeats caller V vsc hdist) pre P INF n op qa qb x L where
  hnv := rfl
  hty := fun v hv => by show bty v = s64; simp [bty, hv]
  hty32 := fun v h1 h2 => by show bty v = i32; simp [bty]; omega
  hinf := by unfold INF; decide
  hninf := by unfold INF; decide
  hnM := hn
  hopM := hop
  hqaM := hqa
  hqbM := hqb
  hx := hx
  hLM := hL
  hinfI := rfl
  hKM := hSM


/-- The call of a method with the 15 tree vectors and the scalar arguments `inf, n, a, b, x` that returns nothing. -/

theorem segment_tree_beats_chmin (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : chminSafe qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_chmin.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_chmin.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 0) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := chmin_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_chmin rfl (by decide +kernel) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRepS n L SC (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩


theorem segment_tree_beats_chmax (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : chmaxSafe qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_chmax.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_chmax.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 1) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := chmax_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_chmax rfl (by decide +kernel) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRepS n L SC (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩


theorem segment_tree_beats_add_val (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : addSafeRec qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_add_val.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_add_val.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 2) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := add_val_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_add_val rfl (by decide +kernel) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRepS n L SC (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩


theorem segment_tree_beats_update_val (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (x : Int) (hqa : qa < M31) (hqb : qb < M31) (hx : -INF < x ∧ x < INF) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : setSafeRec qa qb x t 0 n) (e1 e2 e3 e4 e5 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) (v5 : e5.denote (envOf caller) = some x) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_update_val.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = some Sinit ∧
      SegmentTreeBeats_update_val.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4, .value e5]) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf ∧
        ScalarPostMB 333 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + (e4.nodes + e5.nodes))))
          (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 + 37) caller.scalars.memory (nodesOf t * 47 + innerOf t * 6 + 3) (VVB bf) := by
  have hxv : s64.valid x = true := s64_valid_of_bounds x (by have := hx.1; have := INF_pos; omega) (by have := hx.2; have := INF_pos; omega)
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb, cs x]) (P := callerP caller) (op := 3) (L := L)
    hxv hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := update_val_rep rfl hE hx R hsafe
  obtain ⟨Sinit, fuel, res, hprep, hrun, vf, ⟨bf', Hf', rfl, hR'⟩, post⟩ := beats_apply_call caller sl vb V vsc vbuf hv SegmentTreeBeats_update_val rfl (by decide +kernel) rfl
    n qa qb x e1 e2 e3 e4 e5 hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 v1 v2 v3 v4 v5 hn hqa hqb hxv
    (nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12) (nodesOf t * 47 + innerOf t * 6 + 3)
    (fun v => ∃ bf Hf, v = VVB bf ∧ BRepS n L SC (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf)
    ⟨F, r, h1, h2, ⟨_, h3⟩, ⟨bf, Hf, h4, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, hprep, hrun, bf', Hf', hR', post⟩


/-- The call of a method with the 15 tree vectors and the scalar arguments `inf, n, a, b` that returns a `long long`. -/

theorem segment_tree_beats_calc_max (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : calcSafe qa qb t 0 n) (e1 e2 e3 e4 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare caller SegmentTreeBeats_calc_max.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = some Sinit ∧
      SegmentTreeBeats_calc_max.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = .finished (res, Ret.scalar xf) ∧
      xf = max (-INF) (rangeMaxOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC ys bf (calcMaxBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + e4.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) caller.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb]) (P := callerP caller) (op := 0) (L := L) (x := 0)
    (by decide +kernel) hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, hxe, hR, hvx⟩ := calc_max_rep rfl hE R hsafe
  obtain ⟨Sinit, fuel, res, xf', hprep, hrun, vf, ⟨bf', Hf', rfl, hxe', hR'⟩, post⟩ := beats_calc_call caller sl vb V vsc vbuf hv SegmentTreeBeats_calc_max rfl (by decide +kernel) rfl
    n qa qb e1 e2 e3 e4 hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 v1 v2 v3 v4 hn hqa hqb
    (nodesOf t * 72254 + 4 + 5000 + 16 + 10) (nodesOf t * 24 + 3)
    (fun x v => ∃ bf Hf, v = VVB bf ∧ x = max (-INF) (rangeMaxOf 0 qa qb ys) ∧ BRepS n L SC ys bf (calcMaxBT qa qb t 0 n).1 Hf)
    ⟨F, r, xf, h1, h2, hvx, ⟨_, h3⟩, ⟨bf, Hf, h4, hxe, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, xf', hprep, hrun, hxe', bf', Hf', hR', post⟩


theorem segment_tree_beats_calc_min (caller : NState) (sl vb V vsc : Nat → Nat) (vbuf : Nat → Buffer Value) {b : BS}
    (hv : BVecs caller sl vb V vsc vbuf (VVB b)) {n L : Nat} {ys : List Int} {t : BT} {H : Heap} (R : BRepS n L SC ys b t H)
    (qa qb : Nat) (hqa : qa < M31) (hqb : qb < M31) (hL : L < M31) (hSM : SC < M31) (hn : n < M31)
    (hsafe : calcSafe qa qb t 0 n) (e1 e2 e3 e4 : NExpr)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (v1 : e1.denote (envOf caller) = some INF) (v2 : e2.denote (envOf caller) = some (n : Int))
    (v3 : e3.denote (envOf caller) = some (qa : Int)) (v4 : e4.denote (envOf caller) = some (qb : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (xf : Int),
      prepare caller SegmentTreeBeats_calc_min.parameters (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = some Sinit ∧
      SegmentTreeBeats_calc_min.callFuel fuel caller (vargs sl 0 15 ++ [.value e1, .value e2, .value e3, .value e4]) = .finished (res, Ret.scalar xf) ∧
      xf = min INF (rangeMinOf 0 qa qb ys) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC ys bf (calcMinBT qa qb t 0 n).1 Hf ∧
        ScalarPostMB 400 (mvBeats caller V vsc hv.dist) caller Sinit res (e1.nodes + (e2.nodes + (e3.nodes + e4.nodes)))
          (nodesOf t * 72254 + 4 + 5000 + 16 + 10 + 36) caller.scalars.memory (nodesOf t * 24 + 3) (VVB bf) := by
  have hE := Env_beats caller V vsc hv.dist (pre := [cs INF, Proofs.ForLoop.ci n, Proofs.ForLoop.ci qa, Proofs.ForLoop.ci qb]) (P := callerP caller) (op := 1) (L := L) (x := 0)
    (by decide +kernel) hn (by norm_num [M31]) hqa hqb hL hSM
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, hxe, hR, hvx⟩ := calc_min_rep rfl hE R hsafe
  obtain ⟨Sinit, fuel, res, xf', hprep, hrun, vf, ⟨bf', Hf', rfl, hxe', hR'⟩, post⟩ := beats_calc_call caller sl vb V vsc vbuf hv SegmentTreeBeats_calc_min rfl (by decide +kernel) rfl
    n qa qb e1 e2 e3 e4 hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 v1 v2 v3 v4 hn hqa hqb
    (nodesOf t * 72254 + 4 + 5000 + 16 + 10) (nodesOf t * 24 + 3)
    (fun x v => ∃ bf Hf, v = VVB bf ∧ x = min INF (rangeMinOf 0 qa qb ys) ∧ BRepS n L SC ys bf (calcMinBT qa qb t 0 n).1 Hf)
    ⟨F, r, xf, h1, h2, hvx, ⟨_, h3⟩, ⟨bf, Hf, h4, hxe, hR⟩, h5, h6, h7⟩
  exact ⟨Sinit, fuel, res, xf', hprep, hrun, hxe', bf', Hf', hR', post⟩


/-- The types of the 16 vector parameters of the constructor: the 15 tree vectors and the argument array. -/

structure BFreshS (L SC : Nat) (b0 : BS) : Prop where
  valid : ValidOK b0
  lens : CapS SC b0 L
  lo : L ≤ b0.lo.length
  hi : L ≤ b0.hi.length
  mxv : ∀ j, b0.mxv.getD j 0 = 0
  smx : ∀ j, b0.smx.getD j 0 = 0
  mxc : ∀ j, b0.mxc.getD j 0 = 0
  mnv : ∀ j, b0.mnv.getD j 0 = 0
  smn : ∀ j, b0.smn.getD j 0 = 0
  mnc : ∀ j, b0.mnc.getD j 0 = 0
  len : ∀ j, b0.len.getD j 0 = 0
  ladd : ∀ j, b0.ladd.getD j 0 = 0
  lval : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF
  lov : ∀ j, b0.lo.getD j 0 = 0
  hiv : ∀ j, b0.hi.getD j 0 = 0

/-- The vector `i` of the constructor may be mutable in the caller: the 15 tree vectors always, the argument as given. -/

theorem segment_tree_beats_new0 (caller : NState) (sl vb V vsc : Nat → Nat) (m15 : Bool) (vbuf : Nat → Buffer Value)
    (a : List Int) {b0 : BS} (hv : CVecs caller sl vb V vsc m15 vbuf (VVA a b0)) {n L : Nat}
    (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31) (hAlen : a.length = n) (hAr : InRange a) (hSS : 34 ≤ SC) (hF : BFreshS L SC b0) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller SegmentTreeBeats_new0.parameters (vargs sl 0 16) = some Sinit ∧
      SegmentTreeBeats_new0.callFuel fuel caller (vargs sl 0 16) = .finished (res, Ret.unit) ∧
      ∃ (bf : BS) (Hf : Heap), BRepS n L SC a bf (buildBT a 0 n) Hf ∧
        ScalarPostMB 100 (mvCtor caller V vsc m15 hv.dist) caller Sinit res 0 (4 * n * 45414 + 100 + 34) caller.scalars.memory
          (4 * n * 18 + 10) (VVA a bf) := by
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, hR⟩ := ctor_rep_separate (S := SC) (mvCtor caller V vsc m15 hv.dist) rfl
    (fun v hv' => by show cty v = s64; simp [cty, hv']) (fun v h1 h2 => by show cty v = i32; simp [cty]; omega) (by show cty 15 = s64; simp [cty])
    (callerP caller) a n L hn hL8 hLM hAlen hAr hSS b0 hF.valid hF.lens hF.lo hF.hi hF.mxv hF.smx hF.mxc hF.mnv hF.smn hF.mnc hF.len hF.ladd hF.lval hF.lov hF.hiv
  obtain ⟨Sinit, fuel, res, hprep, hrun, post⟩ := beats_call_unit 100 caller 16 (by norm_num) cty cw sl vb V vsc (fun i => if i < 15 then true else m15) vbuf
    hv.ok (fun k h => by simp [cw] at h; simp [h]) (fun j k hj hk hne hw => hv.dist j k hj (by simpa [cw] using hw) hne) cw (fun k h => ⟨h, by simp [cw] at h; simp [h]⟩)
    [] SegmentTreeBeats_new0 hp_new0 (by intro y hy; simp at hy)
    (VVA a b0) hv.items hv.valid hv.limit hv.owner hv.small wr_new0 rfl F r h1 h2 (by omega) (by simp)
    (4 * n * 45414 + 100 + 34) (Proofs.BeatsRep.new0_extra_bound h5)
  refine ⟨Sinit, fuel, res, hprep, hrun, bf, Hf, hR, ?_⟩
  have hmem : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [h3]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hmem, h4] at post
  exact post.relax (by simp) (Nat.le_refl _) h7


end Proofs.BeatsSeparate
