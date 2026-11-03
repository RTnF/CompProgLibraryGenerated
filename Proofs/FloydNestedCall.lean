import Proofs.FloydNestedExec
import Proofs.Vector2dSumCall

namespace Proofs.FloydNestedCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.MultiVecCallN
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.NestedReadOnly
open Proofs.Vector2dSumCall (NOKG bindRootN_g resolve_nref)
open Proofs.FloydNestedExec
open Proofs.FloydWarshallCall (Dm Em Walk Dm_shortest Em_start)

theorem prepare_fwn (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)}
    (ok : NOKG caller s64 vslot vb V vsc rows true true) :
    ∃ Sinit, prepare caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.parameters
          [.vectorReference vslot] = some Sinit ∧
        Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope + 1 ∧
        Sinit.frame = ⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer s64),true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_nref caller s64 true ok.slot ok.binding ok.graph ok.lengths ok.flag ok.perm (fun h => rfl)
  have b0 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V) (vsc := vsc) (m := true) s64 true
    ok.graph ok.lengths ok.flag ok.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0
  have hp : Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.parameters = [.nested s64 true] := rfl
  rw [hp]
  simp [prepare, ok.valid, resolveAll, rv0]
  simp [b0, bindAll, bindOne, callerP, NState.observe, CppState.State.observe, NState.charge]

def mvFW (V vsc : Nat) (n L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => s64
  wV := fun _ => false
  flag := fun _ => true
  R := fun _ => V
  vsc := fun _ => vsc
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw
  flat := fun _ => false
  wflat := by intro k hk; simp at hk
  wN := fun _ => true
  permN := by intro k hk; rfl
  wNnest := by intro k hk; rfl
  wrows := fun _ => n
  nvSmall := by decide
  rfree := by intro j k i hj hk hf; simp at hf
  nfree := by
    intro k k' i i' hk hk' hf hf' hi hi' hne
    have : i ≠ i' := by rcases hne with h | h
                        · have hk0 : k = 0 := by simpa using hk
                          have hk1 : k' = 0 := by simpa using hk'
                          omega
                        · exact h
    show V + 1 + i ≠ V + 1 + i'
    omega
  nroot := by intro k k' i hk hk' hf hf' hi; show V ≠ V + 1 + i; omega
  wfree := by intro j k hj hk hw; simp at hw

/-- The weight matrix of the nested rows (entries are non-negative in the hypotheses of the theorems). -/
def Wof (rows : List (List Int)) : Nat → Nat → Nat := fun p q => (((rows[p]?).getD [])[q]?.getD 0).toNat

theorem rows_eq_init (rows : List (List Int)) (n : Nat) (hrows : rows.length = n) (hrect : ∀ r ∈ rows, r.length = n)
    (hent : ∀ r ∈ rows, ∀ x ∈ r, 0 ≤ x) (p : Nat) (hp : p < n) :
    rows[p]'(by omega) = (List.range n).map (fun q => (Em (Wof rows) 0 0 0 p q : Int)) := by
  have hmem : rows[p]'(by omega) ∈ rows := List.getElem_mem _
  have hl := hrect _ hmem
  apply List.ext_getElem
  · simp [hl]
  · intro q h1 h2
    have hq : q < n := by omega
    simp only [List.getElem_map, List.getElem_range]
    rw [Em_start]
    show _ = (((((rows[p]?).getD [])[q]?.getD 0).toNat : Nat) : Int)
    have e1 : rows[p]? = some (rows[p]'(by omega)) := by simp [hp, hrows]
    have e2 : (rows[p]'(by omega))[q]? = some ((rows[p]'(by omega))[q]) := by simp [h1]
    rw [e1]
    simp only [Option.getD_some]
    rw [e2]
    simp only [Option.getD_some]
    exact (Int.toNat_of_nonneg (hent _ hmem _ (List.getElem_mem _))).symm

theorem fwFW_init (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)}
    (ok : NOKG caller s64 vslot vb V vsc rows true true) (n : Nat) (hrows : rows.length = n)
    (hrect : ∀ r ∈ rows, r.length = n) (hent : ∀ r ∈ rows, ∀ x ∈ r, 0 ≤ x) (hn : n < 4294967296) :
    FWM (mvFW V vsc n caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (FV (Wof rows) n 0 0 0) Proofs.Vector2dSumCall.bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer s64),true,.root vsc⟩]⟩ : Frame) := by
  refine ⟨ok.valid, ok.lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok.strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bindOf, mvFW]
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hf; simp [mvFW] at hf
  · intro k hk hn'
    have hk0 : k = 0 := by simp [mvFW] at hk; omega
    subst hk0
    refine ⟨by simp [mvFW]; omega, ?_, by simpa [mvFW, hrows] using ok.graph, by simpa [mvFW] using ok.flag, ?_⟩
    · intro i hi
      simp only [mvFW] at hi
      rw [FV_len (Wof rows) n 0 0 0 i hn hi]
      have : (4294967296 : Nat) ≤ 2^64 := by norm_num
      omega
    · intro i hi
      simp only [mvFW] at hi
      obtain ⟨buf, hb, hit⟩ := ok.rowsStore i (by omega)
      refine ⟨buf, by simpa [mvFW] using hb, ?_⟩
      rw [FV_row (Wof rows) n 0 0 0 i hn hi, hit, rows_eq_init rows n hrows hrect hent i hi]

set_option maxHeartbeats 4000000 in
/-- `floyd_warshall(d)` on a square matrix `d` of `n` rows of `n` non-negative entries below `2^62` leaves in `d[p][q]` the
length `Dm W n p q` of the shortest walk from `p` to `q` (`W` the original matrix). -/
theorem floyd_warshall_nested_correct (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)}
    (ok : NOKG caller s64 vslot vb V vsc rows true true) (n : Nat) (hrows : rows.length = n)
    (hrect : ∀ r ∈ rows, r.length = n) (hent : ∀ r ∈ rows, ∀ x ∈ r, 0 ≤ x ∧ x < 4611686018427387904)
    (hn : n + 1 < 2147483648) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.callFuel fuel caller
        [.vectorReference vslot] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvFW V vsc n caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res 0 (costL (cK n) n + 100) caller.scalars.memory (n * n * n) (FV (Wof rows) n n 0 0) := by
  have hn32 : n < 4294967296 := by omega
  have hW : ∀ p q, Wof rows p q < 4611686018427387904 := by
    intro p q
    unfold Wof
    cases hr : rows[p]? with
    | none => simp
    | some r =>
      simp only [Option.getD_some]
      cases hx : r[q]? with
      | none => simp
      | some x =>
        simp only [Option.getD_some]
        have := (hent r (List.mem_of_getElem? hr) x (List.mem_of_getElem? hx)).2
        omega
  have hent0 : ∀ r ∈ rows, ∀ x ∈ r, 0 ≤ x := fun r hr x hx => (hent r hr x hx).1
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_fwn caller ok
  have fwS := fwFW_init caller ok n hrows hrect hent0 hn32
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    prog_exec (mvFW V vsc n caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl rfl rfl rfl (Wof rows) n rfl (3 * n + 3) (callerP caller)
      hn hW (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvFW V vsc n caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (fun _ => true)
    (by intro k hk; simp [mvFW])
    caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long
    [.vectorReference vslot] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]) (by simp [callerP]) ok.base
    (by rw [body_eqN]; simp [WrM]) (3 * n + 3) rr (by rw [hmk, body_eqN]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 (costL (cK n) n + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

/-- After the call, row `p` of `d` holds the shortest walk lengths `Dm W n p q` (`q < n`), and `Dm W n p q` is the length of a
shortest walk from `p` to `q` through the vertices `< n` (a walk is a single edge or two walks joined at a vertex). -/
theorem floyd_warshall_nested_table (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)}
    (ok : NOKG caller s64 vslot vb V vsc rows true true) (n : Nat) (hrows : rows.length = n)
    (hrect : ∀ r ∈ rows, r.length = n) (hent : ∀ r ∈ rows, ∀ x ∈ r, 0 ≤ x ∧ x < 4611686018427387904)
    (hn : n + 1 < 2147483648) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.FloydWarshallInstance.floyd_warshall_std_vector_std_vector_long_long.callFuel fuel caller
        [.vectorReference vslot] = .finished (res,Ret.unit) ∧
      res.frame.state.wellFormed = true ∧
      (∀ p, p < n → ∃ buf, res.frame.state.storage.lookup (V + 1 + p) = some buf ∧
        buf.items = ((List.range n).map (fun q => (Dm (Wof rows) n p q : Int))).map Value.integer) ∧
      (∀ p q, Walk (Wof rows) n p q (Dm (Wof rows) n p q) ∧ ∀ L, Walk (Wof rows) n p q L → Dm (Wof rows) n p q ≤ L) ∧
      res.scalars.work ≤ caller.scalars.work + (costL (cK n) n + 100) := by
  obtain ⟨S,f,r,h1,h2,post⟩ := floyd_warshall_nested_correct caller ok n hrows hrect hent hn
  refine ⟨S,f,r,h1,h2,post.valid,?_,fun p q => Dm_shortest _ n p q,by have := post.scalarWork; omega⟩
  intro p hp
  have hn32 : n < 4294967296 := by omega
  obtain ⟨_,_,_,_,rowsOk⟩ := post.nested 0 (by simp [mvFW]) (by simp [mvFW])
  obtain ⟨buf,hb,hit⟩ := rowsOk p (by simpa [mvFW] using hp)
  refine ⟨buf, by simpa [mvFW] using hb, ?_⟩
  rw [hit, FV_row (Wof rows) n n 0 0 p hn32 hp]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [Em_start]

end Proofs.FloydNestedCall
