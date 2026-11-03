import Proofs.Vector2dSumExec
import Proofs.MatMulPrepare

namespace Proofs.Vector2dSumCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.MultiVecCallN
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.NestedReadOnly Proofs.Vector2dSumExec
open Proofs.MatMulPrepare (bindRoot_g)

/-- The caller owns a nested root (`w` rows, row `i` is the object `V + 1 + i` with the contents `rows[i]`), passed through the
slot `vslot`. -/
structure NOKG (caller : NState) (ty : Ty) (vslot vb V vsc : Nat) (rows : List (List Int)) (wb m : Bool) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.vector (.integer ty),wb,.root vsc⟩
  graph : RootGraph caller.frame.state V ty rows.length vsc
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  perm : wb = true → m = true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length
  rowsStore : ∀ i (h : i < rows.length), ∃ buf, caller.frame.state.storage.lookup (V + 1 + i) = some buf ∧
    buf.items = (rows[i]).map Value.integer

theorem bindRootN_g (f : Frame) {V vsc w : Nat} {m : Bool} (ty : Ty) (wr : Bool) (g : RootGraph f.state V ty w vsc)
    (lengths : f.rootWritable.length = f.state.forest.objects.length) (flag : f.rootWritable[V]? = some m)
    (perm : wr = true → m = true) :
    f.bindRoot V (.vector (.integer ty)) vsc wr = some (f.addBinding ⟨V,.vector (.integer ty),wr,.root vsc⟩) := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object f V ty w vsc g
  have vmax : f.maximum V = some m := maximum_root_g f V ty w vsc g lengths m flag
  simp only [Frame.bindRoot, rootObject, vmax, Bind.bind, Option.bind]
  simp
  exact ⟨rfl, rfl, perm⟩

theorem resolve_nref (c : NState) (ty : Ty) (writable : Bool) {slot vb V vsc w : Nat} {wb m : Bool}
    (hslot : c.vectorSlot slot = some vb) (hbind : c.frame.bindings[vb]? = some ⟨V,.vector (.integer ty),wb,.root vsc⟩)
    (g : RootGraph c.frame.state V ty w vsc) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
    (flag : c.frame.rootWritable[V]? = some m) (hperm : wb = true → m = true) (hw : writable = true → wb = true) :
    resolve c (.nested ty writable) (.vectorReference slot) = some (c.charge 1 1, .nestedRoot V vsc ty writable) := by
  obtain ⟨root,rootObject,rootFound,epoch,items⟩ := root_object c.frame V ty w vsc g
  have resolved : c.frame.resolve vb (.vector (.integer ty)) = some (⟨V,.vector (.integer ty),wb,.root vsc⟩,root) :=
    resolve_root c.frame vb _ _ vsc root (rootTag ty vsc V w) m hbind rfl rfl rootObject rfl rfl
      (maximum_root_g c.frame V ty w vsc g lengths m flag) hperm
  simp [resolve, hslot, hbind, resolved]
  exact hw


theorem prepare_v2d (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller s64 vslot vb V vsc rows wb m) :
    ∃ Sinit, prepare caller Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long.parameters
          [.vectorReference vslot] = some Sinit ∧
        Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope + 1 ∧
        Sinit.frame = ⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer s64),false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_nref caller s64 false ok.slot ok.binding ok.graph ok.lengths ok.flag ok.perm (fun h => absurd h (by decide))
  have b0 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V) (vsc := vsc) (m := m) s64 false
    ok.graph ok.lengths ok.flag (fun h => absurd h (by decide))
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0
  have hp : Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long.parameters = [.nested s64 false] := rfl
  rw [hp]
  simp [prepare, ok.valid, resolveAll, rv0]
  simp [b0, bindAll, bindOne, callerP, NState.observe, CppState.State.observe, NState.charge]

def bbV : Nat → Buffer Value := fun _ => ⟨0, [], 0, 0, 0⟩

/-- The contents family: row `i` of the nested vector parameter 0 is `vv (rowKey 0 i)`. -/
def rowsVV (rows : List (List Int)) : Nat → List Int := fun key =>
  if key / 4294967296 = 1 then (rows[key % 4294967296]?).getD [] else []

theorem rowsVV_row (rows : List (List Int)) (hR : rows.length < 4294967296) (i : Nat) (h : i < rows.length) :
    rowsVV rows (rowKey 0 i) = rows[i] := by
  have hi : i < 4294967296 := by omega
  unfold rowsVV rowKey
  have e1 : (4294967296 * (0 + 1) + i) / 4294967296 = 1 := by omega
  have e2 : (4294967296 * (0 + 1) + i) % 4294967296 = i := by omega
  simp [e1, e2, h]

def mvV2D (V vsc : Nat) (m : Bool) (rows : List (List Int)) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => s64
  wV := fun _ => false
  flag := fun _ => m
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
  wN := fun _ => false
  permN := by intro k hk; simp at hk
  wNnest := by intro k hk; simp at hk
  wrows := fun _ => rows.length
  nvSmall := by decide
  rfree := by intro j k i hj hk hf; simp at hf
  nfree := by
    intro k k' i i' hk hk' hf hf' hi hi' hne
    have hk0 : k = 0 := by simpa using hk
    have hk1 : k' = 0 := by simpa using hk'
    subst hk0; subst hk1
    have : i ≠ i' := by rcases hne with h | h; exact absurd rfl h; exact h
    show V + 1 + i ≠ V + 1 + i'
    omega
  nroot := by intro k k' i hk hk' hf hf' hi; show V ≠ V + 1 + i; omega
  wfree := by intro j k hj hk hw; simp at hw

theorem fwV2D_init (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller s64 vslot vb V vsc rows wb m) (hR : rows.length < 4294967296)
    (hs2 : ∀ i (h : i < rows.length), (rows[i]).length < 2^64) :
    FWM (mvV2D V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (rowsVV rows) bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer s64),false,.root vsc⟩]⟩ : Frame) := by
  refine ⟨ok.valid, ok.lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok.strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bindOf, mvV2D]
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hf; simp [mvV2D] at hf
  · intro k hk hn
    have hk0 : k = 0 := by simp [mvV2D] at hk; omega
    subst hk0
    refine ⟨by simp [mvV2D]; omega, ?_, ok.graph, ok.flag, ?_⟩
    · intro i hi
      simp only [mvV2D] at hi
      rw [rowsVV_row rows hR i hi]; exact hs2 i hi
    · intro i hi
      simp only [mvV2D] at hi
      rw [rowsVV_row rows hR i hi]; exact ok.rowsStore i hi

theorem wr_body2 : WrM (fun _ => false) (prog2 1) = true := by simp [WrM]

set_option maxHeartbeats 4000000 in
/-- `vector2d_sum<long long>(g)` returns the sum of all elements of `g` (row by row), when every partial sum fits in
`long long`; the work is at most `(50 * L + 100) * g.size() + c` where `L` bounds the length of the rows. -/
theorem vector2d_sum_correct (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller s64 vslot vb V vsc rows wb m) (L : Nat)
    (hR : rows.length < 2147483647) (hL : ∀ r ∈ rows, r.length ≤ L) (hL' : L < 2147483647)
    (hvalid : ∀ r ∈ rows, ∀ x ∈ r, s64.valid x = true)
    (hOK : ∀ t j r, rows[t]? = some r → j ≤ r.length → s64.valid (sumRows (rows.take t) + (r.take j).sum) = true)
    (hfin : s64.valid (sumRows rows) = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.scalar (sumRows rows)) ∧
      ScalarPostM (mvV2D V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res 0 ((50 * L + 100) * rows.length + 100)
        caller.scalars.memory 0 (rowsVV rows) := by
  have hR' : rows.length < 4294967296 := by omega
  have hs2 : ∀ i (h : i < rows.length), (rows[i]).length < 2^64 := by
    intro i h
    have := hL (rows[i]) (List.getElem_mem h)
    omega
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_v2d caller ok
  have fwS := fwV2D_init caller ok hR' hs2
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,hrps,hcost,hneed,hwk⟩ :=
    prog_exec (mvV2D V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl rfl rfl rows (rowsVV rows) rfl
      (fun i hi => rowsVV_row rows hR' i hi) (callerP caller) (L + 1 + rows.length + 1) L
      hR hL hL' hvalid hOK hfin (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm (mvV2D V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.Vector2dSumInstance.vector2d_sum_std_vector_std_vector_long_long [.vectorReference vslot] Sinit
    (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]) (by simp [callerP]) ok.base
    (by rw [body_eq2]; exact wr_body2) _ rr (by rw [hmk, body_eq2]; exact hexec) _ hret s64 rfl hfin
    (by omega) (by simp [hlenP]) 0 ((50 * L + 100) * rows.length + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

end Proofs.Vector2dSumCall
