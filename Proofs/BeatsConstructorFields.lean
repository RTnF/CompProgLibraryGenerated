import Proofs.BeatsInlineExec
import Proofs.CppConstructorMultiFinish
import Proofs.CppConstructorRetirement

namespace Proofs.BeatsConstructorFields
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppVector
open Proofs.CppRootModel Proofs.MultiVec Proofs.CppNestedFacts
open Proofs.BeatsInlineExec Proofs.BeatsInlineFrame Proofs.BeatsPrepare Proofs.BeatsRep
open Proofs.QuotientFrame Proofs.CppConstructorMultiFinish
open Proofs.BeatsModel Proofs.BeatsExec Proofs.DoublingNested Proofs.IntSim

-- The normalized view changes indices, never physical root models.
theorem final_models {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n) (i : Nat) (bound : i < 16) :
    Models out.frame.state (V i) (.flat (cty i) (vsc i) (vv i)) := by
  obtain ⟨distinct,buffers,work,frame,_⟩ := layout
  exact ⟨frame.valid,frame.vtag i bound,buffers i,frame.vfound i bound,frame.items i bound⟩

theorem final_lengths {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n) :
    16 ≤ out.slots.length ∧ 16 ≤ out.frame.bindings.length := by
  obtain ⟨distinct,buffers,work,frame,scalars⟩ := layout
  have slots : 16 ≤ (normalize out).slots.length := by
    rw [scalars.slots]
    simp only [slN,List.length_append,List.length_map,List.length_range]
    omega
  have bindings : (normalize out).frame.bindings.length = 16 := by
    rw [frame.bindings]
    simp only [List.length_map,List.length_range]
    rfl
  simp only [normalize,Proofs.BeatsBindingCycle.view,Proofs.BeatsBindingCycle.rebind,
    Proofs.BeatsSlotCycle.permute,List.length_map,Proofs.BeatsSlotCycle.rotate,
    List.length_append,List.length_take,List.length_drop] at slots bindings
  constructor <;> omega

def field (i : Nat) : VectorField := ⟨i+1,.integer (cty i)⟩
def fieldBinding (V vsc : Nat → Nat) (i : Nat) : Binding :=
  ⟨V i,.integer (cty i),cw i,.root (vsc i)⟩
def vectorFields : List VectorField := (List.range 15).map field

theorem final_field {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n) (i : Nat) (bound : i < 15)
    (scope : vsc i = out.scope) :
    ∃ index buffer, out.vectorSlot (i+1) = some index ∧
      out.frame.resolve index (.integer (cty i)) = some (fieldBinding V vsc i,buffer) ∧
      (fieldBinding V vsc i).element = (field i).element ∧
      (fieldBinding V vsc i).header = .root out.scope := by
  have longs := final_lengths layout
  obtain ⟨distinct,buffers,work,frame,scalars⟩ := layout
  let mv := mvCtor initial V vsc m distinct
  have inside : i < 16 := by omega
  have found : (normalize out).frame.bindings[i]? = some (fieldBinding V vsc i) := by
    rw [frame.bindings]
    change ((List.range 16).map (bindOf mv))[i]? = _
    simp only [List.getElem?_map,List.getElem?_range inside,Option.map_some]
    rfl
  have object := object_runs (normalize out).frame (V i) (.integer (cty i)) (buffers i)
    ⟨.integer (cty i),none,some (vsc i),[]⟩ frame.valid (frame.vfound i inside) (frame.vtag i inside) rfl
  have maximum := maximum_runs (normalize out).frame (V i) (V i) true frame.lengths
    (Proofs.CppVectorOwnership.root_runs _ (V i) _ (frame.vtag i inside) rfl)
    (by simpa only [mvCtor,mvB,ite_eq_left bound] using frame.flagR i inside)
  have resolved := resolve_root (normalize out).frame i (.integer (cty i)) (fieldBinding V vsc i)
    (vsc i) (buffers i) ⟨.integer (cty i),none,some (vsc i),[]⟩ true found rfl rfl object rfl rfl maximum
    (by intro _; rfl)
  have slot : (normalize out).vectorSlot i = some i := by
    simp only [NState.vectorSlot,scalars.slots,slN,List.getElem?_append_left
      (show i < ((List.range 16).map Proofs.CppMixedInvoke.Location.vector).length by simpa using inside),
      List.getElem?_map,List.getElem?_range inside,Option.map_some,Bind.bind,Option.bind]
  have commute := Proofs.BeatsBindingCycle.vector_resolve (Proofs.BeatsSlotCycle.permute out) longs.2 i (.integer (cty i))
  rw [Proofs.BeatsSlotCycle.vectorSlot_permute out longs.1] at commute
  change ((normalize out).vectorSlot i).bind (fun index => (normalize out).frame.resolve index (.integer (cty i))) = _ at commute
  rw [slot,Option.bind_some,resolved] at commute
  have cycle : Proofs.BeatsSlotCycle.cycle i = i+1 := by simp [Proofs.BeatsSlotCycle.cycle,bound]
  rw [cycle] at commute
  obtain ⟨index,actualSlot,actualResolve⟩ := Option.bind_eq_some_iff.mp commute.symm
  exact ⟨index,buffers i,actualSlot,actualResolve,rfl,by simpa only [fieldBinding] using congrArg Header.root scope⟩

theorem final_vector_fields {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n)
    (scope : ∀ i, i < 15 → vsc i = out.scope) :
    VectorFieldsMatch out vectorFields ((List.range 15).map (fieldBinding V vsc)) := by
  have mapped : ∀ ids : List Nat, (∀ i ∈ ids, i < 15) →
      VectorFieldsMatch out (ids.map field) (ids.map (fieldBinding V vsc)) := by
    intro ids
    induction ids with
    | nil => intro _; trivial
    | cons i ids ih =>
      intro bounded
      have bound := bounded i (by simp)
      exact ⟨final_field layout i bound (scope i bound),ih (fun j member => bounded j (by simp [member]))⟩
  exact mapped _ (fun i member => List.mem_range.mp member)


def scalarFields : List Proofs.CppConstructorFinish.ScalarField :=
  [⟨16,Proofs.IntSim.s64⟩,⟨17,Proofs.DoublingNested.i32⟩]
def scalarValues (n : Nat) : List Proofs.CppConstructorFinish.ScalarValue :=
  [(⟨Proofs.IntSim.s64,INF⟩,true),(⟨Proofs.DoublingNested.i32,n⟩,true)]

-- Keep evaluation abstract in both the state and cell value. Specializing a
-- large state directly to Nat-to-Int values creates unnecessarily deep terms.
theorem scalar_cell_from_layout (s : NState) (P cells : List Proofs.CppState.Cell) (base scope : Nat)
    (qs : QS s [] base scope (Proofs.GenState.gS P cells).mem (Proofs.GenState.gS P cells).bs
      (slN 16 (Proofs.GenState.gS P cells).bs.length))
    (j : Nat) (cell : Proofs.CppState.Cell) (found : cells[j]? = some cell)
    (valid : cell.type.valid cell.value = true) :
    s.scalarCell (16+j) cell.type = some (⟨P.length+j,true⟩,cell) := by
  have inside : j < cells.length := (List.getElem?_eq_some_iff.mp found).1
  have sl : s.slots[16+j]? = some (.scalar j) := by
    rw [qs.slots]
    simp [slN,Proofs.GenState.gS,Proofs.Mod61Body.ssl,List.getElem?_append_right,
      List.getElem?_map,List.getElem?_range inside]
  have binding : s.scalars.bindings[j]? = some ⟨P.length+j,true⟩ := by
    rw [qs.bindings]
    simp [Proofs.GenState.gS,List.getElem?_map,List.getElem?_range inside]
  have memory : s.scalars.memory[P.length+j]? = some cell := by
    rw [qs.memory]
    change (P ++ cells)[P.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simpa using found
  simp [NState.scalarCell,NState.scalarSlot,sl,binding,memory,valid]

theorem final_scalar_fields {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n) (range : 4*n < 2147483648) :
    Proofs.CppConstructorFinish.FieldsMatch out scalarFields (scalarValues n) := by
  have longs := final_lengths layout
  obtain ⟨distinct,buffers,work,frame,scalars⟩ := layout
  have scalar (i : Nat) (ty : Ty) :
      (normalize out).scalarCell i ty = out.scalarCell (Proofs.BeatsSlotCycle.cycle i) ty := by
    rw [normalize,Proofs.BeatsBindingCycle.scalarCell,Proofs.BeatsSlotCycle.scalarCell_permute out longs.1]
  have infValid : s64.valid INF = true := by decide
  have nValid : i32.valid (n : Int) = true :=
    Proofs.BellmanFordExec.i32_valid_nat n (by change n < 2147483648; omega)
  have infCell := scalar_cell_from_layout (normalize out) P (CtCells INF n 0 (4*n))
    initial.scalars.baseMemory initial.scope scalars 0 ⟨s64,INF⟩ rfl infValid
  have nCell := scalar_cell_from_layout (normalize out) P (CtCells INF n 0 (4*n))
    initial.scalars.baseMemory initial.scope scalars 1 ⟨i32,n⟩ rfl nValid
  rw [scalar 16 s64] at infCell
  rw [scalar 17 i32] at nCell
  exact ⟨⟨⟨P.length,true⟩,infCell,rfl⟩,⟨⟨⟨P.length+1,true⟩,nCell,rfl⟩,True.intro⟩⟩


def roots (V vsc : Nat → Nat) (vv : Nat → List Int) : List Proofs.CppConstructorRoots.Root :=
  (List.range 15).map fun i => (V i,View.flat (cty i) (vsc i) (vv i))

theorem final_roots {initial out : NState} {V vsc : Nat → Nat} {m : Bool}
    {vv : Nat → List Int} {P : List Proofs.CppState.Cell} {n : Nat}
    (layout : FinalLayout initial out V vsc m vv P n)
    (scope : ∀ i, i < 15 → vsc i = out.scope) :
    ((roots V vsc vv).map Prod.fst).Nodup ∧
      Proofs.CppConstructorRoots.HaveModels out.frame (roots V vsc vv) out.scope := by
  have distinct := layout.choose
  constructor
  · have mapped : ∀ ids : List Nat, ids.Nodup → (∀ i ∈ ids, i < 15) → (ids.map V).Nodup := by
      intro ids
      induction ids with
      | nil => intro _ _; exact List.nodup_nil
      | cons i ids ih =>
        intro nodup bound
        obtain ⟨absent,tail⟩ := List.nodup_cons.mp nodup
        apply List.nodup_cons.mpr
        constructor
        · intro member
          obtain ⟨j,member,equal⟩ := List.mem_map.mp member
          have hi := bound i (by simp)
          have hj := bound j (by simp [member])
          have different : j ≠ i := by intro same; subst j; exact absent member
          exact distinct j i (by omega) hi different equal
        · exact ih tail (fun j member => bound j (by simp [member]))
    simpa only [roots,List.map_map,Function.comp_def] using
      mapped (List.range 15) List.nodup_range (fun i member => List.mem_range.mp member)
  · intro root member
    change root ∈ (List.range 15).map (fun i => (V i,View.flat (cty i) (vsc i) (vv i))) at member
    obtain ⟨i,inRange,mapped⟩ := List.mem_map.mp member
    subst root
    have bound := List.mem_range.mp inRange
    exact ⟨final_models layout i (by omega),scope i bound⟩

def memberBinding (caller : NState) (V : Nat → Nat) (i : Nat) : Binding :=
  ⟨V i,.integer (cty i),true,.root caller.scope⟩

-- Concrete caller metadata and usable field lookups, in addition to payload
-- models. The prefix can contain updates when the generic caller differs.
def FieldBuffers (result : NState) (V : Nat → Nat) : Prop :=
  ∀ i, i < 15 → ∃ buffer, result.frame.state.storage.lookup (V i) = some buffer ∧
    buffer.Valid (accepts (.integer (cty i))) ∧ buffer.limit = Proofs.CppVectorBindings.sizeLimit (cty i) ∧
    buffer.owner = V i ∧ buffer.items.length < 18446744073709551616

structure ExportLayout (caller result : NState) (V : Nat → Nat) (n : Nat)
    (prefixCells : List Proofs.CppState.Cell) : Prop where
  memory : result.scalars.memory = prefixCells ++ [⟨s64,INF⟩,⟨i32,n⟩]
  scalarBindings : result.scalars.bindings = caller.scalars.bindings ++
    [⟨caller.scalars.memory.length,true⟩,⟨caller.scalars.memory.length+1,true⟩]
  bindings : result.frame.bindings = caller.frame.bindings ++ (List.range 15).map (memberBinding caller V)
  slots : result.slots = caller.slots ++ vectorLocations caller.frame.bindings.length 15 ++
    Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2
  scope : result.scope = caller.scope
  base : result.scalars.baseMemory = caller.scalars.baseMemory
  flags : ∀ i, i < 15 → result.frame.rootWritable[V i]? = some true
  lengths : result.frame.rootWritable.length = result.frame.state.forest.objects.length
  vector : ∀ i, i < 15 → result.vectorSlot (caller.slots.length+i) = some (caller.frame.bindings.length+i) ∧
    result.frame.bindings[caller.frame.bindings.length+i]? = some (memberBinding caller V i)
  infCell : result.scalarCell (caller.slots.length+15) s64 =
    some (⟨caller.scalars.memory.length,true⟩,⟨s64,INF⟩)
  nCell : result.scalarCell (caller.slots.length+16) i32 =
    some (⟨caller.scalars.memory.length+1,true⟩,⟨i32,n⟩)
  buffers : FieldBuffers result V
  strict : ∀ owner c, result.frame.state.forest.context owner = some c → c ≤ result.scope

theorem ExportLayout.congr_fields {caller result : NState} {V W : Nat → Nat} {n : Nat}
    {prefixCells : List Proofs.CppState.Cell} (layout : ExportLayout caller result V n prefixCells)
    (same : ∀ i, i < 15 → V i = W i) : ExportLayout caller result W n prefixCells := by
  have mapped : (List.range 15).map (memberBinding caller V) = (List.range 15).map (memberBinding caller W) := by
    apply List.map_congr_left
    intro i member
    simp only [memberBinding,same i (List.mem_range.mp member)]
  refine ⟨layout.memory,layout.scalarBindings,layout.bindings.trans (congrArg (caller.frame.bindings ++ ·) mapped),
    layout.slots,layout.scope,layout.base,?_,layout.lengths,?_,layout.infCell,layout.nCell,?_,layout.strict⟩
  · intro i bound
    rw [← same i bound]
    exact layout.flags i bound
  · intro i bound
    simpa only [memberBinding,same i bound] using layout.vector i bound
  · intro i bound
    simpa only [same i bound] using layout.buffers i bound

private theorem rebound_members (caller : NState) (V vsc : Nat → Nat) :
    rebound caller.scope ((List.range 15).map (fieldBinding V vsc)) =
      (List.range 15).map (memberBinding caller V) := by
  simp only [rebound,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i member
  have bound := List.mem_range.mp member
  simp [fieldBinding,memberBinding,cw,bound]

-- Export succeeds from the layout produced by the actual constructor body.
-- Caller-prefix fit/type facts concern the initial memory, never a successful
-- finish or a postulated final field representation.
theorem finish_from_layout_full (caller initial out : NState) (V vsc : Nat → Nat) (m : Bool)
    (vv : Nat → List Int) (P : List Proofs.CppState.Cell) (n : Nat)
    (layout : FinalLayout initial out V vsc m vv P n) (range : 4*n < 2147483648)
    (scope : out.scope = caller.scope+1) (fieldsScope : ∀ i, i < 15 → vsc i = out.scope)
    (fits : caller.scalars.memory.length ≤ P.length)
    (types : (P.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type) :
    ∃ result, finish caller out vectorFields scalarFields = some (result,reference caller 15 2) ∧
      (∀ root ∈ roots V vsc vv, Models result.frame.state root.1
        (Proofs.DynamicTransfer.inScope root.2 caller.scope)) ∧
      (∀ owner view, Models out.frame.state owner view → owner ∉ (roots V vsc vv).map Prod.fst →
        view.scope ≠ out.scope → Models result.frame.state owner view) ∧
      ExportLayout caller result V n (P.take caller.scalars.memory.length) := by
  have rootFacts := final_roots layout fieldsScope
  have selected : descriptors ((List.range 15).map (fieldBinding V vsc)) =
      Proofs.CppConstructorRoots.specs (roots V vsc vv) := by
    simp only [descriptors,roots,Proofs.CppConstructorRoots.specs,List.map_map,Function.comp_def,
      fieldBinding,View.element]
  have memory : out.scalars.memory = P ++ CtCells INF n 0 (4*n) := layout.choose_spec.choose_spec.choose_spec.2.memory
  have actualFits : caller.scalars.memory.length ≤ out.scalars.memory.length := by
    rw [memory,List.length_append]
    omega
  have actualTypes : (out.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type := by
    rw [memory,List.take_append]
    simpa only [Nat.sub_eq_zero_of_le fits,List.take_zero,List.append_nil] using types
  have valid := (final_models layout 0 (by decide)).valid
  obtain ⟨result,ran,restoredEq,members,kept,memoryEq,scalarBindingsEq,bindingsEq,slotsEq,scopeEq⟩ := Proofs.CppConstructorMultiFinish.finish_ok caller out vectorFields scalarFields
    ((List.range 15).map (fieldBinding V vsc)) (scalarValues n) (roots V vsc vv) scope actualFits actualTypes
    (final_vector_fields layout fieldsScope) (final_scalar_fields layout range) selected rootFacts.1 valid rootFacts.2
  refine ⟨result,?_,members,kept,?_⟩
  · simpa only [List.length_map,List.length_range,scalarValues,List.length_cons,List.length_nil] using ran
  let exportedFrame := Proofs.DynamicRetire.retiredFrame
    (Proofs.CppConstructorRoots.movedAll out.frame (roots V vsc vv) caller.scope) out.scope
  have flagsEq : result.frame.rootWritable = out.frame.rootWritable := by
    rw [restoredEq]
    exact (Proofs.CppConstructorRoots.movedAll_layout out.frame (roots V vsc vv) caller.scope).2.2
  obtain ⟨distinct,buffers,work,frame,scalars⟩ := layout
  refine ⟨?_,?_,?_,?_,scopeEq,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [memoryEq,memory,List.take_append]
    simp only [Nat.sub_eq_zero_of_le fits,List.take_zero,List.append_nil,scalarValues,
      List.map_cons,List.map_nil]
  · simpa only [scalarValues,Proofs.CppConstructorFinish.scalarBindings] using scalarBindingsEq
  · rw [bindingsEq,rebound_members]
  · simpa only [List.length_map,List.length_range,scalarValues,List.length_cons,List.length_nil] using slotsEq
  · rw [restoredEq]
    rfl
  · intro i bound
    rw [flagsEq]
    simpa only [mvCtor,mvB,ite_eq_left bound,normalize,Proofs.BeatsBindingCycle.view,
      Proofs.BeatsBindingCycle.rebind,Proofs.BeatsSlotCycle.permute] using frame.flagR i (by show i < 16; omega)
  · rw [flagsEq,restoredEq]
    change out.frame.rootWritable.length =
      ((Proofs.CppConstructorRoots.movedAll out.frame (roots V vsc vv) caller.scope).state.retired out.scope).forest.objects.length
    rw [(Proofs.CppNestedVectorStore.retired_lengths _ _).1,
      Proofs.CppConstructorRoots.movedAll_length]
    exact frame.lengths
  · intro i bound
    have found : ((List.range 15).map (fieldBinding V vsc))[i]? = some (fieldBinding V vsc i) := by
      simp [List.getElem?_map,List.getElem?_range bound]
    rw [restoredEq]
    simpa only [fieldBinding,cw,decide_eq_true bound,memberBinding] using
      restored_vector caller out exportedFrame ((List.range 15).map (fieldBinding V vsc)) (scalarValues n)
        i (fieldBinding V vsc i) found
  · rw [restoredEq]
    simpa only [List.length_map,List.length_range,Nat.add_zero] using
      restored_scalar caller out exportedFrame ((List.range 15).map (fieldBinding V vsc)) (scalarValues n)
        0 ⟨s64,INF⟩ true actualFits rfl (by decide)
  · rw [restoredEq]
    have nValid : i32.valid (n : Int) = true :=
      Proofs.BellmanFordExec.i32_valid_nat n (by change n < 2147483648; omega)
    simpa only [List.length_map,List.length_range,Nat.reduceAdd,Nat.add_assoc] using
      restored_scalar caller out exportedFrame ((List.range 15).map (fieldBinding V vsc)) (scalarValues n)
        1 ⟨i32,n⟩ true actualFits rfl nValid

  · intro i bound
    have inside : i < 16 := by omega
    have member : (V i,View.flat (cty i) (vsc i) (vv i)) ∈ roots V vsc vv :=
      List.mem_map.mpr ⟨i,List.mem_range.mpr bound,rfl⟩
    have sameBuffer := Proofs.CppConstructorRetirement.finished_buffer out.frame (roots V vsc vv)
      out.scope caller.scope rootFacts.1 rootFacts.2 (by omega) _ member
    have found : result.frame.state.storage.lookup (V i) = some (buffers i) := by
      rw [restoredEq]
      exact sameBuffer.trans (frame.vfound i inside)
    refine ⟨buffers i,found,frame.bvalid i inside,frame.limit i inside,frame.owner i inside,?_⟩
    rw [frame.items i inside,List.length_map]
    exact frame.small i inside
  · intro owner c found
    have before : ∀ other d, out.frame.state.forest.context other = some d → d ≤ caller.scope+1 := by
      intro other d previous
      have bound := frame.strict other d previous
      change d < initial.scope+1 at bound
      have outScope : out.scope = initial.scope := scalars.scope
      omega
    have models := rootFacts.2
    rw [scope] at models
    have strictFinal := Proofs.CppConstructorRetirement.finished_scope_le out.frame (roots V vsc vv)
      caller.scope valid rootFacts.1 models before
    rw [scopeEq]
    apply strictFinal owner c
    rw [restoredEq] at found
    change exportedFrame.state.forest.context owner = some c at found
    simpa only [exportedFrame,Proofs.DynamicRetire.retiredFrame,scope] using found

theorem finish_from_layout (caller initial out : NState) (V vsc : Nat → Nat) (m : Bool)
    (vv : Nat → List Int) (P : List Proofs.CppState.Cell) (n : Nat)
    (layout : FinalLayout initial out V vsc m vv P n) (range : 4*n < 2147483648)
    (scope : out.scope = caller.scope+1) (fieldsScope : ∀ i, i < 15 → vsc i = out.scope)
    (fits : caller.scalars.memory.length ≤ P.length)
    (types : (P.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type) :
    ∃ result, finish caller out vectorFields scalarFields = some (result,reference caller 15 2) ∧
      (∀ root ∈ roots V vsc vv, Models result.frame.state root.1
        (Proofs.DynamicTransfer.inScope root.2 caller.scope)) ∧
      (∀ owner view, Models out.frame.state owner view → owner ∉ (roots V vsc vv).map Prod.fst →
        view.scope ≠ out.scope → Models result.frame.state owner view) := by
  obtain ⟨result,ran,members,kept,_⟩ :=
    finish_from_layout_full caller initial out V vsc m vv P n layout range scope fieldsScope fits types
  exact ⟨result,ran,members,kept⟩


structure ExportFacts (caller : NState) (n : Nat) (st : Proofs.DynamicOwnedState.State) (p : Proofs.MultiVecDynamic.Parameter)
    (a : List Int) (bf : BS) (step : NStep) (result : NState) : Prop where
  scope : step.state.scope = st.scope
  models : ∀ i, i < 16 → Models step.state.frame.state (Proofs.BeatsAllocationArgs.owner st p i)
    (.flat (cty i) (Proofs.BeatsAllocationArgs.scope st p i) (VVA a bf i))
  kept : ∀ owner view, Models step.state.frame.state owner view →
    owner ∉ (roots (Proofs.BeatsAllocationArgs.owner st p) (Proofs.BeatsAllocationArgs.scope st p) (VVA a bf)).map Prod.fst →
    view.scope ≠ step.state.scope → Models result.frame.state owner view
  layout : ExportLayout caller result (Proofs.BeatsAllocationArgs.owner st p) n
    (st.core.locals.memory.take caller.scalars.memory.length)

-- Whole inline stage plus field export, from initial caller conditions.
theorem stage_export_full {st : Proofs.DynamicOwnedState.State} {p : Proofs.MultiVecDynamic.Parameter} {a : List Int}
    (caller : NState) (h : Proofs.BeatsAllocation.Input st p a) (entry : Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64)
    (scope : st.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ st.core.locals.memory.length)
    (types : (st.core.locals.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type) :
    ∃ fuel step bf heap result,
      runFuel fuel (stage 0 15) s = .finished step ∧ step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      finish caller step.state vectorFields scalarFields = some (result,reference caller 15 2) ∧
      (∀ root ∈ roots (Proofs.BeatsAllocationArgs.owner st p) (Proofs.BeatsAllocationArgs.scope st p)
        (VVA a bf), Models result.frame.state root.1 (Proofs.DynamicTransfer.inScope root.2 caller.scope)) ∧
      ExportFacts caller n st p a bf step result := by
  obtain ⟨allocated,fuel,step,bf,heap,prefixRun,ran,returned,breaking,rep,bodyScope,_,_,_,_,_,_,layout⟩ :=
    stage_exec_full h entry n positive range length values s real strict base buf stored readonly limit
  obtain ⟨prefixStep,prefixRun',after,_⟩ := Proofs.BeatsAllocation.prefix_actual h n length range s real
  have same : prefixStep.state = allocated :=
    congrArg NStep.state (Proofs.CppLoop.Outcome.finished.inj (prefixRun'.symm.trans prefixRun))
  have allocatedScope : allocated.scope = st.scope := by
    rw [← same]
    exact after.scopedState.trans (Proofs.BeatsAllocation.states_scope st n 15)
  have finalScope : step.state.scope = st.scope := bodyScope.trans allocatedScope
  have fieldsScope : ∀ i, i < 15 → Proofs.BeatsAllocationArgs.scope st p i = step.state.scope := by
    intro i bound
    simp only [Proofs.BeatsAllocationArgs.scope,ite_eq_left bound,finalScope]
  obtain ⟨result,finished,members,kept,resultLayout⟩ := finish_from_layout_full caller allocated step.state _ _ _ _ _ n layout range
    (finalScope.trans scope) fieldsScope fits types
  refine ⟨fuel,step,bf,heap,result,ran,returned,breaking,rep,finished,members,finalScope,?_,kept,resultLayout⟩
  intro i bound
  exact final_models layout i bound

theorem stage_export {st : Proofs.DynamicOwnedState.State} {p : Proofs.MultiVecDynamic.Parameter} {a : List Int}
    (caller : NState) (h : Proofs.BeatsAllocation.Input st p a) (entry : Entry st p) (n : Nat)
    (positive : 1 ≤ n) (range : 4*n < 2147483648) (length : a.length = n) (values : InRange a)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Buffer Value) (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit s64)
    (scope : st.scope = caller.scope+1)
    (fits : caller.scalars.memory.length ≤ st.core.locals.memory.length)
    (types : (st.core.locals.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type) :
    ∃ fuel step bf heap result,
      runFuel fuel (stage 0 15) s = .finished step ∧ step.returned = none ∧ step.breaking = false ∧
      BRepS n (8*n+8) 256 a bf (buildBT a 0 n) heap ∧
      finish caller step.state vectorFields scalarFields = some (result,reference caller 15 2) ∧
      ∀ root ∈ roots (Proofs.BeatsAllocationArgs.owner st p) (Proofs.BeatsAllocationArgs.scope st p)
        (VVA a bf), Models result.frame.state root.1 (Proofs.DynamicTransfer.inScope root.2 caller.scope) := by
  obtain ⟨fuel,step,bf,heap,result,ran,returned,breaking,rep,finished,members,_⟩ :=
    stage_export_full caller h entry n positive range length values s real strict base buf stored readonly limit scope fits types
  exact ⟨fuel,step,bf,heap,result,ran,returned,breaking,rep,finished,members⟩

end Proofs.BeatsConstructorFields
