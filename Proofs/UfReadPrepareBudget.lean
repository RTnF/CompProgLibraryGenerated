import Proofs.UfReadCall
import Proofs.CppMoveArgumentOuter
import Proofs.UfClassInvariant

namespace Proofs.UfReadPrepareBudget
open Proofs.CppMoveContext Proofs.CppMoveReceiverPermissions Proofs.CppMoveReceiverResolve
open Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver Proofs.CppConstructorFinish
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppScalar Proofs.DoublingNested
open Proofs.CppMoveArgumentFacts Proofs.CppMoveArgumentWork Proofs.CppMoveArgumentPeak
open Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout Proofs.CppMoveFrame
open Proofs.UfReadPrograms Proofs.CppVector Proofs.VecExpr Proofs.UfRootCall
open Proofs.CppMoveHeaders

def nodes (expressions : List (NExpr × Int)) : Nat := (expressions.map (fun pair => pair.1.nodes)).sum

theorem arguments_pure (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (expressions : List (NExpr × Int)) (ready : Ready s i32 expressions) :
    ∀ arg ∈ readArguments s object receiver expressions, argumentPure arg := by
  intro arg member
  simp only [readArguments,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl | rfl) | member
  · trivial
  · trivial
  · rfl
  · obtain ⟨pair,inside,rfl⟩ := List.mem_map.mp member
    exact (ready pair.1 pair.2 inside).2.1

theorem argument_cost (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (expressions : List (NExpr × Int)) :
    argumentsWork (readArguments s object receiver expressions) = nodes expressions+3 := by
  simp [readArguments,arguments,argumentsWork,argumentWork,nodes,List.map_map,
    Function.comp_def,NExpr.nodes]
  omega

def prepareBudget (s : Context) (n : Nat) : Nat :=
  max (max s.scalars.peak (scalarLive s+n+3))
    ((s.scalars.memory.length+s.slots.length+10-s.scalars.baseMemory)+10)
def scalarBudget (s : Context) (n : Nat) : Nat :=
  max (prepareBudget s n) ((receiverPrefix s).length+48-s.scalars.baseMemory)
def heapBudget (s : Context) : Nat :=
  max (project s i32).frame.state.storage.peak
    ((project s i32).frame.state.liveSpace+1-(project s i32).frame.state.storage.baseSpace)
def totalBudget (s : Context) (n : Nat) : Nat := max s.peak (scalarBudget s n+heapBudget s)

theorem prepare_base (s out : Context) (program : NProgram) (args : List NArgument)
    (actual : prepareArguments s i32 program.parameters args = some out) :
    out.scalars.baseMemory = s.scalars.baseMemory := by
  unfold prepareArguments at actual
  obtain ⟨pair,resolved,prepared⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  rcases pair with ⟨last,saved⟩
  have stable := resolveArguments_stable s last i32 program.parameters args saved resolved
  exact (prepareSaved_resources last out saved prepared).2.2.2.trans stable.baseline

theorem limits (s prepared : Context) (initial : NState) (program : NProgram)
    (object : ObjectRef) (receiver : ReadReceiver s object i32) (expressions : List (NExpr × Int))
    (ready : Ready s i32 expressions) (arity : program.parameters.length ≤ 5)
    (actual : prepareArguments s i32 program.parameters (readArguments s object receiver expressions) = some prepared)
    (compacted : compact (project prepared i32) = some initial) :
    work prepared ≤ work s+nodes expressions+4+program.parameters.length ∧
    UfReadBody.scalarBudget initial (receiverPrefix s).length ≤ scalarBudget s (nodes expressions) ∧
    initial.peak ≤ max s.peak (prepareBudget s (nodes expressions)+s.objects.heap.peak) ∧
    initial.frame.state = (project s i32).frame.state := by
  have pure := arguments_pure s object receiver expressions ready
  have cost := prepare_work s prepared i32 program.parameters _ pure actual
  have peak := prepare_peak s prepared i32 program.parameters _ pure actual
  have outer := Proofs.CppMoveArgumentOuter.prepare_effects s prepared i32 program.parameters _ pure actual
  have metadata := compact_metadata (project prepared i32) initial compacted
  have base := prepare_base s prepared program _ actual
  have bound : prepared.scalars.peak ≤ prepareBudget s (nodes expressions) := by
    rw [argument_cost] at peak
    simp only [prepareBudget]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [argument_cost] at cost
    omega
  · simp only [UfReadBody.scalarBudget,metadata.2.2.1]
    change max prepared.scalars.peak ((receiverPrefix s).length+48-prepared.scalars.baseMemory) ≤ _
    rw [base]
    exact max_le_max bound (Nat.le_refl _)
  · rw [metadata.2.2.2.2.1]
    change prepared.peak ≤ _
    exact outer.outer.trans (max_le_max (Nat.le_refl _) (Nat.add_le_add_right bound _))
  · rw [metadata.1]
    simp only [project,materialize,outer.heap]

theorem scalar_bound (s : Context) (n : Nat) :
    scalarBudget s n ≤ max s.scalars.peak (scalarLive s+n+s.slots.length+49) := by
  simp only [scalarBudget,prepareBudget,receiverPrefix,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,scalarLive]
  omega


structure Resources (before after : Context) (n : Nat) : Prop where
  scalar : after.scalars.peak ≤ scalarBudget before n
  heap : after.objects.heap.peak ≤ heapBudget before
  total : after.peak ≤ totalBudget before n

theorem resources (s prepared out : Context) (initial : NState) (program : NProgram)
    (object : ObjectRef) (receiver : ReadReceiver s object i32) (expressions : List (NExpr × Int))
    (ready : Ready s i32 expressions) (arity : program.parameters.length ≤ 5)
    (actual : prepareArguments s i32 program.parameters (readArguments s object receiver expressions) = some prepared)
    (compacted : compact (project prepared i32) = some initial) (live : Nat)
    (liveEq : initial.frame.state.liveSpace = live)
    (bounds : UfReadCall.Resources s out initial (receiverPrefix s).length live) :
    Resources s out (nodes expressions) := by
  obtain ⟨_,scalar,outer,state⟩ := limits s prepared initial program object receiver expressions ready arity actual compacted
  have heapEq : UfReadBody.heapBudget initial live = heapBudget s := by
    unfold UfReadBody.heapBudget heapBudget
    rw [←liveEq,state]
  have oldScalar : s.scalars.peak ≤ scalarBudget s (nodes expressions) := by
    simp only [scalarBudget,prepareBudget]
    omega
  have oldLive : scalarLive s ≤ scalarBudget s (nodes expressions) := by
    simp only [scalarBudget,prepareBudget]
    omega
  have scalarLimit : UfReadCall.scalarLimit s initial (receiverPrefix s).length ≤ scalarBudget s (nodes expressions) := by
    simp only [UfReadCall.scalarLimit]
    omega
  have oldHeap : s.objects.heap.peak ≤ heapBudget s := Nat.le_max_left _ _
  have prepareBound : prepareBudget s (nodes expressions) ≤ scalarBudget s (nodes expressions) := Nat.le_max_left _ _
  have initialBound : initial.peak ≤ totalBudget s (nodes expressions) := by
    exact outer.trans (max_le_max (Nat.le_refl _) (Nat.add_le_add prepareBound oldHeap))
  have totalLimit : UfReadCall.totalLimit s initial (receiverPrefix s).length live ≤ totalBudget s (nodes expressions) := by
    unfold UfReadCall.totalLimit
    rw [heapEq]
    unfold totalBudget
    omega
  exact ⟨bounds.scalar.trans scalarLimit,by simpa only [heapEq] using bounds.heap,bounds.total.trans totalLimit⟩

theorem size_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (weights : Proofs.UfFieldsSize.Weights data.items) (a : Nat) (inside : a < data.items.length)
    (expression : NExpr) (typed : expression.resultType = i32) (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (Proofs.CppNestedEval.envOf (project s i32)) = some (a : Int))
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root : Nat) (weight : Int),
      callFuel sizeProgram fuel s i32 (readArguments s object receiver [(expression,(a : Int))]) = .finished (out,.scalar (-weight)) ∧
      Reach data.items a root ∧ root < data.items.length ∧ data.items[root]? = some weight ∧ weight < 0 ∧
      (∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
        -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int)) ∧
      work out ≤ work s+expression.nodes+16*rank a+49 ∧ out.scalars.memory = s.scalars.memory ∧
      Resources s out expression.nodes ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Proofs.CppNestedVectorStore.Value.integer := by
  have ready : Ready s i32 [(expression,(a : Int))] := by
    intro e value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨typed,scalar,denotes⟩
  obtain ⟨prepared,initial,vc,fuel,out,root,weight,prep,compacted,call,reach,rl,atRoot,negative,cost,memory,live,owner,bounds,buffer,found,items⟩ :=
    UfReadCall.size_call s object receiver data current rank forest length weights a inside expression typed scalar denotes
      readable unique covered valid limit baseline contexts
  have prepCost := (limits s prepared initial sizeProgram object receiver [(expression,(a : Int))] ready
    (by decide +kernel) prep compacted).1
  have finalBounds := resources s prepared out initial sizeProgram object receiver [(expression,(a : Int))] ready
    (by decide +kernel) prep compacted vc.L0 live bounds
  have interpretation : ∀ groups, Proofs.UfClassInvariant.Valid data.items groups rank →
      -weight = ((Proofs.UfClassInvariant.component data.items a).length : Int) := by
    intro groups valid
    have result := valid.size_value atRoot negative
    rw [← Proofs.UfClassInvariant.component_eq_members data.items a root reach ⟨weight,atRoot,negative⟩] at result
    exact result
  refine ⟨fuel,out,root,weight,call,reach,rl,atRoot,negative,interpretation,?_,memory,?_,buffer,?_,items⟩
  · simp only [nodes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at prepCost
    omega
  · simpa only [nodes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using finalBounds
  · rw [←owner]; exact found

theorem same_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (data : Buffer Int) (current : currentBuffer s.objects.heap receiver.view.header receiver.header = some data)
    (rank : Nat → Nat) (forest : Forest data.items rank) (length : data.items.length < 2147483648)
    (a b : Nat) (ha : a < data.items.length) (hb : b < data.items.length)
    (ea eb : NExpr) (ready : Ready s i32 [(ea,(a : Int)),(eb,(b : Int))])
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (fuel : Nat) (out : Context) (root1 root2 : Nat),
      callFuel sameProgram fuel s i32 (readArguments s object receiver [(ea,(a : Int)),(eb,(b : Int))]) =
        .finished (out,.scalar (if root1=root2 then 1 else 0)) ∧
      Reach data.items a root1 ∧ Reach data.items b root2 ∧
      (root1=root2 ↔ Proofs.UfFieldsSame.Connected data.items a b) ∧
      work out ≤ work s+ea.nodes+eb.nodes+16*rank a+16*rank b+84 ∧ out.scalars.memory = s.scalars.memory ∧
      Resources s out (ea.nodes+eb.nodes) ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Proofs.CppNestedVectorStore.Value.integer := by
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,prep,compacted,call,reach1,reach2,rl1,rl2,root1,root2,cost,memory,live,owner,bounds,buffer,found,items⟩ :=
    UfReadCall.same_call s object receiver data current rank forest length a b ha hb ea eb ready
      readable unique covered valid limit baseline contexts
  have prepCost := (limits s prepared initial sameProgram object receiver [(ea,(a : Int)),(eb,(b : Int))] ready
    (by decide +kernel) prep compacted).1
  have finalBounds := resources s prepared out initial sameProgram object receiver [(ea,(a : Int)),(eb,(b : Int))] ready
    (by decide +kernel) prep compacted vc.L0 live bounds
  refine ⟨fuel,out,r1,r2,call,reach1,reach2,Proofs.UfFieldsSame.roots_connected data.items a b r1 r2 reach1 reach2 root1 root2,
    ?_,memory,?_,buffer,?_,items⟩
  · simp only [nodes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at prepCost
    omega
  · simpa only [nodes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using finalBounds
  · rw [←owner]; exact found

theorem counter_call (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap receiver.header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap) (valid : AllocationsValid s.objects.heap i32)
    (limit : receiver.header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (baseline : s.scalars.baseMemory ≤ (receiverPrefix s).length)
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (data : Buffer Int) (fuel : Nat) (out : Context),
      currentBuffer s.objects.heap receiver.view.header receiver.header = some data ∧
      callFuel counterProgram fuel s i32 (readArguments s object receiver []) = .finished (out,.scalar receiver.counter.value) ∧
      work out ≤ work s+10 ∧ out.scalars.memory = s.scalars.memory ∧ Resources s out 0 ∧
      ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Proofs.CppNestedVectorStore.Value.integer := by
  have ready : Ready s i32 [] := by intro e value member; simp at member
  obtain ⟨prepared,initial,vc,data,fuel,out,prep,compacted,current,call,cost,memory,live,owner,bounds,buffer,found,items⟩ :=
    UfReadCall.counter_call s object receiver readable unique covered valid limit baseline contexts
  have prepCost := (limits s prepared initial counterProgram object receiver [] ready
    (by decide +kernel) prep compacted).1
  have finalBounds := resources s prepared out initial counterProgram object receiver [] ready
    (by decide +kernel) prep compacted vc.L0 live bounds
  refine ⟨data,fuel,out,current,call,?_,memory,?_,buffer,?_,items⟩
  · simp only [nodes,List.map_nil,List.sum_nil,List.length_cons,List.length_nil] at prepCost
    omega
  · simpa only [nodes,List.map_nil,List.sum_nil] using finalBounds
  · rw [←owner]; exact found

end Proofs.UfReadPrepareBudget
