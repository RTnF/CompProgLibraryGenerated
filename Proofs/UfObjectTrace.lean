import Proofs.UfObjectStateMethods

namespace Proofs.UfObjectTrace
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppScalar
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.UfObjectState Proofs.UfObjectStateMethods Proofs.DoublingNested

inductive Operation where
  | root (a : Nat)
  | same (a b : Nat)
  | size (a : Nat)
  | unite (a b : Nat)
  | groups
  deriving DecidableEq, Repr

def Operation.Valid (n : Nat) : Operation → Prop
  | .root a | .size a => a < n
  | .same a b | .unite a b => a < n ∧ b < n
  | .groups => True

def Operation.program : Operation → NProgram
  | .root _ => Proofs.UnionFindCandidateInstance.UnionFind_root
  | .same _ _ => Proofs.UnionFindCandidateInstance.UnionFind_same
  | .size _ => Proofs.UnionFindCandidateInstance.UnionFind_size
  | .unite _ _ => Proofs.UnionFindCandidateInstance.UnionFind_unite
  | .groups => Proofs.UnionFindCandidateInstance.UnionFind_num_groups

def Operation.expressions : Operation → List (NExpr × Int)
  | .root a | .size a => [(.literal i32 (a : Int),(a : Int))]
  | .same a b | .unite a b => [(.literal i32 (a : Int),(a : Int)),(.literal i32 (b : Int),(b : Int))]
  | .groups => []

def expand (object : ObjectRef) (op : Operation) : Option (List NArgument) :=
  match object.scalarSlots with
  | [counter,size] => some ([.vectorReference object.vectorSlot,.scalarReference counter,
      .value (.variable i32 size)] ++ Proofs.CppMoveReceiverResolve.arguments op.expressions)
  | _ => none

def invoke (fuel : Nat) (s : Context) (object : ObjectRef) (op : Operation) : Outcome (Context × Ret) := do
  let args ← liftChecked (expand object op)
  Proofs.CppMoveCallBindings.callFuel op.program fuel s i32 args

theorem expand_state (s : Context) (object : ObjectRef) (state : State s object) (op : Operation) :
    expand object op = some (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) := by
  simp [expand,state.receiver.fields,Proofs.UfObjectCall.arguments]

theorem invoke_state (fuel : Nat) (s : Context) (object : ObjectRef) (state : State s object) (op : Operation) :
    invoke fuel s object op = Proofs.CppMoveCallBindings.callFuel op.program fuel s i32
      (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) := by
  simp [invoke,expand_state s object state op,bind,Outcome.bind,liftChecked]

theorem same_length (s out : Context) (object : ObjectRef) (before : State s object) (after : State out object)
    (size : after.receiver.size.value = before.receiver.size.value) : after.data.items.length = before.data.items.length := by
  have a := before.size
  have b := after.size
  omega

theorem literal_valid (s : Context) (object : ObjectRef) (state : State s object) (a : Nat)
    (inside : a < state.data.items.length) : i32.valid (a : Int) = true := by
  have length := state.math.length
  exact Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)

-- Observable method semantics are kept for every step of a history.
def Effect (before after : List Int) (groups nextGroups : Int) (op : Operation) (result : Ret) : Prop :=
  match op with
  | .root a => ∃ (r : Nat), result = .scalar (r : Int) ∧
      Proofs.UfCompression.Compressed before after a r ∧ nextGroups = groups
  | .same a b => ∃ (r1 r2 : Nat) (middle : List Int), result = .scalar (if r1=r2 then 1 else 0) ∧
      Proofs.UfCompression.Compressed before middle a r1 ∧ Proofs.UfCompression.Compressed middle after b r2 ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected before a b) ∧ nextGroups = groups
  | .size a => result = .scalar ((Proofs.UfClassInvariant.component before a).length : Int) ∧
      (∃ (r : Nat), Proofs.UfCompression.Compressed before after a r) ∧ nextGroups = groups
  | .unite a b => ∃ (r1 r2 : Nat) (middle two : List Int),
      result = .scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int) ∧
      Proofs.UfCompression.Compressed before middle a r1 ∧ Proofs.UfCompression.Compressed middle two b r2 ∧
      after = Proofs.UfUniteCall.uniteVec two r1 r2 ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected before a b) ∧
      nextGroups = Proofs.UfFieldsUnite.countAfter groups r1 r2
  | .groups => result = .scalar groups ∧ after = before ∧ nextGroups = groups

def bodyWork (rank : Nat → Nat) : Operation → Nat
  | .root a => 91*rank a+81
  | .same a b => 91*rank a+91*rank b+181
  | .size a => 91*rank a+101
  | .unite a b => 91*rank a+91*rank b+343
  | .groups => 3

structure Step (s : Context) (object : ObjectRef) (state : State s object) (op : Operation)
    (fuel : Nat) (out : Context) (result : Ret) (next : State out object) : Prop where
  actual : invoke fuel s object op = .finished (out,result)
  size : next.receiver.size.value = state.receiver.size.value
  meaning : Effect state.data.items next.data.items state.receiver.counter.value next.receiver.counter.value op result
  cost : ∃ prepared, prepareArguments s i32 op.program.parameters
      (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) = some prepared ∧
      work out ≤ work prepared + bodyWork state.rank op

theorem step (s : Context) (object : ObjectRef) (state : State s object) (op : Operation)
    (ready : op.Valid state.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out object),
      Step s object state op fuel out result next := by
  cases op with
  | root a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,fuel,out,r,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      root_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,fw,actual,compressed,forest,cost,rest⟩ := post
    refine ⟨fuel,out,.scalar (r : Int),next,?_,sizeEq,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · exact ⟨r,rfl,itemsEq.symm ▸ compressed,countEq⟩
    · dsimp only [Operation.program,Operation.expressions,bodyWork]
      refine ⟨prepared,prep,?_⟩
      simpa only [Nat.add_assoc] using cost
  | same a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      same_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,fw,actual,c1,c2,forest,connected,cost,rest⟩ := post
    refine ⟨fuel,out,.scalar (if r1=r2 then 1 else 0),next,?_,sizeEq,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · exact ⟨r1,r2,middle,rfl,c1,itemsEq.symm ▸ c2,connected,countEq⟩
    · dsimp only [Operation.program,Operation.expressions,bodyWork]
      refine ⟨prepared,prep,?_⟩
      simpa only [Nat.add_assoc] using cost
  | size a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,fuel,out,r,weight,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      size_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,fw,actual,atRoot,negative,compressed,forest,weights,meaning,cost,rest⟩ := post
    refine ⟨fuel,out,.scalar (-weight),next,?_,sizeEq,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · exact ⟨congrArg Ret.scalar (meaning _ state.math).1,⟨r,itemsEq.symm ▸ compressed⟩,countEq⟩
    · dsimp only [Operation.program,Operation.expressions,bodyWork]
      refine ⟨prepared,prep,?_⟩
      simpa only [Nat.add_assoc] using cost
  | unite a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,post,next,countEq,sizeEq,itemsEq⟩ :=
      unite_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,rest⟩ := post
    refine ⟨fuel,out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int),next,?_,sizeEq,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · exact ⟨r1,r2,middle,two,rfl,c1,c2,itemsEq.trans finalEq,connected,countEq⟩
    · dsimp only [Operation.program,Operation.expressions,bodyWork]
      refine ⟨prepared,prep,?_⟩
      simpa only [Nat.add_assoc] using cost
  | groups =>
    obtain ⟨prepared,initial,vc,fuel,out,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      counter_step s object state
    obtain ⟨prep,compacted,current,fw,actual,cost,rest⟩ := post
    refine ⟨fuel,out,.scalar state.receiver.counter.value,next,?_,sizeEq,?_,?_⟩
    · rw [invoke_state fuel s object state]
      exact actual
    · exact ⟨rfl,itemsEq,countEq⟩
    · dsimp only [Operation.program,Operation.expressions,bodyWork]
      refine ⟨prepared,prep,?_⟩
      simpa only [Nat.add_assoc] using cost

def run : Context → ObjectRef → List (Nat × Operation) → Outcome (Context × List Ret)
  | s,_,[] => .finished (s,[])
  | s,object,(fuel,op)::tail => do
    let (next,result) ← invoke fuel s object op
    let (last,results) ← run next object tail
    pure (last,result::results)

-- Intermediate States and per-call meanings/costs remain in the proof history.
inductive History (object : ObjectRef) : (s : Context) → State s object → List Operation →
    (out : Context) → List Ret → State out object → Prop where
  | nil (s : Context) (state : State s object) : History object s state [] s [] state
  | cons {s middle out : Context} {state : State s object} {next : State middle object}
      {last : State out object} {op : Operation} {tail : List Operation} {result : Ret} {results : List Ret}
      (ready : op.Valid state.data.items.length) (fuel : Nat)
      (first : Step s object state op fuel middle result next)
      (rest : History object middle next tail out results last) :
      History object s state (op::tail) out (result::results) last

theorem execute (s : Context) (object : ObjectRef) (state : State s object) (ops : List Operation)
    (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next := by
  induction ops generalizing s with
  | nil => exact ⟨[],s,[],state,rfl,rfl,rfl,rfl,.nil s state⟩
  | cons op tail ih =>
    obtain ⟨fuel,middle,result,next,first⟩ := step s object state op (ready op (by simp))
    have length := same_length s middle object state next first.size
    have restReady : ∀ entry ∈ tail, entry.Valid next.data.items.length := by
      intro entry member
      rw [length]
      exact ready entry (by simp [member])
    obtain ⟨script,out,results,final,mapped,ran,count,sizeFinal,history⟩ := ih middle next restReady
    exact ⟨(fuel,op)::script,out,result::results,final,by simp [mapped],
      by simp [run,first.actual,ran,bind,Outcome.bind,pure],by simp [count],sizeFinal.trans first.size,
      .cons (ready op (by simp)) fuel first history⟩

end Proofs.UfObjectTrace
