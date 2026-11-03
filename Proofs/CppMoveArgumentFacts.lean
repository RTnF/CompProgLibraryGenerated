import Proofs.CppMoveContext
import Proofs.CppExprPrefix
import Proofs.CppTargetCast

namespace Proofs.CppMoveArgumentFacts
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.DynamicResultValid
open Proofs.CppMoveContext

-- Pure NExpr evaluation may charge resources but does not mutate scalar data.
def ScalarData (s out : NState) : Prop :=
  out.scalars.memory = s.scalars.memory ∧ out.scalars.bindings = s.scalars.bindings ∧
    out.scalars.baseMemory = s.scalars.baseMemory

theorem ScalarData.trans {a b c : NState} (second : ScalarData b c) (first : ScalarData a b) : ScalarData a c :=
  ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2.trans first.2.2⟩

mutual
theorem container_data (c : Container) (s t : NState) (value : Nat)
    (actual : c.eval s = some (t,value)) : ScalarData s t := by
  cases c with
  | «local» slot =>
    unfold Container.eval at actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,rfl,rfl⟩
  | row parent ty index =>
    unfold Container.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨⟨frame,binding⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_data index a b pos rb).trans (container_data parent (s.charge 0 (parent.nodes+index.nodes+1)) a owner ra)
termination_by sizeOf c

theorem expression_data (e : NExpr) (s t : NState) (value : Int)
    (actual : e.eval s = some (t,value)) : ScalarData s t := by
  cases e with
  | literal ty v =>
    unfold NExpr.eval at actual
    split at actual
    · have eq := congrArg Prod.fst (Option.some.inj actual)
      change _ = t at eq
      subst t
      exact ⟨rfl,rfl,rfl⟩
    · simp at actual
  | «variable» ty slot =>
    unfold NExpr.eval at actual
    obtain ⟨cell,_,rest⟩ := bind_some _ _ _ actual
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact ⟨rfl,rfl,rfl⟩
  | cast ty operand | targetCast ty operand | unary ty _ operand =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact expression_data operand (s.charge 0 (operand.nodes+1)) a _ ra
  | binary ty _ left right | divrem ty _ left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨z,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_data right a b y rb).trans (expression_data left (s.charge 0 (left.nodes+right.nodes+1)) a x ra)
  | logical conjunction left right =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
    have first := expression_data left (s.charge 0 (left.nodes+right.nodes+1)) a x ra
    dsimp only at rest
    split at rest <;> split at rest
    all_goals
      first
      | have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact first
      | obtain ⟨⟨b,y⟩,rb,rest⟩ := bind_some _ _ _ rest
        have eq := congrArg Prod.fst (Option.some.inj rest)
        change _ = t at eq
        subst t
        exact (expression_data right a b y rb).trans first
  | size ty c =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨frame,x⟩,rf,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact container_data c (s.charge 0 (c.nodes+2)) a owner ra
  | read ty c index =>
    unfold NExpr.eval at actual
    obtain ⟨⟨a,owner⟩,ra,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨b,pos⟩,rb,rest⟩ := bind_some _ _ _ rest
    obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := congrArg Prod.fst (Option.some.inj rest)
    change _ = t at eq
    subst t
    exact (expression_data index a b pos rb).trans (container_data c (s.charge 0 (c.nodes+index.nodes+2)) a owner ra)
termination_by sizeOf e
end

structure Stable (s out : Context) : Prop where
  objects : out.objects = s.objects
  slots : out.slots = s.slots
  scope : out.scope = s.scope
  memory : out.scalars.memory = s.scalars.memory
  bindings : out.scalars.bindings = s.scalars.bindings
  baseline : out.scalars.baseMemory = s.scalars.baseMemory

theorem Stable.trans {a b c : Context} (first : Stable a b) (second : Stable b c) : Stable a c :=
  ⟨second.objects.trans first.objects,second.slots.trans first.slots,second.scope.trans first.scope,
    second.memory.trans first.memory,second.bindings.trans first.bindings,second.baseline.trans first.baseline⟩

theorem evalExpression_stable (s out : Context) (ty : Ty) (expression : NExpr) (value : Int)
    (run : evalExpression s ty expression = some (out,value)) : Stable s out := by
  unfold evalExpression at run
  obtain ⟨pair,actual,rest⟩ := bind_some _ _ _ run
  rcases pair with ⟨next,result⟩
  have eq := Prod.mk.inj (Option.some.inj rest)
  rw [← eq.1]
  have data := expression_data expression (project s ty) next result actual
  exact ⟨rfl,rfl,rfl,data.1,data.2.1,data.2.2⟩


theorem resolveArgument_stable (s out : Context) (vectorTy : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : Proofs.CppNestedCall.NArgument) (saved : SavedArgument)
    (run : resolveArgument s vectorTy parameter argument = some (out,saved)) : Stable s out := by
  cases parameter with
  | scalar ty reference writable =>
    cases reference with
    | false =>
      cases argument with
      | value expression =>
        simp only [resolveArgument] at run
        split at run
        · obtain ⟨pair,actual,rest⟩ := bind_some _ _ _ run
          rcases pair with ⟨next,value⟩
          have eq := (Prod.mk.inj (Option.some.inj rest)).1
          rw [← eq]
          exact evalExpression_stable s next vectorTy expression value actual
        · simp at run
      | scalarReference slot | vectorReference slot => simp [resolveArgument] at run
    | true =>
      cases argument with
      | scalarReference slot =>
        simp only [resolveArgument] at run
        obtain ⟨argument,_,rest⟩ := bind_some _ _ _ run
        have eq := (Prod.mk.inj (Option.some.inj rest)).1
        rw [← eq]
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      | value expression => simp [resolveArgument] at run
      | vectorReference slot => simp [resolveArgument] at run
  | vector ty writable =>
    cases argument with
    | vectorReference slot =>
      simp only [resolveArgument] at run
      split at run
      · obtain ⟨argument,_,rest⟩ := bind_some _ _ _ run
        have eq := (Prod.mk.inj (Option.some.inj rest)).1
        rw [← eq]
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      · simp at run
    | value expression => simp [resolveArgument] at run
    | scalarReference slot => simp [resolveArgument] at run
  | nested ty writable => cases argument <;> simp [resolveArgument] at run

theorem resolveArguments_stable (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument) (saved : List SavedArgument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) : Stable s out := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have eq := (Prod.mk.inj (Option.some.inj run)).1
      rw [← eq]
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    | cons argument tail => simp [resolveArguments] at run
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [resolveArguments] at run
    | cons argument arguments =>
      simp only [resolveArguments] at run
      obtain ⟨pair,first,rest⟩ := bind_some _ _ _ run
      rcases pair with ⟨next,head⟩
      obtain ⟨pair,tail,last⟩ := bind_some _ _ _ rest
      rcases pair with ⟨final,savedTail⟩
      have eq := (Prod.mk.inj (Option.some.inj last)).1
      rw [← eq]
      exact (resolveArgument_stable s next ty parameter argument head first).trans (ih next final arguments savedTail tail)

theorem stable_savedReady (s out : Context) (argument : SavedArgument) (stable : Stable s out)
    (ready : SavedReady s argument) : SavedReady out argument := by
  apply savedReady_mono s out argument (congrArg Proofs.CppMoveViews.State.heap stable.objects)
  · exact ⟨[],by simp [stable.memory]⟩
  · exact ready


theorem captureBorrow_ready (s : Context) (slot : Nat) (writable : Bool) (argument : Borrow)
    (run : captureBorrow s slot writable = some argument) : SavedReady s (.vector argument) := by
  unfold captureBorrow at run
  obtain ⟨viewSlot,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨pair,resolved,rest⟩ := bind_some _ _ _ rest
  rcases pair with ⟨view,header⟩
  dsimp only at rest
  split at rest
  next permission =>
    have eq := Option.some.inj rest
    subst argument
    have parts := Proofs.CppMoveViews.resolve_parts s.objects viewSlot view header resolved
    exact ⟨header,parts.2.1,fun write => parts.2.2 (permission write)⟩
  next => simp at rest

theorem captureScalarReference_ready (s : Context) (ty : Ty) (slot : Nat) (writable : Bool) (argument : SavedArgument)
    (run : captureScalarReference s ty slot writable = some argument) : SavedReady s argument := by
  unfold captureScalarReference at run
  obtain ⟨pair,cellRun,rest⟩ := bind_some _ _ _ run
  rcases pair with ⟨binding,cell⟩
  dsimp only at rest
  split at rest
  next permission =>
    have eq := Option.some.inj rest
    subst argument
    rw [project_scalarCell] at cellRun
    obtain ⟨index,_,inside⟩ := bind_some _ _ _ cellRun
    obtain ⟨actualBinding,_,inside⟩ := bind_some _ _ _ inside
    obtain ⟨actualCell,found,inside⟩ := bind_some _ _ _ inside
    split at inside
    next typed =>
      have eq := Prod.mk.inj (Option.some.inj inside)
      cases eq.1
      cases eq.2
      exact ⟨cell,found,rfl,typed.1,typed.2⟩
    next => simp at inside
  next => simp at rest


theorem convert_valid (ty : Ty) (value result : Int) (run : ty.convert value = some result) : ty.valid result = true := by
  by_cases boolean : ty.boolean = true
  · cases zero : value == 0 <;> simp [Ty.convert,boolean,zero] at run <;> subst result <;> simp [Ty.valid,boolean]
  · by_cases signed : ty.signed = true
    · simp [Ty.convert,boolean,signed] at run
      obtain ⟨valid,equal⟩ := run
      rw [← equal]
      exact valid
    · simp [Ty.convert,boolean,signed] at run
      rw [← run]
      have positive : (0 : Int) < 2^ty.width := Int.pow_pos (by decide)
      have low := Int.emod_nonneg value (by omega : (2^ty.width : Int) ≠ 0)
      have high := Int.emod_lt_of_pos value positive
      simpa [Ty.valid,boolean,signed] using And.intro low high

theorem targetConvert_valid (ty : Ty) (value result : Int) (run : ty.targetConvert value = some result) : ty.valid result = true := by
  by_cases special : (ty.signed && !ty.boolean) = true
  · have signed := (Bool.and_eq_true_iff.mp special).1
    have boolean : ty.boolean = false := by simpa using (Bool.and_eq_true_iff.mp special).2
    by_cases width32 : ty.width = 32
    · have actual : ty.targetConvert value = some (signedDecode ty.width value) := by simp [Ty.targetConvert,special,width32]
      rw [actual] at run
      cases Option.some.inj run
      have bounds := Proofs.CppTargetCast.decode_bounds ty.width value (by omega)
      simpa [Ty.valid,signed,boolean] using bounds
    · by_cases width64 : ty.width = 64
      · have actual : ty.targetConvert value = some (signedDecode ty.width value) := by simp [Ty.targetConvert,special,width64]
        rw [actual] at run
        cases Option.some.inj run
        have bounds := Proofs.CppTargetCast.decode_bounds ty.width value (by omega)
        simpa [Ty.valid,signed,boolean] using bounds
      · simp [Ty.targetConvert,special,width32,width64] at run
  · have fallback : ty.targetConvert value = ty.convert value := by simp [Ty.targetConvert,special]
    rw [fallback] at run
    exact convert_valid ty value result run

theorem checkedDivRem_valid (ty : Ty) (remainder : Bool) (a b result : Int)
    (run : checkedDivRem ty remainder a b = some result) : ty.valid result = true := by
  unfold checkedDivRem at run
  split at run
  · simp at run
  · split at run
    · simp at run
    · exact convert_valid ty _ result run

theorem readRef_valid (buffer : Proofs.CppVector.Buffer α) (accept : α → Bool) (reference : Proofs.CppVector.ElementRef)
    (result : Proofs.CppVector.Result α α) (run : Proofs.CppVector.readRef buffer accept reference = some result) :
    accept result.value = true := by
  unfold Proofs.CppVector.readRef at run
  split at run
  next good =>
    obtain ⟨value,found,finish⟩ := bind_some _ _ _ run
    have equal := Option.some.inj finish
    rw [← equal]
    exact List.all_eq_true.mp good.1.2.2 value (List.mem_iff_getElem?.mpr ⟨reference.index,found⟩)
  next => simp at run

theorem frame_read_valid (frame : Frame) (reference : Reference) (value : Int)
    (run : frame.read reference = some value) : reference.element.valid value = true := by
  unfold Frame.read at run
  obtain ⟨_,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
  rcases pair with ⟨buffer,tag⟩
  obtain ⟨result,read,finish⟩ := bind_some _ _ _ rest
  have valid := readRef_valid buffer (Proofs.CppNestedVectorStore.accepts (.integer reference.element)) reference.address result read
  cases item : result.value with
  | integer actual =>
    simp only [item,Option.some.injEq] at finish
    subst value
    simpa [Proofs.CppNestedVectorStore.accepts,item] using valid
  | child owner => simp [item] at finish

theorem frame_size_valid (frame out : Frame) (slot : Nat) (element : Proofs.CppVectorOwnership.Element) (value : Int)
    (run : frame.size slot element = some (out,value)) : (⟨64,false,false⟩ : Ty).valid value = true := by
  unfold Frame.size at run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
  rcases pair with ⟨binding,buffer⟩
  dsimp only at rest
  split at rest
  next good =>
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact good
  next => simp at rest


theorem scalarCell_valid (s : NState) (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (run : s.scalarCell slot ty = some (binding,cell)) : cell.type = ty ∧ ty.valid cell.value = true := by
  unfold NState.scalarCell at run
  obtain ⟨_,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨actualBinding,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨actualCell,_,rest⟩ := bind_some _ _ _ rest
  split at rest
  next good =>
    have eq := Prod.mk.inj (Option.some.inj rest)
    cases eq.2
    exact good
  next => simp at rest

theorem elementRef_type (frame : Frame) (slot : Nat) (ty : Ty) (index : Int) (reference : Reference)
    (run : frame.elementRef slot ty index = some reference) : reference.element = ty := by
  unfold Frame.elementRef at run
  obtain ⟨_,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨_,_,rest⟩ := bind_some _ _ _ rest
  have eq := Option.some.inj rest
  rw [← eq]

theorem expression_valid (expression : NExpr) (s out : NState) (value : Int)
    (run : expression.eval s = some (out,value)) : expression.resultType.valid value = true := by
  cases expression with
  | literal ty actual =>
    unfold NExpr.eval at run
    split at run
    next good =>
      have eq := (Prod.mk.inj (Option.some.inj run)).2
      rw [← eq]
      exact good
    next => simp at run
  | «variable» ty slot =>
    unfold NExpr.eval at run
    obtain ⟨pair,found,rest⟩ := bind_some _ _ _ run
    rcases pair with ⟨binding,cell⟩
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact (scalarCell_valid s slot ty binding cell found).2
  | cast ty operand | unary ty _ operand =>
    unfold NExpr.eval at run
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨result,converted,rest⟩ := bind_some _ _ _ rest
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact convert_valid ty _ result converted
  | targetCast ty operand =>
    unfold NExpr.eval at run
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨result,converted,rest⟩ := bind_some _ _ _ rest
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact targetConvert_valid ty _ result converted
  | binary ty op left right =>
    unfold NExpr.eval at run
    obtain ⟨_,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨_,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,converted,rest⟩ := bind_some _ _ _ rest
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact convert_valid ty _ result converted
  | divrem ty remainder left right =>
    unfold NExpr.eval at run
    obtain ⟨_,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨_,_,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,converted,rest⟩ := bind_some _ _ _ rest
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact checkedDivRem_valid ty remainder _ _ result converted
  | logical conjunction left right =>
    change (⟨1,false,true⟩ : Ty).valid value = true
    unfold NExpr.eval at run
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
    rcases pair with ⟨next,first⟩
    dsimp only at rest
    split at rest <;> split at rest
    all_goals
      first
      | have eq := (Prod.mk.inj (Option.some.inj rest)).2
        rw [← eq]
        decide
      | obtain ⟨pair,_,finish⟩ := bind_some _ _ _ rest
        rcases pair with ⟨last,lastValue⟩
        have eq := (Prod.mk.inj (Option.some.inj finish)).2
        rw [← eq]
        split <;> decide
  | size element container =>
    unfold NExpr.eval at run
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    obtain ⟨pair,sized,rest⟩ := bind_some _ _ _ rest
    rcases pair with ⟨frame,result⟩
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact frame_size_valid next.frame frame slot element result sized
  | read ty container index =>
    unfold NExpr.eval at run
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ rest
    rcases pair with ⟨last,position⟩
    obtain ⟨reference,referenced,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,read,rest⟩ := bind_some _ _ _ rest
    have typed := elementRef_type last.frame slot ty position reference referenced
    have valid := frame_read_valid last.frame reference result read
    rw [typed] at valid
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    rw [← eq]
    exact valid


theorem evalExpression_valid (s out : Context) (vectorTy : Ty) (expression : NExpr) (value : Int)
    (run : evalExpression s vectorTy expression = some (out,value)) : expression.resultType.valid value = true := by
  unfold evalExpression at run
  obtain ⟨pair,actual,rest⟩ := bind_some _ _ _ run
  rcases pair with ⟨next,result⟩
  have eq := (Prod.mk.inj (Option.some.inj rest)).2
  rw [← eq]
  exact expression_valid expression (project s vectorTy) next result actual

theorem resolveArgument_ready (s out : Context) (vectorTy : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : Proofs.CppNestedCall.NArgument) (saved : SavedArgument)
    (run : resolveArgument s vectorTy parameter argument = some (out,saved)) : SavedReady out saved := by
  cases parameter with
  | scalar ty reference writable =>
    cases reference with
    | false =>
      cases argument with
      | value expression =>
        simp only [resolveArgument] at run
        split at run
        next type =>
          obtain ⟨pair,actual,rest⟩ := bind_some _ _ _ run
          rcases pair with ⟨next,value⟩
          have eq := Prod.mk.inj (Option.some.inj rest)
          rw [← eq.1,← eq.2]
          have valid := evalExpression_valid s next vectorTy expression value actual
          rw [type] at valid
          exact ⟨rfl,valid⟩
        next => simp at run
      | scalarReference slot | vectorReference slot => simp [resolveArgument] at run
    | true =>
      cases argument with
      | scalarReference slot =>
        simp only [resolveArgument] at run
        obtain ⟨argument,actual,rest⟩ := bind_some _ _ _ run
        have eq := Prod.mk.inj (Option.some.inj rest)
        rw [← eq.1,← eq.2]
        exact stable_savedReady s (charge s 1 1) argument ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
          (captureScalarReference_ready s ty slot writable argument actual)
      | value expression => simp [resolveArgument] at run
      | vectorReference slot => simp [resolveArgument] at run
  | vector ty writable =>
    cases argument with
    | vectorReference slot =>
      simp only [resolveArgument] at run
      split at run
      · obtain ⟨argument,actual,rest⟩ := bind_some _ _ _ run
        have eq := Prod.mk.inj (Option.some.inj rest)
        rw [← eq.1,← eq.2]
        exact stable_savedReady s (charge s 1 1) (.vector argument) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
          (captureBorrow_ready s slot writable argument actual)
      · simp at run
    | value expression => simp [resolveArgument] at run
    | scalarReference slot => simp [resolveArgument] at run
  | nested ty writable => cases argument <;> simp [resolveArgument] at run

theorem resolveArguments_ready (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument) (saved : List SavedArgument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) :
    ∀ argument ∈ saved, SavedReady out argument := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have eq := (Prod.mk.inj (Option.some.inj run)).2
      rw [← eq]
      simp
    | cons argument tail => simp [resolveArguments] at run
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [resolveArguments] at run
    | cons argument arguments =>
      simp only [resolveArguments] at run
      obtain ⟨pair,first,rest⟩ := bind_some _ _ _ run
      rcases pair with ⟨next,head⟩
      obtain ⟨pair,tail,last⟩ := bind_some _ _ _ rest
      rcases pair with ⟨final,savedTail⟩
      have eq := Prod.mk.inj (Option.some.inj last)
      rw [← eq.1,← eq.2]
      have nextReady := resolveArgument_ready s next ty parameter argument head first
      have stable := resolveArguments_stable next final ty parameters arguments savedTail tail
      have readyTail := ih next final arguments savedTail tail
      intro value member
      rcases List.mem_cons.mp member with equal | member
      · subst value
        exact stable_savedReady next final head stable nextReady
      · exact readyTail value member

theorem prepareArguments_of_resolve (s last : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument) (saved : List SavedArgument)
    (run : resolveArguments s ty parameters arguments = some (last,saved)) :
    ∃ out, prepareArguments s ty parameters arguments = some out ∧
      out.objects.heap = s.objects.heap ∧ out.slots.length = saved.length := by
  have ready := resolveArguments_ready s last ty parameters arguments saved run
  obtain ⟨out,prepared,heap,slots⟩ := prepareSaved_ready last saved ready
  have stable := resolveArguments_stable s last ty parameters arguments saved run
  refine ⟨out,?_,?_,slots⟩
  · simp [prepareArguments,run,prepared]
  · exact heap.trans (congrArg Proofs.CppMoveViews.State.heap stable.objects)


theorem resolveArguments_lengths (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument) (saved : List SavedArgument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) :
    saved.length = parameters.length ∧ arguments.length = parameters.length := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have eq := (Prod.mk.inj (Option.some.inj run)).2
      rw [← eq]
      exact ⟨rfl,rfl⟩
    | cons argument tail => simp [resolveArguments] at run
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [resolveArguments] at run
    | cons argument arguments =>
      simp only [resolveArguments] at run
      obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
      rcases pair with ⟨next,head⟩
      obtain ⟨pair,tail,last⟩ := bind_some _ _ _ rest
      rcases pair with ⟨final,savedTail⟩
      have eq := (Prod.mk.inj (Option.some.inj last)).2
      rw [← eq]
      have lengths := ih next final arguments savedTail tail
      simp only [List.length_cons]
      exact ⟨by omega,by omega⟩

theorem prepareArguments_resources (s last out : Context) (ty : Ty)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List Proofs.CppNestedCall.NArgument)
    (saved : List SavedArgument) (resolved : resolveArguments s ty parameters arguments = some (last,saved))
    (prepared : prepareArguments s ty parameters arguments = some out)
    (baseline : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    out.slots.length = parameters.length ∧ work out = work last+1+parameters.length ∧
      out.peak ≤ max last.peak (max last.scalars.peak
        (s.scalars.memory.length-s.scalars.baseMemory+s.slots.length+2*parameters.length)+s.objects.heap.peak) := by
  have ready : prepareSaved last saved = some out := by simpa [prepareArguments,resolved] using prepared
  have stable := resolveArguments_stable s last ty parameters arguments saved resolved
  have lengths := resolveArguments_lengths s last ty parameters arguments saved resolved
  have resources := prepareSaved_resources last out saved ready
  have bound : last.scalars.baseMemory ≤ last.scalars.memory.length := by simpa [stable.baseline,stable.memory] using baseline
  have peak := prepareSaved_peak_linear last out saved ready bound
  have heap := congrArg Proofs.CppMoveViews.State.heap stable.objects
  rw [stable.memory,stable.baseline,stable.slots,heap,lengths.1] at peak
  exact ⟨(prepareSaved_effects last out saved ready).2.trans lengths.1,by simpa [lengths.1] using resources.2.2.1,peak⟩

end Proofs.CppMoveArgumentFacts
