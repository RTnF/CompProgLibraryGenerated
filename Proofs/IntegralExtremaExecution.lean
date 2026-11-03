import Proofs.IntegralExtrema
import Proofs.ExtremaReferences
import Proofs.CppTargetCast

namespace Proofs.IntegralExtremaExecution
open Proofs.CppScalar Proofs.CppState Proofs.CppTemplate

def schema (left right : Ty) (condition assignment : Expr) : StateProgram :=
  ⟨[⟨left,true,true⟩,⟨right,true,false⟩],Integral.boolean.type,
    .scope (.sequence (.branch condition
      (.scope (.scope (.sequence (.assign 0 assignment)
        (.sequence (.ret (.cast Integral.boolean.type (.literal Integral.i32.type 1))) .skip)))) .skip)
      (.sequence (.ret (.cast Integral.boolean.type (.literal Integral.i32.type 0))) .skip))⟩

-- Conversion preconditions are separate from the control-flow proof. Only the
-- selected assignment needs to be representable under the checked policy.
theorem schema_call (left right : Ty) (condition assignment : Expr)
    (memory : List Cell) (p q : Nat) (a b c : Int) (update : Bool)
    (hp : memory[p]? = some ⟨left,a⟩) (hq : memory[q]? = some ⟨right,b⟩)
    (ha : left.valid a = true) (hb : right.valid b = true)
    (hc : update = true → left.valid c = true)
    (evaluated : condition.eval [a,b] = some ⟨if update then 1 else 0,condition.nodes⟩)
    (assigned : update = true → assignment.eval [a,b] = some ⟨c,assignment.nodes⟩)
    (conditionSize : 3 ≤ condition.nodes) (assignmentSize : assignment.nodes ≤ condition.nodes) :
    (schema left right condition assignment).call memory [.reference p,.reference q] =
      some ⟨if update then 1 else 0,
        if update then memory.set p ⟨left,c⟩ else memory,
        condition.nodes + (if update then assignment.nodes + 5 else 4),2 + condition.nodes⟩ := by
  have boundP : p < memory.length := (List.getElem?_eq_some_iff.mp hp).1
  have boundQ : q < memory.length := (List.getElem?_eq_some_iff.mp hq).1
  have cellP : memory[p] = ⟨left,a⟩ := (List.getElem?_eq_some_iff.mp hp).2
  have cellQ : memory[q] = ⟨right,b⟩ := (List.getElem?_eq_some_iff.mp hq).2
  have boolValid0 : Ty.valid ⟨1,false,true⟩ 0 = true := by decide
  have boolValid1 : Ty.valid ⟨1,false,true⟩ 1 = true := by decide
  have intValid0 : Ty.valid ⟨32,true,false⟩ 0 = true := by decide
  have intValid1 : Ty.valid ⟨32,true,false⟩ 1 = true := by decide
  have boolConvert0 : Ty.convert ⟨1,false,true⟩ 0 = some 0 := rfl
  have boolConvert1 : Ty.convert ⟨1,false,true⟩ 1 = some 1 := rfl
  have maxCond : max 2 (2 + condition.nodes) = 2 + condition.nodes := by omega
  have maxReturn : max (2 + condition.nodes) 4 = 2 + condition.nodes := by omega
  cases update
  · simp [schema,StateProgram.call,bindArguments,bindArgument,Stmt.run,State.evaluate,
      State.environment,State.observe,Expr.eval,Expr.nodes,
      boolValid0,intValid0,intValid1,boolConvert0,boolConvert1,cellP,cellQ,ha,hb,boundP,boundQ,
      evaluated,Integral.type,maxCond,maxReturn,Nat.add_comm] <;> omega
  · have validC := hc rfl
    have validQ : ((memory.set p ⟨left,c⟩)[q]'(by simpa)).type.valid
        ((memory.set p ⟨left,c⟩)[q]'(by simpa)).value = true := by
      by_cases same : p = q
      · subst q; simp [List.getElem_set_self,validC]
      · have newQ : (memory.set p ⟨left,c⟩)[q]? = some ⟨right,b⟩ := by
          simp [List.getElem?_set_ne same,hq]
        rw [(List.getElem?_eq_some_iff.mp newQ).2]; exact hb
    have converted := Ty.convert_of_valid left c validC
    have takeUpdated : (memory.set p ⟨left,c⟩).take memory.length = memory.set p ⟨left,c⟩ := by
      simpa using List.take_length (l := memory.set p ⟨left,c⟩)
    simp [schema,StateProgram.call,bindArguments,bindArgument,Stmt.run,State.evaluate,
      State.environment,State.observe,Expr.eval,Expr.nodes,
      boolValid1,intValid0,intValid1,boolConvert0,boolConvert1,cellP,cellQ,ha,hb,boundP,boundQ,
      evaluated,assigned rfl,Integral.type,maxCond,
      validC,validQ,converted,takeUpdated,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

-- Value-level conversion specification, independent of expression evaluation.
def convertValue (policy : Bool) (source target : Integral) (value : Int) : Option Int :=
  if source = target then some value else
    let represents := source.type.boolean ||
      (source.type.signed && decide (source.type.width ≤ target.type.width)) ||
      (!source.type.signed && decide (source.type.width < target.type.width))
    if policy && target.type.signed && !target.type.boolean && !represents then
      target.type.targetConvert value
    else target.type.convert value

def conversionWork (source target : Integral) : Nat := if source = target then 0 else 1

theorem convert_eval (policy : Bool) (source target : Integral) (e : Expr)
    (env : List Int) (value converted : Int) (work : Nat)
    (evaluated : e.eval env = some ⟨value,work⟩)
    (conversion : convertValue policy source target value = some converted) :
    (convertExpression policy source target e).eval env =
      some ⟨converted,work + conversionWork source target⟩ := by
  cases source <;> cases target <;> cases policy <;>
    simp_all [convertValue,convertExpression,castExpression,Integral.type,Expr.eval,conversionWork]

theorem conversion_nodes (policy : Bool) (source target : Integral) (e : Expr) :
    (convertExpression policy source target e).nodes = e.nodes + conversionWork source target := by
  unfold convertExpression conversionWork
  split
  · simp
  · unfold castExpression; dsimp only; split <;> simp [Expr.nodes]

theorem scalar_conversion_valid (ty : Ty) (value converted : Int)
    (conversion : ty.convert value = some converted) : ty.valid converted = true := by
  unfold Ty.convert at conversion
  split at conversion
  · simp only [Option.some.injEq] at conversion
    rw [← conversion]
    simp only [Ty.valid]; simp_all
    by_cases zero : value = 0 <;> simp_all
  · split at conversion
    · split at conversion
      · simp_all
      · simp_all
    · simp only [Option.some.injEq] at conversion
      rw [← conversion]
      have low := Int.emod_nonneg value (by have h := (Int.pow_pos (by decide) : (0 : Int) < 2 ^ ty.width); omega : (2 ^ ty.width : Int) ≠ 0)
      have high := Int.emod_lt_of_pos value (Int.pow_pos (by decide) : (0 : Int) < 2 ^ ty.width)
      simp_all [Ty.valid]

theorem conversion_valid (policy : Bool) (source target : Integral) (value converted : Int)
    (valid : source.type.valid value = true)
    (conversion : convertValue policy source target value = some converted) :
    target.type.valid converted = true := by
  by_cases same : source = target
  · subst target
    have eq : value = converted := by simpa [convertValue] using conversion
    simpa [← eq] using valid
  · unfold convertValue at conversion
    simp only [same,ite_false] at conversion
    split at conversion
    · cases target
      all_goals try {simp_all [Integral.type]}
      all_goals simp only [Integral.type,Ty.targetConvert] at conversion
      all_goals simp only [Bool.not_false,Bool.and_self,ite_true,
        Nat.reduceBEq,Bool.or_true,Bool.true_or,Option.some.injEq] at conversion
      all_goals subst converted
      all_goals first
        | exact (Proofs.CppTargetCast.targetConvert_i32_valid value).2
        | exact (Proofs.CppTargetCast.targetConvert_i64_valid value).2
    · exact scalar_conversion_valid target.type value converted conversion

def condition (left right : Integral) (policy minimum : Bool) : Expr :=
  let common := commonIntegral left right
  let a := convertExpression policy left common (.variable left.type 0)
  let b := convertExpression policy right common (.variable right.type 1)
  .binary Integral.boolean.type .lt (if minimum then b else a) (if minimum then a else b)

def assignment (left right : Integral) (policy : Bool) : Expr :=
  convertExpression policy right left (.variable right.type 1)

def program (minimum : Bool) : TemplateProgram :=
  if minimum then IntegralExtrema.chmin else IntegralExtrema.chmax

theorem source_schema (left right : Integral) (policy minimum : Bool) :
    (program minimum).instantiate [left,right] policy =
      some (schema left.type right.type (condition left right policy minimum)
        (assignment left right policy)) := by
  cases left <;> cases right <;> cases policy <;> cases minimum <;> rfl

theorem expression_sizes (left right : Integral) (policy minimum : Bool) :
    3 ≤ (condition left right policy minimum).nodes ∧
    (condition left right policy minimum).nodes ≤ 5 ∧
    (assignment left right policy).nodes ≤ 2 ∧
    (assignment left right policy).nodes ≤ (condition left right policy minimum).nodes := by
  cases left <;> cases right <;> cases policy <;> cases minimum <;> decide

theorem condition_eval (left right : Integral) (policy minimum : Bool) (a b ac bc : Int)
    (ha : left.type.valid a = true) (hb : right.type.valid b = true)
    (ca : convertValue policy left (commonIntegral left right) a = some ac)
    (cb : convertValue policy right (commonIntegral left right) b = some bc) :
    (condition left right policy minimum).eval [a,b] =
      some ⟨if (if minimum then bc < ac else ac < bc) then 1 else 0,
        (condition left right policy minimum).nodes⟩ := by
  have va : (Expr.variable left.type 0).eval [a,b] = some ⟨a,1⟩ := by simp [Expr.eval,ha]
  have vb : (Expr.variable right.type 1).eval [a,b] = some ⟨b,1⟩ := by simp [Expr.eval,hb]
  have ea := convert_eval policy left (commonIntegral left right) _ [a,b] a ac 1 va ca
  have eb := convert_eval policy right (commonIntegral left right) _ [a,b] b bc 1 vb cb
  have boolConversion (predicate : Prop) [Decidable predicate] :
      Integral.boolean.type.convert (if predicate then 1 else 0) =
        some (if predicate then 1 else 0) := by
    by_cases h : predicate <;> simp [h,Integral.type,Ty.convert]
  cases minimum <;>
    simp [condition,Expr.eval,ea,eb,binaryValue,boolConversion,
      conversion_nodes,Expr.nodes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem assignment_eval (left right : Integral) (policy : Bool) (a b c : Int)
    (hb : right.type.valid b = true) (converted : convertValue policy right left b = some c) :
    (assignment left right policy).eval [a,b] = some ⟨c,(assignment left right policy).nodes⟩ := by
  have vb : (Expr.variable right.type 1).eval [a,b] = some ⟨b,1⟩ := by simp [Expr.eval,hb]
  simpa [assignment,conversion_nodes,Expr.nodes] using
    convert_eval policy right left _ [a,b] b c 1 vb converted

-- A generated-source call theorem for every supported integral type pair.
-- The hypotheses describe scalar conversions, rather than assumed execution.
theorem call_correct (left right : Integral) (policy minimum : Bool)
    (memory : List Cell) (p q : Nat) (a b ac bc c : Int)
    (hp : memory[p]? = some ⟨left.type,a⟩) (hq : memory[q]? = some ⟨right.type,b⟩)
    (ha : left.type.valid a = true) (hb : right.type.valid b = true)
    (ca : convertValue policy left (commonIntegral left right) a = some ac)
    (cb : convertValue policy right (commonIntegral left right) b = some bc)
    (cc : (if minimum then bc < ac else ac < bc) → convertValue policy right left b = some c) :
    ((program minimum).instantiate [left,right] policy).bind
        (fun model => model.call memory [.reference p,.reference q]) =
      some ⟨if (if minimum then bc < ac else ac < bc) then 1 else 0,
        if (if minimum then bc < ac else ac < bc) then memory.set p ⟨left.type,c⟩ else memory,
        (condition left right policy minimum).nodes +
          (if (if minimum then bc < ac else ac < bc) then (assignment left right policy).nodes + 5 else 4),
        2 + (condition left right policy minimum).nodes⟩ := by
  rw [source_schema]
  simp only [Option.bind_some]
  have sizes := expression_sizes left right policy minimum
  simpa only [decide_eq_true_eq] using
    schema_call left.type right.type (condition left right policy minimum)
      (assignment left right policy) memory p q a b c
      (decide (if minimum then bc < ac else ac < bc)) hp hq ha hb
      (by intro update; exact conversion_valid policy right left b c hb (cc (by simpa using update)))
      (by simpa using condition_eval left right policy minimum a b ac bc ha hb ca cb)
      (by intro update; exact assignment_eval left right policy a b c hb (cc (by simpa using update)))
      sizes.1 sizes.2.2.2

set_option backward.isDefEq.respectTransparency false in
theorem common_conversion_total (left right : Integral) (policy : Bool) (a : Int)
    (ha : left.type.valid a = true) :
    (convertValue policy left (commonIntegral left right) a).isSome = true := by
  cases left <;> cases right <;> cases policy
  all_goals simp [Integral.type,Ty.valid] at ha
  all_goals simp_all [convertValue,commonIntegral,Integral.type,Integral.rank,Integral.promote,
      Integral.unsigned,Ty.convert,Ty.valid,decide_eq_true_eq]
  all_goals try simp_all only [decide_eq_true_eq]
  all_goals omega

theorem execution_bounds (left right : Integral) (policy minimum update : Bool) :
    (condition left right policy minimum).nodes +
      (if update then (assignment left right policy).nodes + 5 else 4) ≤ 12 ∧
    2 + (condition left right policy minimum).nodes ≤ 7 := by
  have sizes := expression_sizes left right policy minimum
  cases update <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

set_option backward.isDefEq.respectTransparency false in
theorem target_conversion_total (source target : Integral) (value : Int)
    (valid : source.type.valid value = true) :
    (convertValue true source target value).isSome = true := by
  cases source <;> cases target
  all_goals simp [Integral.type,Ty.valid] at valid
  all_goals simp_all [convertValue,Integral.type,Ty.convert,Ty.targetConvert,Ty.valid,decide_eq_true_eq]
  all_goals try simp_all only [decide_eq_true_eq]
  all_goals omega

theorem call_target_total (left right : Integral) (minimum : Bool)
    (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨left.type,a⟩) (hq : memory[q]? = some ⟨right.type,b⟩)
    (ha : left.type.valid a = true) (hb : right.type.valid b = true) :
    ∃ result : CallResult,
      ((program minimum).instantiate [left,right] true).bind
        (fun model => model.call memory [.reference p,.reference q]) = some result ∧
      result.work ≤ 12 ∧ result.peak ≤ 7 := by
  obtain ⟨ac,ca⟩ : ∃ ac, convertValue true left (commonIntegral left right) a = some ac := by
    cases converted : convertValue true left (commonIntegral left right) a with
    | none => have total := common_conversion_total left right true a ha; simp [converted] at total
    | some v => exact ⟨v,rfl⟩
  obtain ⟨bc,cb⟩ : ∃ bc, convertValue true right (commonIntegral left right) b = some bc := by
    cases converted : convertValue true right (commonIntegral left right) b with
    | none =>
        have total := common_conversion_total right left true b hb
        rw [common_symmetric right left] at total
        simp [converted] at total
    | some v => exact ⟨v,rfl⟩
  obtain ⟨c,cc⟩ : ∃ c, convertValue true right left b = some c := by
    cases converted : convertValue true right left b with
    | none => have total := target_conversion_total right left b hb; simp [converted] at total
    | some v => exact ⟨v,rfl⟩
  refine ⟨_,call_correct left right true minimum memory p q a b ac bc c hp hq ha hb ca cb
    (fun _ => cc),?_⟩
  simpa only [decide_eq_true_eq] using
    execution_bounds left right true minimum (decide (if minimum then bc < ac else ac < bc))

theorem same_common_value (ty : Integral) (policy : Bool) (value : Int)
    (valid : ty.type.valid value = true) :
    convertValue policy ty (commonIntegral ty ty) value = some value := by
  cases ty <;> cases policy <;>
    simp_all [convertValue,commonIntegral,Integral.type,Integral.promote,
      Ty.convert,Ty.valid,decide_eq_true_eq] <;> omega

theorem same_type_call (ty : Integral) (policy minimum : Bool)
    (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨ty.type,a⟩) (hq : memory[q]? = some ⟨ty.type,b⟩)
    (ha : ty.type.valid a = true) (hb : ty.type.valid b = true) :
    ((program minimum).instantiate [ty,ty] policy).bind
        (fun model => model.call memory [.reference p,.reference q]) =
      some ⟨if (if minimum then b < a else a < b) then 1 else 0,
        if (if minimum then b < a else a < b) then memory.set p ⟨ty.type,b⟩ else memory,
        (condition ty ty policy minimum).nodes +
          (if (if minimum then b < a else a < b) then 6 else 4),
        2 + (condition ty ty policy minimum).nodes⟩ := by
  simpa [assignment,conversion_nodes,conversionWork,Expr.nodes] using
    call_correct ty ty policy minimum memory p q a b a b b hp hq ha hb
      (same_common_value ty policy a ha) (same_common_value ty policy b hb)
      (by intro _; simp [convertValue])

theorem result_frame (memory : List Cell) (p : Nat) (ty : Ty) (a c : Int) (update : Bool)
    (hp : memory[p]? = some ⟨ty,a⟩) :
    (if update then memory.set p ⟨ty,c⟩ else memory).length = memory.length ∧
    (if update then memory.set p ⟨ty,c⟩ else memory)[p]? =
      some ⟨ty,if update then c else a⟩ ∧
    ∀ r, r ≠ p → (if update then memory.set p ⟨ty,c⟩ else memory)[r]? = memory[r]? := by
  have boundP : p < memory.length := (List.getElem?_eq_some_iff.mp hp).1
  cases update
  · simp [hp]
  · refine ⟨by simp,by simp [boundP],?_⟩
    intro r different
    simp [List.getElem?_set_ne (Ne.symm different)]

theorem same_type_alias (ty : Integral) (policy minimum : Bool)
    (memory : List Cell) (p : Nat) (a : Int)
    (hp : memory[p]? = some ⟨ty.type,a⟩) (ha : ty.type.valid a = true) :
    ((program minimum).instantiate [ty,ty] policy).bind
        (fun model => model.call memory [.reference p,.reference p]) =
      some ⟨0,memory,(condition ty ty policy minimum).nodes + 4,
        2 + (condition ty ty policy minimum).nodes⟩ := by
  simpa using same_type_call ty policy minimum memory p p a a hp hp ha ha

end Proofs.IntegralExtremaExecution
