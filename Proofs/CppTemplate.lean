import Proofs.CppState

namespace Proofs.CppTemplate
open Proofs.CppScalar Proofs.CppState

-- Canonical builtin types. Equal widths do not erase C++ conversion rank.
-- Class/enum/floating arguments are intentionally not members of this family.
inductive Integral where
  | boolean | i32 | u32 | signedLong | unsignedLong | signedLongLong | unsignedLongLong
  deriving DecidableEq, Repr

def Integral.type : Integral → Ty
  | .boolean => ⟨1,false,true⟩
  | .i32 => ⟨32,true,false⟩
  | .u32 => ⟨32,false,false⟩
  | .signedLong | .signedLongLong => ⟨64,true,false⟩
  | .unsignedLong | .unsignedLongLong => ⟨64,false,false⟩

def Integral.rank : Integral → Nat
  | .boolean => 0
  | .i32 | .u32 => 1
  | .signedLong | .unsignedLong => 2
  | .signedLongLong | .unsignedLongLong => 3

def Integral.promote : Integral → Integral
  | .boolean => .i32
  | other => other

def Integral.unsigned : Integral → Integral
  | .boolean | .i32 | .u32 => .u32
  | .signedLong | .unsignedLong => .unsignedLong
  | .signedLongLong | .unsignedLongLong => .unsignedLongLong

def commonIntegral (left right : Integral) : Integral :=
  let left := left.promote
  let right := right.promote
  let pair := if left.rank < right.rank then (right,left) else (left,right)
  if left = right then left
  else if pair.1.type.signed = pair.2.type.signed then pair.1
  else if !pair.1.type.signed then pair.1
  else if pair.2.type.width < pair.1.type.width then pair.1
  else pair.1.unsigned

def castExpression (targetPolicy : Bool) (source target : Integral) (operand : Expr) : Expr :=
  let represents := source.type.boolean ||
    (source.type.signed && decide (source.type.width ≤ target.type.width)) ||
    (!source.type.signed && decide (source.type.width < target.type.width))
  if targetPolicy && target.type.signed && !target.type.boolean && !represents then
    .targetCast target.type operand
  else .cast target.type operand

def convertExpression (targetPolicy : Bool) (source target : Integral) (operand : Expr) : Expr :=
  if source = target then operand else castExpression targetPolicy source target operand

inductive TypeExpr where
  | parameter (index : Nat)
  | scalar (type : Integral)
  deriving DecidableEq, Repr

def TypeExpr.resolve (arguments : List Integral) : TypeExpr → Option Integral
  | .parameter i => arguments[i]?
  | .scalar ty => some ty

inductive Comparison where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

def Comparison.operation : Comparison → Binary
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge | .eq => .eq | .ne => .ne

inductive Expression where
  | variable (type : TypeExpr) (slot : Nat)
  | literal (type : TypeExpr) (value : Int)
  | cast (type : TypeExpr) (operand : Expression)
  | comparison (op : Comparison) (left right : Expression)
  deriving DecidableEq, Repr

def Expression.instantiate (arguments : List Integral) (targetPolicy : Bool) :
    Expression → Option (Expr × Integral)
  | .variable ty slot => do
      let t ← ty.resolve arguments
      pure (.variable t.type slot,t)
  | .literal ty value => do
      let t ← ty.resolve arguments
      pure (.literal t.type value,t)
  | .cast ty e => do
      let t ← ty.resolve arguments
      let (operand,source) ← e.instantiate arguments targetPolicy
      pure (castExpression targetPolicy source t operand,t)
  | .comparison op left right => do
      let (a,sourceA) ← left.instantiate arguments targetPolicy
      let (b,sourceB) ← right.instantiate arguments targetPolicy
      let common := commonIntegral sourceA sourceB
      pure (.binary Integral.boolean.type op.operation
        (convertExpression targetPolicy sourceA common a)
        (convertExpression targetPolicy sourceB common b),.boolean)

structure TemplateParameter where
  type : TypeExpr
  reference : Bool
  writable : Bool
  deriving DecidableEq, Repr

inductive Statement where
  | skip
  | scope (body : Statement)
  | sequence (first rest : Statement)
  | branch (condition : Expression) (yes no : Statement)
  | assign (slot : Nat) (value : Expression)
  | ret (value : Expression)
  deriving DecidableEq, Repr

def Statement.instantiate (arguments : List Integral) (targetPolicy : Bool)
    (parameters : List TemplateParameter) (result : Integral) : Statement → Option Stmt
  | .skip => pure .skip
  | .scope body => do pure (.scope (← body.instantiate arguments targetPolicy parameters result))
  | .sequence first rest => do
      pure (.sequence (← first.instantiate arguments targetPolicy parameters result)
        (← rest.instantiate arguments targetPolicy parameters result))
  | .branch condition yes no => do
      let (value,source) ← condition.instantiate arguments targetPolicy
      pure (.branch (convertExpression targetPolicy source .boolean value)
        (← yes.instantiate arguments targetPolicy parameters result)
        (← no.instantiate arguments targetPolicy parameters result))
  | .assign slot e => do
      let parameter ← parameters[slot]?
      if !parameter.writable then none else do
        let target ← parameter.type.resolve arguments
        let (value,source) ← e.instantiate arguments targetPolicy
        pure (.assign slot (convertExpression targetPolicy source target value))
  | .ret e => do
      let (value,source) ← e.instantiate arguments targetPolicy
      pure (.ret (convertExpression targetPolicy source result value))

structure TemplateProgram where
  typeParameters : Nat
  parameters : List TemplateParameter
  resultType : TypeExpr
  body : Statement
  deriving DecidableEq, Repr

def TemplateProgram.instantiate (program : TemplateProgram) (arguments : List Integral)
    (targetPolicy : Bool := false) : Option StateProgram := do
  if arguments.length != program.typeParameters then none else do
    let result ← program.resultType.resolve arguments
    let parameters ← program.parameters.mapM fun p => do
      let t ← p.type.resolve arguments
      pure (⟨t.type,p.reference,p.writable⟩ : Parameter)
    let body ← program.body.instantiate arguments targetPolicy program.parameters result
    pure ⟨parameters,result.type,body⟩

-- Every common arithmetic type is promoted, and retains the larger rank.
theorem common_not_boolean (left right : Integral) :
    commonIntegral left right ≠ .boolean := by cases left <;> cases right <;> decide

theorem common_rank (left right : Integral) :
    (commonIntegral left right).rank = max left.promote.rank right.promote.rank := by
  cases left <;> cases right <;> decide

theorem common_symmetric (left right : Integral) :
    commonIntegral left right = commonIntegral right left := by
  cases left <;> cases right <;> decide

theorem same_integral (type : Integral) : commonIntegral type type = type.promote := by
  cases type <;> decide

theorem convert_same (targetPolicy : Bool) (type : Integral) (operand : Expr) :
    convertExpression targetPolicy type type operand = operand := by simp [convertExpression]

theorem bad_argument_count (program : TemplateProgram) (arguments : List Integral) (policy : Bool)
    (count : arguments.length ≠ program.typeParameters) :
    program.instantiate arguments policy = none := by simp [TemplateProgram.instantiate,count]

end Proofs.CppTemplate
