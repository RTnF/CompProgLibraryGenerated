namespace Proofs.CppScalar

structure Ty where
  width : Nat
  signed : Bool
  boolean : Bool
deriving DecidableEq, Repr

def Ty.valid (t : Ty) (v : Int) : Bool :=
  if t.boolean then v == 0 || v == 1
  else if t.signed then decide (-(2 ^ (t.width - 1) : Int) ≤ v ∧ v < 2 ^ (t.width - 1))
  else decide (0 ≤ v ∧ v < 2 ^ t.width)

-- Signed narrowing outside the representable range is intentionally refused;
-- C++17 leaves that conversion implementation-defined. Unsigned arithmetic wraps.
def Ty.convert (t : Ty) (v : Int) : Option Int :=
  if t.boolean then some (if v == 0 then 0 else 1)
  else if t.signed then if t.valid v then some v else none
  else some (v % (2 ^ t.width))

-- Target-compiler conversion contract, enabled explicitly by the frontend.
-- This rule is never used by arithmetic operators or checkedDivRem.
def signedDecode (width : Nat) (v : Int) : Int :=
  let r := v % (2 ^ width)
  if r < 2 ^ (width-1) then r else r-2 ^ width

def Ty.targetConvert (t : Ty) (v : Int) : Option Int :=
  if t.signed && !t.boolean then
    if t.width == 32 || t.width == 64 then some (signedDecode t.width v) else none
  else t.convert v

theorem Ty.convert_of_valid (ty : Ty) (v : Int) (h : ty.valid v = true) :
    ty.convert v = some v := by
  by_cases hb : ty.boolean = true
  · have hv : v = 0 ∨ v = 1 := by simpa [Ty.valid, hb] using h
    rcases hv with hv | hv <;> subst v <;> simp [Ty.convert, hb]
  · by_cases hs : ty.signed = true
    · simp [Ty.convert, hb, hs, h]
    · have hv : 0 ≤ v ∧ v < 2 ^ ty.width := by simpa [Ty.valid, hb, hs] using h
      simp [Ty.convert, hb, hs, Int.emod_eq_of_lt hv.1 hv.2]

inductive Unary where | plus | neg | not
deriving DecidableEq, Repr
-- The bitwise and shift operators are defined for the nonnegative operands of unsigned types;
-- the common generator rejects them for signed types and for non-literal shift counts.
inductive Binary where | add | sub | mul | lt | le | gt | ge | eq | ne | band | bor | bxor | shl | shr
deriving DecidableEq, Repr
inductive Expr where
  | literal (type : Ty) (value : Int)
  | variable (type : Ty) (slot : Nat)
  | cast (type : Ty) (operand : Expr)
  | unary (type : Ty) (op : Unary) (operand : Expr)
  | binary (type : Ty) (op : Binary) (left right : Expr)
  | divrem (type : Ty) (remainder : Bool) (left right : Expr)
  | targetCast (type : Ty) (operand : Expr)
deriving DecidableEq, Repr

structure Result where
  value : Int
  work : Nat
deriving DecidableEq, Repr

def unaryValue (op : Unary) (v : Int) : Int :=
  match op with
  | .plus => v
  | .neg => -v
  | .not => if v == 0 then 1 else 0

def binaryValue (op : Binary) (a b : Int) : Int :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .lt => if a < b then 1 else 0
  | .le => if a ≤ b then 1 else 0
  | .gt => if a > b then 1 else 0
  | .ge => if a ≥ b then 1 else 0
  | .eq => if a == b then 1 else 0
  | .ne => if a != b then 1 else 0
  | .band => ((a.toNat &&& b.toNat : Nat) : Int)
  | .bor => ((a.toNat ||| b.toNat : Nat) : Int)
  | .bxor => ((a.toNat ^^^ b.toNat : Nat) : Int)
  | .shl => a * 2 ^ b.toNat
  | .shr => ((a.toNat >>> b.toNat : Nat) : Int)

-- C++ truncates toward zero. A nonrepresentable quotient invalidates both
-- division and remainder (including signed MIN % -1).
def checkedDivRem (ty : Ty) (remainder : Bool) (a b : Int) : Option Int :=
  if b == 0 then none
  else if !(ty.valid (a.tdiv b)) then none
  else ty.convert (if remainder then a.tmod b else a.tdiv b)

def Expr.eval (environment : List Int) : Expr → Option Result
  | .literal ty v => do
      if ty.valid v then some ⟨v, 1⟩ else none
  | .variable ty slot => do
      let v ← environment[slot]?
      if ty.valid v then some ⟨v, 1⟩ else none
  | .cast ty operand => do
      let v ← operand.eval environment
      let result ← ty.convert v.value
      some ⟨result, v.work + 1⟩
  | .targetCast ty operand => do
      let v ← operand.eval environment
      let result ← ty.targetConvert v.value
      some ⟨result, v.work + 1⟩
  | .unary ty op operand => do
      let v ← operand.eval environment
      let result ← ty.convert (unaryValue op v.value)
      some ⟨result, v.work + 1⟩
  | .binary ty op left right => do
      let a ← left.eval environment
      let b ← right.eval environment
      let result ← ty.convert (binaryValue op a.value b.value)
      some ⟨result, a.work + b.work + 1⟩
  | .divrem ty remainder left right => do
      let a ← left.eval environment
      let b ← right.eval environment
      let result ← checkedDivRem ty remainder a.value b.value
      some ⟨result, a.work + b.work + 1⟩

structure Program where
  parameters : List Ty
  locals : List Expr
  result : Expr
deriving DecidableEq, Repr

def evalLocals (environment : List Int) (work : Nat) : List Expr → Option (List Int × Nat)
  | [] => some (environment, work)
  | e :: rest => do
      let value ← e.eval environment
      evalLocals (environment ++ [value.value]) (work + value.work + 1) rest

def Program.call (p : Program) (arguments : List Int) : Option Result := do
  if arguments.length != p.parameters.length then none
  else if !(p.parameters.zip arguments).all (fun (t, v) => t.valid v) then none
  else
    let (env, work) ← evalLocals arguments 0 p.locals
    let result ← p.result.eval env
    some ⟨result.value, work + result.work + 1⟩

def Expr.nodes : Expr → Nat
  | .literal .. | .variable .. => 1
  | .cast _ e | .targetCast _ e | .unary _ _ e => e.nodes + 1
  | .binary _ _ a b | .divrem _ _ a b => a.nodes + b.nodes + 1

theorem Expr.eval_work (e : Expr) (env : List Int) (r : Result)
    (h : e.eval env = some r) : r.work = e.nodes := by
  induction e generalizing r with
  | literal ty v =>
      simp only [eval] at h
      split at h
      · cases Option.some.inj h
        rfl
      · simp at h
  | «variable» ty slot =>
      cases hv : env[slot]? with
      | none => simp [eval, hv] at h
      | some v =>
          simp [eval, hv] at h
          cases h.2
          rfl
  | cast ty e ih =>
      cases he : e.eval env with
      | none => simp [eval, he] at h
      | some v =>
          cases hc : ty.convert v.value with
          | none => simp [eval, he, hc] at h
          | some value =>
              simp [eval, he, hc] at h
              subst r
              simp [nodes, ih v he]
  | targetCast ty e ih =>
      cases he : e.eval env with
      | none => simp [eval, he] at h
      | some v =>
          cases hc : ty.targetConvert v.value with
          | none => simp [eval, he, hc] at h
          | some value =>
              simp [eval, he, hc] at h
              subst r
              simp [nodes, ih v he]
  | unary ty op e ih =>
      cases he : e.eval env with
      | none => simp [eval, he] at h
      | some v =>
          cases hc : ty.convert (unaryValue op v.value) with
          | none => simp [eval, he, hc] at h
          | some value =>
              simp [eval, he, hc] at h
              subst r
              simp [nodes, ih v he]
  | binary ty op a b iha ihb =>
      cases ha : a.eval env with
      | none => simp [eval, ha] at h
      | some x =>
          cases hb : b.eval env with
          | none => simp [eval, ha, hb] at h
          | some y =>
              cases hc : ty.convert (binaryValue op x.value y.value) with
              | none => simp [eval, ha, hb, hc] at h
              | some value =>
                  simp [eval, ha, hb, hc] at h
                  subst r
                  simp [nodes, iha x ha, ihb y hb]
  | divrem ty remainder a b iha ihb =>
      cases ha : a.eval env with
      | none => simp [eval, ha] at h
      | some x =>
          cases hb : b.eval env with
          | none => simp [eval, ha, hb] at h
          | some y =>
              cases hc : checkedDivRem ty remainder x.value y.value with
              | none => simp [eval, ha, hb, hc] at h
              | some value =>
                  simp [eval, ha, hb, hc] at h
                  subst r
                  simp [nodes, iha x ha, ihb y hb]

theorem checkedDivRem_success_safe (ty : Ty) (remainder : Bool) (a b r : Int)
    (h : checkedDivRem ty remainder a b = some r) :
    b ≠ 0 ∧ ty.valid (a.tdiv b) = true := by
  unfold checkedDivRem at h
  split at h
  · contradiction
  · rename_i hb
    split at h
    · contradiction
    · rename_i hq
      simpa using And.intro hb hq

theorem checkedDivRem_zero (ty : Ty) (remainder : Bool) (a : Int) :
    checkedDivRem ty remainder a 0 = none := by
  simp [checkedDivRem]

theorem checkedDivRem_invalid_quotient (ty : Ty) (remainder : Bool) (a b : Int)
    (h : ty.valid (a.tdiv b) = false) : checkedDivRem ty remainder a b = none := by
  simp [checkedDivRem, h]

theorem checkedDivRem_division_exact (ty : Ty) (a b : Int) (hb : b ≠ 0)
    (hq : ty.valid (a.tdiv b) = true) :
    checkedDivRem ty false a b = some (a.tdiv b) := by
  simp [checkedDivRem, hb, hq, Ty.convert_of_valid ty _ hq]

theorem checkedDivRem_remainder_exact (ty : Ty) (a b : Int) (hb : b ≠ 0)
    (hq : ty.valid (a.tdiv b) = true) (hr : ty.valid (a.tmod b) = true) :
    checkedDivRem ty true a b = some (a.tmod b) := by
  simp [checkedDivRem, hb, hq, Ty.convert_of_valid ty _ hr]

theorem checkedDivRem_signed_min_neg_one (width : Nat) (remainder : Bool) :
    checkedDivRem ⟨width, true, false⟩ remainder
      (-(2 ^ (width - 1) : Int)) (-1) = none := by
  apply checkedDivRem_invalid_quotient
  simp [Ty.valid, Int.tdiv_neg, Int.tdiv_one]

end Proofs.CppScalar
