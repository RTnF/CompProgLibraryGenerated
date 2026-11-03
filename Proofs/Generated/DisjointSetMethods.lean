import Proofs.CppMoveCallBindings
import Proofs.CppMoveObjectReceiver
-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.Generated.DisjointSetMethods.Methods
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «DisjointSet_getNum» : NProgram := ⟨[.vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ true true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 2))) (.primitive .skip))⟩

end Proofs.Generated.DisjointSetMethods.Methods

namespace Proofs.Generated.DisjointSetMethods
open Proofs.CppMoveContext Proofs.CppNestedCall Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppLoop
def sourceSHA256 : String := "20c9daaa3b92a291c410bbdde8e01444e6c419bf57eb41bf211b9a5d9401e254"
def fieldNames : List String := ["ps", "_n", "num_groups"]
def coverage : String := "selected_context_method_receivers"
def declaredFieldNames : List String := ["_n", "ps", "num_groups"]
def fieldPermutation : List Nat := [1, 0, 2]
def selectedMethods : List String := ["getNum"]
def availableMethods : List String := ["unite", "same", "root", "size", "getNum"]
def dependencyMethods : List String := []
def «DisjointSet_getNum_arguments» (receiver : ObjectRef) (arguments : List NArgument) : Option (List NArgument) := do
  if receiver.scalarSlots.length != 2 || arguments.length != 0 then none else pure ()
  let slot0 ← receiver.scalarSlots[0]?
  let slot1 ← receiver.scalarSlots[1]?
  pure ([.vectorReference receiver.vectorSlot, .value (.variable ⟨32, true, false⟩ slot0), .scalarReference slot1] ++ arguments)
theorem «DisjointSet_getNum_arguments_of_fields» (receiver : ObjectRef) (arguments : List NArgument) (slot0 slot1 : Nat)
    (fields : receiver.scalarSlots = [slot0,slot1]) (arity : arguments.length = 0) :
    «DisjointSet_getNum_arguments» receiver arguments = some ([.vectorReference receiver.vectorSlot, .value (.variable ⟨32, true, false⟩ slot0), .scalarReference slot1] ++ arguments) := by
  simp [«DisjointSet_getNum_arguments»,fields,arity]
def «DisjointSet_getNum_callFuel» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments : List NArgument) : Outcome (Context × Ret) := do
  let prepared ← liftChecked («DisjointSet_getNum_arguments» receiver arguments)
  Proofs.CppMoveCallBindings.callFuel Methods.«DisjointSet_getNum» fuel caller ⟨32, true, false⟩ prepared
theorem «DisjointSet_getNum_call_of_arguments» (fuel : Nat) (caller : Context) (receiver : ObjectRef) (arguments expanded : List NArgument)
    (mapped : «DisjointSet_getNum_arguments» receiver arguments = some expanded) :
    «DisjointSet_getNum_callFuel» fuel caller receiver arguments = Proofs.CppMoveCallBindings.callFuel Methods.«DisjointSet_getNum» fuel caller ⟨32, true, false⟩ expanded := by
  simp [«DisjointSet_getNum_callFuel»,mapped,liftChecked,Bind.bind,Outcome.bind]
theorem «DisjointSet_getNum_eligible» : Proofs.CppMoveCallRestore.eligible Methods.«DisjointSet_getNum» = true := by decide +kernel
end Proofs.Generated.DisjointSetMethods
