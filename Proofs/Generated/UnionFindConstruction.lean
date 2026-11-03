-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.UnionFindConstructionInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

-- Initializer/body stage: runFuel retains fields; callFuel retires them.
def «UnionFind_construct0» : NProgram := ⟨[],.unit,(.sequence (.primitive (.declareVector ⟨32, true, false⟩ true)) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.primitive .skip))))⟩
def «UnionFind_construct0_fields» : List (String × Nat) := [("_ps",0), ("_num_groups",1), ("_n",2)]
-- Initializer/body stage: runFuel retains fields; callFuel retires them.
def «UnionFind_construct1» : NProgram := ⟨[.scalar ⟨32, true, false⟩ false true],.unit,(.sequence (.primitive (.fillVector ⟨32, true, false⟩ true (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 0)) (.unary ⟨32, true, false⟩ .neg (.literal ⟨32, true, false⟩ (1))))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 0))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 0))) (.sequence (.primitive (.check (.binary ⟨1, false, true⟩ .ge (.variable ⟨32, true, false⟩ 0) (.literal ⟨32, true, false⟩ (0))))) (.primitive .skip)))))⟩
def «UnionFind_construct1_fields» : List (String × Nat) := [("_ps",1), ("_num_groups",2), ("_n",3)]

end Proofs.UnionFindConstructionInstance
