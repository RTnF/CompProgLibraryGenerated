-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.TreeAncestorInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «tree_ancestor» : NProgram := ⟨[.nested ⟨32, true, false⟩ false, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (1)))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .le (.variable ⟨32, true, false⟩ 4) (.variable ⟨32, true, false⟩ 2)) (.sequence (.scope (.sequence (.branch (.binary ⟨1, false, true⟩ .eq (.divrem ⟨32, true, false⟩ true (.divrem ⟨32, true, false⟩ false (.variable ⟨32, true, false⟩ 2) (.variable ⟨32, true, false⟩ 4)) (.literal ⟨32, true, false⟩ (2))) (.literal ⟨32, true, false⟩ (1))) (.sequence (.scope (.sequence (.primitive (.assign 1 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.row (.local 0) (.integer ⟨32, true, false⟩) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 1))))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip)) (.sequence (.primitive (.assign 4 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .mul (.variable ⟨32, true, false⟩ 4) (.literal ⟨32, true, false⟩ (2))))) (.sequence (.primitive (.assign 3 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 3) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 1))) (.primitive .skip)))))⟩

end Proofs.TreeAncestorInstance
