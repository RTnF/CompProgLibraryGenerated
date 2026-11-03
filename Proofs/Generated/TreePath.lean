-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.TreePathInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «tree_path» : NProgram := ⟨[.vector ⟨32, true, false⟩ false, .vector ⟨32, true, false⟩ true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.variable ⟨32, true, false⟩ 3))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨32, true, false⟩ 5) (.variable ⟨32, true, false⟩ 2)) (.sequence (.scope (.sequence (.primitive (.write (.local 1) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4)) (.variable ⟨32, true, false⟩ 5))) (.sequence (.primitive (.assign 4 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 4) (.literal ⟨32, true, false⟩ (1))))) (.sequence (.primitive (.assign 5 ⟨32, true, false⟩ (.read ⟨32, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 5))))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.write (.local 1) ⟨32, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4)) (.variable ⟨32, true, false⟩ 2))) (.sequence (.primitive (.ret (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 4) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip))))))⟩

end Proofs.TreePathInstance
