-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.TreeDistanceInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «tree_distance_std_vector_long_long» : NProgram := ⟨[.vector ⟨64, true, false⟩ false, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true, .scalar ⟨32, true, false⟩ false true],.scalar ⟨64, true, false⟩,(.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 1))))) (.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 2))))) (.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))))) (.sequence (.primitive (.ret (.binary ⟨64, true, false⟩ .sub (.binary ⟨64, true, false⟩ .add (.variable ⟨64, true, false⟩ 4) (.variable ⟨64, true, false⟩ 5)) (.binary ⟨64, true, false⟩ .mul (.variable ⟨64, true, false⟩ 6) (.cast ⟨64, true, false⟩ (.literal ⟨32, true, false⟩ (2))))))) (.primitive .skip)))))⟩

end Proofs.TreeDistanceInstance
