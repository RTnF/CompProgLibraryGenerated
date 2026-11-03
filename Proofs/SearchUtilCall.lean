import Proofs.CountCall
import Proofs.LowerBoundIndexCall

namespace Proofs.SearchUtilCall

/-- `count<int>(v, value, idx_begin, idx_end)`. -/
theorem count_correct : type_of% @Proofs.CountCall.count_correct := @Proofs.CountCall.count_correct

/-- `lower_bound_index<long long>(a, x)`. -/
theorem lower_bound_index_correct : type_of% @Proofs.LowerBoundIndexCall.lower_bound_index_correct :=
  @Proofs.LowerBoundIndexCall.lower_bound_index_correct

end Proofs.SearchUtilCall
