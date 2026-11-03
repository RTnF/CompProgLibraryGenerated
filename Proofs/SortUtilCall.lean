import Proofs.InvPermCall
import Proofs.CompressCall
import Proofs.SortVectorCall
import Proofs.DedupVectorCall

namespace Proofs.SortUtilCall

/-- `inv_perm<int>(v)`. -/
theorem inv_perm_correct : type_of% @Proofs.InvPermCall.inv_perm_correct := @Proofs.InvPermCall.inv_perm_correct

/-- The specification of the vector `inv_perm` builds. -/
theorem inv_perm_spec : type_of% @Proofs.InvPermCall.inv_perm_spec := @Proofs.InvPermCall.inv_perm_spec

/-- `compress<long long>(x, unzip, cmp)`. -/
theorem compress_correct : type_of% @Proofs.CompressCall.compress_correct := @Proofs.CompressCall.compress_correct

/-- `sort_vector<long long>(x)` under the `std::sort` contract. -/
theorem sort_vector_correct : type_of% @Proofs.SortVectorCall.sort_vector_correct := @Proofs.SortVectorCall.sort_vector_correct

theorem sorted_result_spec : type_of% @Proofs.SortVectorCall.sorted_result_spec := @Proofs.SortVectorCall.sorted_result_spec

theorem sort_vector_work_bound : type_of% @Proofs.SortVectorCall.sort_vector_work_bound := @Proofs.SortVectorCall.sort_vector_work_bound

/-- `dedup_vector<long long>(x)` under the `std::unique` and `erase` contracts. -/
theorem dedup_vector_correct : type_of% @Proofs.DedupVectorCall.dedup_vector_correct := @Proofs.DedupVectorCall.dedup_vector_correct

theorem uniqAdj_sorted_spec : type_of% @Proofs.DedupVectorCall.uniqAdj_sorted_spec := @Proofs.DedupVectorCall.uniqAdj_sorted_spec

end Proofs.SortUtilCall
