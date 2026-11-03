import Proofs.FenwickCall
import Proofs.FenwickRangeCall
import Proofs.FenwickTreeVecCall

namespace Proofs.FenwickTreeCall

/-- `FenwickTree<long long>::add(i, val)`. -/
theorem fenwick_tree_add_correct : type_of% @Proofs.FenwickCall.fenwick_add_correct := @Proofs.FenwickCall.fenwick_add_correct

/-- `FenwickTree<long long>::sum(r)`. -/
theorem fenwick_tree_sum_correct : type_of% @Proofs.FenwickCall.fenwick_sum_correct := @Proofs.FenwickCall.fenwick_sum_correct

/-- `FenwickTree<long long>::sum(l, r)`. -/
theorem fenwick_tree_range_correct : type_of% @Proofs.FenwickRangeCall.fenwick_range_correct := @Proofs.FenwickRangeCall.fenwick_range_correct

/-- `FenwickTree<long long>::FenwickTree(const std::vector<long long> &)`, given the field built by the standard
constructor `tree(v.size() + 1)`. -/
theorem fenwick_tree_from_vector_correct : type_of% @Proofs.FenwickTreeVecCall.fenwick_tree_from_vector_correct := @Proofs.FenwickTreeVecCall.fenwick_tree_from_vector_correct

end Proofs.FenwickTreeCall
