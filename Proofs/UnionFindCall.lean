import Proofs.UfCounterCall

namespace Proofs.UnionFindCall

/-- The private `UnionFind::find_root`: the root of the tree of `a`, without compressing the path. -/
theorem union_find_find_root_correct : type_of% @Proofs.UfRootCall.uf_root_correct := @Proofs.UfRootCall.uf_root_correct

/-- `UnionFind::size(a)`. -/
theorem union_find_size_correct : type_of% @Proofs.UfRootCall.uf_size_correct := @Proofs.UfRootCall.uf_size_correct

/-- `UnionFind::same(a, b)`. -/
theorem union_find_same_correct : type_of% @Proofs.UfSameCall.uf_same_correct := @Proofs.UfSameCall.uf_same_correct

/-- `UnionFind::root(a)`, which compresses the path from `a` to the root. -/
theorem union_find_root_correct : type_of% @Proofs.UfFindCall.uf_find_correct := @Proofs.UfFindCall.uf_find_correct

/-- `UnionFind::unite(a, b)`. -/
theorem union_find_unite_correct : type_of% @Proofs.UfUniteCall.uf_unite_correct := @Proofs.UfUniteCall.uf_unite_correct

/-- The vector after `unite` is again a forest. -/
theorem union_find_unite_forest : type_of% @Proofs.UfUniteCall.uniteVecC_forest := @Proofs.UfUniteCall.uniteVecC_forest

/-- `UnionFind::num_groups()`. -/
theorem union_find_num_groups_correct : type_of% @Proofs.UfCounterCall.uf_num_groups_correct :=
  @Proofs.UfCounterCall.uf_num_groups_correct

/-- The body of `UnionFind::UnionFind(int n)` after the member initialiser `ps(n + 1, -1)`: `ps[n] = -1 - n`. -/
theorem union_find_new_correct : type_of% @Proofs.UfCounterCall.uf_new_correct := @Proofs.UfCounterCall.uf_new_correct

end Proofs.UnionFindCall
