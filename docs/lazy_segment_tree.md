# lazy_segment_tree

`library/segment_tree/lazy_segment_tree.hpp` は元の `experiments/library/cpp/segment_tree/lazy_segment_tree.hpp` のクラス `LazySegmentTree<M, F>`（ACL 方式の非再帰遅延セグメント木）そのものである。元のソースからの変更は、名前空間 `cp`、標準ヘッダの include、`std::` の修飾、前提を書いた注釈だけで、メンバーと本体は元のまま（構築子 3 種、`set`、`get`、`product`、`product_all`、点への作用 `update(idx, f)`、区間への作用 `update(l, r, f)`、`search_prod_right`、`search_prod_left`）。

## 前提

- `M` はモノイド: 静的メンバー `M::e()` と、引数依存の名前探索で見つかる `op(M, M)` を持つ。`F` は作用: 静的メンバー `F::id()`、引数依存の名前探索で見つかる `compose(F, F)`、メンバー `f.apply(M)` を持つ（例: `algebraic_structure/monoid_lazy.hpp` の入れ子クラス `RangeAddRangeSum<T>::RangeSum`/`RangeAdd` など）。
- 法則（Lean の `Proofs.Cpp.LazySegmentTreeMath.Act`）: 値の集合 `V` と作用の集合 `VF` の上で、`M` はモノイド、`apply f` は `V` を保つ準同型（`apply f (op x y) = op (apply f x) (apply f y)`）、`compose(f, g).apply(x) = f.apply(g.apply(x))`（「`g` の後に `f`」）、`F::id().apply(x) = x`、`compose` と `id` は `VF` で閉じる。演算は副作用のない関数で、Lean では `Cpp.StaticCall`・`Cpp.AdlCall2`・`Cpp.Method1` のインスタンスが一定の手数で `Act` の演算を計算することを仮定 `Ops` に置く。
- `apply` は余りの葉の値 `e` にも適用される（`push` が子の両方に作用する）。`e` を含む `V` の全ての値で `apply` が定義されていなければならない。たとえば `RangeAddRangeMaxMin` は `e` が整数の最小値・最大値なので加算が溢れ、この前提を満たさない（`docs/experiments_findings.md`）。
- `n ≤ 2^29`（`2 * n_node` が `int` に収まる）。`set`/`get`/`update(idx, f)` は `0 ≤ idx < n`、`product`/`update(l, r, f)` は `0 ≤ l ≤ r ≤ n`、`product_all` は `n ≥ 1`（`n = 0` では元のコードが空の配列の `node[1]` を読む）。
- 探索の述語は副作用のない関数 `p : M → Bool` を計算し（`Cpp.Invoke1`）、`p(M::e()) == true`（`assert` で確かめる）。単調である必要はない。

## 結果（`Proofs/Cpp/LazySegmentTree.lean`）

`virt` は全てのタグを葉まで押し下げた木（節点の値に祖先のタグを近い順に作用させたもの）。`LValid A st v` は「`st` は値の列 `v` の遅延木」: 形（`n_node = 2^h`）と配列の長さ、各値と各タグが `V`/`VF` に属し、内部節点 `k` は `node[k] = apply(lazy[k], op(node[2k], node[2k+1]))`、`virt` の葉が `v` と `e`。

- `init_vec_spec` / `init_int_spec` / `init_0_spec`: 構築した木は `LValid`（値は `v`、`n` 個の `e`、空）。時間 `O(n)`。
- `get_spec`・`set_spec`・`update_point_spec`: 葉への道の祖先を根から押し下げてから読み書きし、書いた後は道を下から再計算する。結果は `v[idx]`、`v.set idx val`、`v.set idx (apply f v[idx])`。時間 `O(log n)`。
- `lproduct_spec`: 両端で切れる祖先を押し下げてから通常の区間積を `virt` 上で行う。`v[l] * ... * v[r-1]`、時間 `O(log n)`。`product_all_spec`: 根の値、1 手。
- `update_range_spec`: 両端の祖先を押し下げ、区間を覆う標準の節点に作用し（その祖先は全て押し下げ済みでタグが恒等）、両端の祖先を下から再計算する。結果は `[l, r)` の各値に `f` を作用させた列。時間 `O(log n)`。
- `lsearch_right_spec` / `lsearch_left_spec`: 返す境界の条件は通常のセグメント木と同じ（`docs/segment_tree.md`）。上昇中に読む節点の祖先は始点（終点）の葉の祖先に含まれて押し下げ済み、降下中は読む前に節点を押し下げるので、読む値は `virt` と一致する。時間 `O(log n)`。
- 返した木はどの操作の後も `LValid`。数学の補題は `Proofs/Cpp/Lib/LazySegmentTreeMath.lean`（`P`・`virt`、押し下げ、作用と再計算、境界の節点の性質）で、区間積と探索は通常の木の補題 `Proofs/Cpp/Lib/SegmentTreeMath.lean` を `virt` に適用する。

## 検証

`verifier/lean_translate.py` がヘッダ全体を翻訳する（`f.apply(x)` → `Cpp.Method1`、ほかは `docs/segment_tree.md` と同じ。`docs/translation.md`）。差分テスト `tests/diff/lazy_segment_tree.py` は `(M, F)` を `monoid_lazy.hpp` の `RangeAddRangeSum` と `RangeSetRangeSum` の入れ子クラス（`[diff] bindings = ["monoid_lazy"]`。作用のフィールド数が違うので生成器に `case_args` を渡す）にして、構築・`set`・`get`・`product`・`product_all`・点と区間への作用を比べる。C++ のテスト `tests/lazy_segment_tree.cpp` は `RangeAddRangeSum`・`RangeSetRangeSum`・`RangeSetRangeMaxMin` の最大と最小で、探索（単調・非単調の述語）を含めて素朴な配列と照合する（ASan/UBSan 付き）。
