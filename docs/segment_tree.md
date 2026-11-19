# segment_tree

`library/segment_tree/segment_tree.hpp` は元の `experiments/library/cpp/segment_tree/segment_tree.hpp` のクラス `SegmentTree<M>`（ACL 方式の非再帰セグメント木）そのものである。元のソースからの変更は、名前空間 `cp`、標準ヘッダの include、`std::` の修飾だけで、メンバーと本体は元のまま（構築子 3 種、`set`、`get`、`product`、`product_all`、`search_prod_right`、`search_prod_left`）。

## 前提

- `M` はモノイド: 静的メンバー `M::e()` と、引数依存の名前探索で見つかる `op(M, M)` を持つ（例: `algebraic_structure/monoid.hpp` の `MonoidMax`・`MonoidMin`・`MonoidMul`）。表す値の集合 `V` の上で結合則と単位元の法則が成り立ち、`op` は `V` で閉じる（Lean の `Proofs.Cpp.SegmentTreeMath.Mon`）。`op` と `e` は副作用のない関数である（Lean では `Cpp.AdlCall2`・`Cpp.StaticCall` のインスタンスが一定の手数で `Mon` の演算を計算することを仮定 `Ops` に置く）。
- `n ≤ 2^29`（`2 * n_node` が `int` に収まる）。`set`/`get` は `0 ≤ idx < n`、`product` は `0 ≤ l ≤ r ≤ n`、`product_all` は `n ≥ 1`（`n = 0` では元のコードが空の配列の `node[1]` を読む。`docs/experiments_findings.md`）。
- 探索の述語 `f` は副作用のない関数 `p : M → Bool` を計算し（Lean では `Cpp.Invoke1` のインスタンス）、`f(M::e()) == true`（`assert` で確かめる）。単調である必要はない。

## 結果（`Proofs/Cpp/SegmentTree.lean`）

`Valid m st v` は「`st` は値の列 `v` の木」: `n_node = 2^h`（`n ≥ 1` のとき `h` は `n ≤ 2^h` となる最小の `h ≥ 1`）、葉 `node[n_node + i] = v[i]`、余りの葉は `e`、内部節点は子の積。

- `init_vec_spec` / `init_int_spec` / `init_0_spec`: 構築した木は `Valid`（値は `v`、`n` 個の `e`、空）。時間 `O(n)`。
- `get_spec`: `v[idx]`、1 手。`product_all_spec`: `v[0] * ... * v[n-1]`、1 手。
- `product_spec`: `v[l] * ... * v[r-1]`（`rf`）、時間 `O(log n)`（`op` の呼び出し回数と手数）。
- `set_spec`: `Valid` が `v.set idx val` に対して保たれる。時間 `O(log n)`。
- `search_right_spec`: 戻り値 `r` は `l ≤ r ≤ n`、`p(v[l] * ... * v[r-1]) = true`、かつ `r = n` または `p(v[l] * ... * v[r]) = false`。`search_left_spec` は対称（`l` を返し、`p(v[l..r)) = true`、かつ `l = 0` または `p(v[l-1..r)) = false`）。どちらも時間 `O(log n)`（`op` と `f` の呼び出しを含む）。
- 数学の補題は `Proofs/Cpp/Lib/SegmentTreeMath.lean`（区間積 `rf`、木の不変条件、二分探索の不変条件 `RInv`/`DInv`/`LInv`/`DLInv`、2 冪の高さの補題）。

## 検証

`verifier/lean_translate.py` がヘッダ全体を翻訳する（`op(a, b)` → `Cpp.AdlCall2`、`M::e()` → `Cpp.StaticCall`、`f(x)` → `Cpp.Invoke1`、委譲構築子、式中の `l++`/`--r`、`do-while`。`docs/translation.md`）。差分テスト `tests/diff/segment_tree.py` は `M` を `MonoidMax`・`MonoidMin`・`MonoidMul`（`[diff] bindings = ["monoid"]`）にして構築・更新・取得・区間積を比べ、探索は `tests/test_segment_tree_search.py` が述語を持つ専用のドライバで比べる。C++ のテスト `tests/segment_tree.cpp` は単調・非単調の述語を含めて愚直な畳み込みと照合する。
