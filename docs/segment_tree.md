# segment_tree

`cp::SegmentTree<M>` は、モノイド `M` の反復型セグメント木（`experiments/library/cpp/segment_tree/segment_tree.hpp`、ACL ベース）である。構成子 `SegmentTree(const vector<T>& v)`、1 点更新 `set(idx, val)`、1 点取得 `get(idx)`、区間積 `product(l, r)`（`[l, r)`）、全体の積 `product_all()` を持つ。検証した具体化は `SegmentTree<SegMax<long long>>`（`long long` の最大値。`SegMax<T>` は `monoid.hpp` の `MonoidMax<T>` に当たる方針）と `SegmentTree<SegMin<long long>>`（最小値。`MonoidMin<T>` に当たる）。

モノイド `M` は、`value_type`、静的な `e()`（単位元）、静的な `apply(a, b)`（結合的な演算）を持つ方針（policy）として与える。他のモノイド（`MonoidMin`、`MonoidMul`、和など）は、同じ形の方針と `template class SegmentTree<方針>;` を足して検証する（Lean の数学部分 `Proofs/SegTreeMath.lean` は任意のモノイドについて証明済みで、実行の証明は具体化ごとに書く）。

配置: `n_node` は `n` 以上の最小の 2 冪（`n = 0` なら 0）、`h_node = log2(n_node)`、`node` は `2 * n_node` 個。葉は `node[n_node + i]`（`i < n`）、残りの葉は単位元、内部節点は `1 <= i < n_node` で `node[i] == apply(node[2i], node[2i+1])`。

元のソースからの変更:
- 木は `M` のオブジェクトではなく値（`vector<value_type>`）を持つ。`get`/`product`/`product_all` は `M` ではなく `value_type`（元の `M::x`）を返し、`set` は `value_type` を取る。検証されたベクトル操作が整数の `std::vector` だけなので、1 つのフィールド `x` だけを持つ値のモノイドに限る（複数のフィールドを持つ `M`、たとえば遅延セグメント木の作用付きのモノイドは未対応）。この狭まりは `docs/experiments_status.md` の違反一覧に載せた。
- 構成子は、`node`、`n`、`n_node`、`h_node` をメンバー初期化子で作り（`n_node`/`h_node` は静的補助関数 `size_of`/`height_of`）、本体は葉のコピーと構築ループだけにした（ベクトルの代入 `node = vector(...)` が監査の対象外のため）。フィールドは `node` を先頭に宣言する（検証の枠組みがベクトルのスロットを先に取るため）。
- `1 << k` と `>>` を `* 2` と `/ 2` に、`set` の `update(idx >> i)` を `idx = idx / 2; update(idx)` に書き換えた（符号付きのビット演算は未対応）。結果は同じ。
- `assert`、`search_prod_right`、`search_prod_left`（述語 `F` を取る二分探索）は含めていない。

前提: 構成子は `1 <= n <= 2^29`（`2 * n_node` が `int` に収まる）、`v` の要素は有効な値。`set` は `0 <= idx < n_node`、`product` は `0 <= l <= r <= n_node`（元の `assert` は `r <= n`）。`n = 0` の空の木は扱わない。

結果（`Proofs/SegmentTreeCall.lean`、一般の入力について証明）:
- 構成子: `node` が長さ `2 * n_node` で、葉 `n_node + i` が `v[i]`（`i < n`）または `e()`、内部節点が子の積になる（`TInv`）。
- `set`: 呼び出し後も木の配置を満たし、葉 `idx + n_node` は `val`、他の葉は変わらない。
- `product(l, r)`: 返り値は葉 `[l, r)` の積（`rfold`）。`get(idx)`: 葉 `node[idx + n_node]`。`product_all()`: `node[1]`。

時間と領域: 構成子は `O(n_node)`（仕事量 `3000 * (2^k + 1) + 3000` 以下、`n_node = 2^k`）、`set` は `h_node + 1` 回の反復（仕事量 `900 * h_node + 300` 以下）、`product` は `log2(r - l) + 1` 回以下の反復（仕事量 `1600 * (log2(r - l) + 1) + 400` 以下）、`get`/`product_all` は定数。追加領域はどれも局所変数だけ。

証明: `Proofs/SegTreeMath.lean`（任意のモノイド `Mon` に対する `rfold`、配置 `TInv`、`product` のループ不変条件 `PInv`/`prod_step`、`set` の `SInv`、構築の `BInv`）、`Proofs/SegmentTreeExec.lean`（インライン展開された `apply` の 5 文を扱う `appblk_exec`、`update(i)` の `upd_exec`、`maxMon`）、`SegmentTreeSet.lean`/`SegmentTreeProduct.lean`/`SegmentTreeGet.lean`/`SegmentTreeCtor.lean`（各関数の実行）、`SegmentTreePrepare.lean`（引数の準備。生成スクリプトで作成）、`SegmentTreeCall.lean`（呼び出し。最小値版は同じファイルの名前空間 `Min`）。最小値版の実行の証明は `SegmentTreeMin*.lean`（最大値版を機械的に写し、`apply` の条件 `b < a` の向きと単位元 `LLONG_MAX` だけを変えた）。C++ のテストは `tests/segment_tree.cpp`（元の `SegmentTree` の写しと素朴な実装との照合、全区間、`LLONG_MIN`/`LLONG_MAX`、2^16 + 1 要素、`-fsanitize=address,undefined`）。
