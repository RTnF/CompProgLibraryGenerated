# segtree_sum

`cp::segtree_sum_product(node, l, r)` と `cp::segtree_sum_set(node, idx, val)` は、`experiments/library/cpp/segment_tree/segment_tree.hpp` の `SegmentTree` を、要素を `unsigned long long`、演算を加算（mod 2^64）に具体化した反復型セグメント木の `product`（区間 `[l, r)` の和）と `set`（1 点更新）である。クラスのフィールド `n_node`、`h_node` は vector の大きさから求める（`n_node = node.size() / 2`）。`node` は呼び出し側が持つ `std::vector<unsigned long long>`。

- 配置: `node.size() == 2 * N`（`N >= 1`。`N` は 2 の冪でなくてよい）。葉は `node[N + i]`（`i < N`）、内部節点は `1 <= i < N` で `node[i] == node[2 * i] + node[2 * i + 1]`（mod 2^64）。
- 前提: 上の配置、`N < 2^30`、`product` は `0 <= l <= r <= N`、`set` は `0 <= idx < N`。符号なしの加算は定義上ラップするので、オーバーフローの前提はない。
- `product` の結果: 葉 `[l, r)` の和を mod 2^64 で返す（`Σ_{j<r-l} node[N + l + j] mod 2^64`）。
- `set` の結果: 呼び出し後の `node` も同じ配置を満たし、葉 `idx` は `val`、他の葉は変わらない。
- 時間と領域: どちらも反復は `floor(log2 N) + 1` 回以下で、追加領域は局所変数だけ（モデル上の仕事量は呼び出し側の引数評価を除いて `410 * log2 N + 700` 以下（product）、`330 * log2 N + 800` 以下（set））。`set` の記憶域への書き込みは `log2 N + 3` 回以下。

証明は `Proofs/SegtreeSumCall.lean`:
- 数学: `rsum`（節点の和）、`TInv`（配置）、`rsum_pairs`（偶数位置から始まる節点の和が親の和に等しい）、`prod_step`（`product` の 1 反復で「残りの和」の不変条件 `PInv` が保たれる。`l`、`r` の偶奇 4 通りを `pl1`/`pr1`/`pleft`/`pright` で場合分けなしに書く）。`set` の `SInv`（根までの経路上の節点だけが未更新）と `sinv_step`/`sinv_init`/`sinv_zero`。
- 実行: 状態を `Proofs/GenState.lean` の `gS`（任意の型のセルの列）で記述し、`gS_decl`/`gS_assign`/`gS_env` で宣言・代入・参照を一般に扱った。`br1_exec`/`br2_exec`（偶奇の分岐）、`prod_iter`、`prod_loop`、`body_execP`、`set_iter`、`set_loop`、`body_execS`、呼び出し定理 `segtree_sum_product_correct`、`segtree_sum_set_correct`。

`product_all`、`get`、`search_prod_right/left`（ラムダの述語を取る二分探索）、一般のモノイドは扱わない。C++ のテストは `tests/segtree_sum.cpp`（大きさ 1〜40 の全ての区間、非 2 冪、ラップアラウンド、`set` 後の再構築との一致、2^17 要素）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <型>(...)`）に書いた型だけ。
