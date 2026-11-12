# segtree_sum

`cp::segtree_sum_product(node, l, r)` と `cp::segtree_sum_set(node, idx, val)` は、`experiments/library/cpp/segment_tree/segment_tree.hpp` の `SegmentTree` を、要素を `unsigned long long`、演算を加算（mod 2^64）に具体化した反復型セグメント木の `product`（区間 `[l, r)` の和）と `set`（1 点更新）である。クラスのフィールド `n_node`、`h_node` は vector の大きさから求める（`n_node = node.size() / 2`）。`node` は呼び出し側が持つ `std::vector<unsigned long long>`。

- 配置: `node.size() == 2 * N`（`N >= 1`。`N` は 2 の冪でなくてよい）。葉は `node[N + i]`（`i < N`）、内部節点は `1 <= i < N` で `node[i] == node[2 * i] + node[2 * i + 1]`（mod 2^64）。
- 前提: 上の配置、`N < 2^30`、`product` は `0 <= l <= r <= N`、`set` は `0 <= idx < N`。符号なしの加算は定義上ラップするので、オーバーフローの前提はない。
- `product` の結果: 葉 `[l, r)` の和を mod 2^64 で返す（`Σ_{j<r-l} node[N + l + j] mod 2^64`）。
- `set` の結果: 呼び出し後の `node` も同じ配置を満たし、葉 `idx` は `val`、他の葉は変わらない。
- 時間と領域: どちらも反復は `floor(log2 N) + 1` 回以下で、追加領域は局所変数だけ（モデル上の仕事量は呼び出し側の引数評価を除いて `410 * log2 N + 700` 以下（product）、`330 * log2 N + 800` 以下（set））。`set` の記憶域への書き込みは `log2 N + 3` 回以下。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/SegtreeSum.lean` を生成する。`Proofs/Cpp/SegtreeSum.lean` は `T = unsigned long long`（`UInt64`）について、旧来の `Proofs/SegTreeMath.lean` のモノイド `Mon` を 2^64 を法とする和 `M64` で具体化して次を示す。

- `segtree_sum_product_spec`: 配置 `TInv` と `N < 2^30`、`l <= r <= N` のとき、返り値は葉 `[l, r)` の和 `rfold M64 v (N + l) (r - l)`。ループの不変条件は `PInv`（1 回の反復は `prod_step`。右側の累積 `right + node[r]` は和の可換性で `pright` に一致）。tick 数は `bitWidth (r + N) + 2` 以下。
- `segtree_sum_set_spec`: 更新後も `TInv` を満たし、葉は `idx` だけが `val` に変わる。ループの不変条件は根への経路以外が整合していること `SInv`（`sinv_init`、`sinv_step`、`sinv_zero`）。tick 数は `bitWidth N + 2` 以下。

差分テスト（`tests/diff/segtree_sum.py`）と C++ のテストで翻訳と実装を確かめる。

`product_all`、`get`、`search_prod_right/left`（ラムダの述語を取る二分探索）、一般のモノイドは扱わない。C++ のテストは `tests/segtree_sum.cpp`（大きさ 1〜40 の全ての区間、非 2 冪、ラップアラウンド、`set` 後の再構築との一致、2^17 要素）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <型>(...)`）に書いた型だけ。
