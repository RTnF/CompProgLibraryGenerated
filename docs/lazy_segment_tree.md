# lazy_segment_tree

> 2026-11-11 に公開を取り下げた（検証待ち）。旧方式の証明が全件CIの30分予算を超えるため、新方式（`docs/redesign_2026-11.md`）で再検証してから公開する。旧証明は Git 履歴に残る。取り下げ前の記録。以下は取り下げ前の記録で、記載の `library/`・`Proofs/` のファイルには現在のツリーにないものがある。

`cp::LazySegmentTree<P>` は、モノイド（値）と、その上に作用する写像（作用）を方針 `P` として与える遅延伝播セグメント木（`experiments/library/cpp/segment_tree/lazy_segment_tree.hpp`、ACL ベース）である。構成子 `LazySegmentTree(const vector<T>& v)`、1 点代入 `set(idx, val)`、1 点取得 `get(idx)`、区間積 `product(l, r)`（`[l, r)`）、全体の積 `product_all()`、1 点作用 `update(idx, f)`、区間作用 `update(l, r, f)` を持つ。検証した具体化は `LazySegmentTree<LazyChminMax<long long>>` である。値は `long long` の最大値のモノイド（単位元 `e()` は最小値、`op` は max）、作用は chmin（作用 `f` は `x` を `min(f, x)` にする。恒等 `id()` は最大値、`composition(f, g) = min(f, g)`）である。

方針 `P` は、`value_type`、`action_type`、静的な `e()`、`id()`、`op(a, b)`、`mapping(f, x)`、`composition(f, g)` を持つ。ライブラリが仮定する法則は、`mapping(f, op(a, b)) == op(mapping(f, a), mapping(f, b))`、`mapping(composition(f, g), x) == mapping(f, mapping(g, x))`、`mapping(id, x) == x`、`composition` が結合的で `id` が単位元、の 4 つである。他の方針（区間加算・区間 max など）は、同じ形の方針と `template class LazySegmentTree<方針>;` を足して検証する（Lean の数学部分 `Proofs/LazySegMath.lean` は法則を `LMon` の構造として一般に証明してあり、実行の証明は具体化ごとに書く）。

配置: `n_node` は `n` 以上の最小の 2 冪（`n = 0` なら 0。`n >= 1` では 2 以上）、`h_node = log2(n_node)`、`node` は `2 * n_node` 個、`lazy` は `n_node` 個。葉は `node[n_node + i]`（`i < n`）、残りの葉は単位元。節点 `k` の保留中の作用 `lazy[k]` は、`k` の子孫すべてに（上の祖先の作用の後で）まだ適用されていない。理想の木は葉の列 `A` から作り、「祖先の作用の合成を適用した `node[k]` は、`k` の葉区間の積に等しい」ことを不変条件（Lean の `Rep`）とする。

元のソースからの変更:
- 値と作用は、元のモノイド `M`（`op`、`e()`）と作用 `F`（`apply`、`compose`、`id()`）のオブジェクトの木ではなく、値の型 `value_type` と作用の型 `action_type` を持つ方針 `P` の静的関数として与える（`vector<value_type>`、`vector<action_type>`）。検証された vector 操作が整数の `std::vector` だけなので、1 つの `long long` だけを持つ値と作用に限る。この狭まりは `docs/experiments_status.md` の違反一覧に載せた。
- 構成子は、`node`、`lazy`、`n`、`n_node`、`h_node` をメンバー初期化子で作り、本体は葉のコピーと構築ループだけにした。フィールドは `node`、`lazy` の順に先頭で宣言する（検証の枠組みがベクトルのスロットを先に取るため）。既定構成子と `int` を取る構成子は含めない。
- `1 << k` と `>>` を `pw`（2 冪を持つ変数）と `/ 2` に書き換えた（符号付きのビット演算は未対応）。結果は同じ。`all_apply`/`push`/`update(i)` は元どおり小さな private 関数として残す。
- `l == r` の早期 return はしない（`product(l, l)` は単位元、`update(l, l, f)` は木を変えない。どちらも証明の対象に含む）。
- `assert`、`search_prod_right`、`search_prod_left`（述語 `F` を取る二分探索）は含めない。

前提: 構成子は `1 <= n <= 2^29`（`2 * n_node` が `int` に収まる）、`v` の要素は有効な値。`set`/`get`/`update(idx, f)` は `0 <= idx < n_node`（`n_node` は 2^29 以下）、`product`/`update(l, r, f)` は `0 <= l <= r <= n_node` と `h_node <= 29`、`product_all()` は `h_node >= 1`（`n >= 1` なら成り立つ）。`n = 0` の空の木は扱わない。作用 `f` は有効な `long long`。

結果（`Proofs/LazySegCall.lean`、一般の入力について証明。木の状態は `Rep chminMon N A node lz` で、`A` が表す配列、`N = n_node`）:
- 構成子: `node`/`lazy` の初期値（`e()` が `2 * n_node` 個、`id()` が `n_node` 個）から、配列 `v ++ (e() を n_node - n 個)` を表す状態になる。
- `set(idx, val)`: 配列 `A` を `A[idx] = val` にした配列を表す状態になる。
- `get(idx)`: 返り値は `A[idx]`。状態は同じ配列を表す（保留中の作用を押し下げる）。
- `product(l, r)`: 返り値は `A[l .. r-1]` の積（`rfold`、最大値）。状態は同じ配列を表す。
- `product_all()`: 返り値は `A` 全体の積（`node[1]`）。状態は変わらない。
- `update(idx, f)`: 配列を `A[idx] = min(f, A[idx])` にした配列を表す状態になる。
- `update(l, r, f)`: 配列を、`l <= i < r` の `A[i]` を `min(f, A[i])` にした配列（`chminRange A l r f`）を表す状態になる。

時間と領域: 構成子は `O(n_node)`（仕事量 `3000 * (2^k + 1) + 3300` 以下、`n_node = 2^k`）、`set`/`update(idx, f)` は `h_node + 1` 回の反復（仕事量 `2500 * h_node + 450` 以下）、`get` は仕事量 `1500 * h_node + 250` 以下、`product` は `h_node` 回の下向きの押し下げと `log2(r - l) + 1` 回以下の反復（仕事量 `3400 * h_node + 1600 * (log2(r - l) + 1) + 800` 以下）、`update(l, r, f)` は仕事量 `7000 * h_node + 3100 * (log2(r - l) + 1) + 1100` 以下、`product_all` は定数。追加領域は局所変数だけで、呼び出し側の変数に加える領域の上限は定数（1000 セル）で表す（呼び出しの定理 `ScalarPostMB 1000 ...`。`Proofs/MultiVecCallB.lean` は `MultiVecCall.lean` の上限の定数 100 を引数にしたもの）。

証明: `Proofs/LazySegMath.lean`（作用つきモノイド `LMon`、保留中の作用の合成 `G`、理想の木 `tr`、不変条件 `Ext`/`Rep`、`push`/`all_apply`/`update` の各補題）、`LazySegChmin.lean`（chmin と max の `LMon` の具体化）、`LazySegBlocks.lean`（インライン展開された `all_apply`/`push` の実行）、`LazySegUpd.lean`/`LazySegSet.lean`/`LazySegGet.lean`/`LazySegApplyPt.lean`/`LazySegProduct.lean`/`LazySegRange.lean`/`LazySegAll.lean`/`LazySegCtor.lean`/`LazySegCtorRep.lean`（各関数の実行）、`LazySegAncLeaf.lean`/`LazySegArith.lean`/`LazySegApplyMath.lean`/`LazySegApplyLoop.lean`（区間作用の算術と不変条件）、`LazySegApplyExec.lean`/`LazySegApplyGlue.lean`/`LazySegUpdE.lean`/`LazySegUpdBody.lean`（区間作用の実行）、`LazySegPrepare.lean`（引数の準備。生成スクリプトで作成）、`LazySegCall.lean`（呼び出し）。C++ のテストは `tests/lazy_segment_tree.cpp`（元の `LazySegmentTree` の写しと素朴な実装との照合、全区間、`LLONG_MIN`/`LLONG_MAX`、2^16 + 1 要素、`-fsanitize=address,undefined`）。
