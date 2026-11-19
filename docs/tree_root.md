# tree_root

`cp::tree_root(head, target, cost, parent, depth, cost_depth, stk, root, n)` は、根付き木の構築（反復の深さ優先探索）である。`experiments/library/cpp/tree/tree.hpp` の `Tree::build_depth` のうち、`parent_`・`depth_`・`cost_depth_`・最遠点 `farthest` を求める部分を、検証できる形に書き直した。`Cost` はテンプレートのまま残し、検証した具体化は `long long`。

グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺は `target[head[v] .. head[v + 1])` で、辺 `p` の費用は `cost[p]`。結果は呼び出し側の `parent`・`depth`・`cost_depth` に書き、最遠点は `stk` の最後の要素 `stk[n]` に書く（`stk` は長さ `n + 1`: 前半 `n` 個が手動のスタック、最後の 1 個が最遠点）。

元のソースからの変更:
- 隣接リスト（`vector<vector<E>>`）と `Edge` の代わりに CSR 配列と平行な費用配列を使う。検証器が扱えるのは平らな vector だけである。
- 元は `std::stack<tuple<int,int,Cost>>` と構造化束縛を使う。ここでは呼び出し側が渡す `stk`（`int` の vector、長さ `n`）を手動のスタックにし、`depth[v]`・`cost_depth[v]` を配列から読む。pop の順序と親の決まり方は元と同じ（頂点を積むときに訪問済みにする）。
- 元の `build_depth` が同時に求める高さ `height_`（最遠点の `cost_depth` に等しい）、およびそれを使う `diameter`・`height`・`path`・`build_ancestor`・`ancestor`・`lowest_common_ancestor`・`distance`・`full_tree_dp`、複数のコンストラクタ（辺リスト・親配列）は含めない。これらは `experiments/` に残し、`docs/experiments_status.md` の違反一覧に載せた。
- 各頂点の `parent_`・`depth_`・`cost_depth_` を根ごとに持つ `vector<vector<int>>` ではなく、1 つの根について 3 本の vector に書く。

前提: `n >= 1`、`head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size() == cost.size() < 2^31 - 1`、すべての `target[p]` が `[0, n)`、`0 <= root < n`、`parent.size() == depth.size() == cost_depth.size() == stk.size() == n`、`parent` の全要素が負（元は -1）、`n < 2^31 - 2`、`n * C < 2^63`（`C` は `|cost[p]|` の上界）。`depth`・`cost_depth`・`stk` の初期値は問わない（上書きする作業領域）。辺が対称な木であることは**要求しない**（任意の有向グラフで下の結果が成り立ち、対称な木ならそれが通常の根付き木になる）。

結果（`Proofs/Cpp/TreeRoot.lean` の `tree_root_correct`、一般の入力について証明。`Proofs/Math/TreeRootMath.lean` の `TreeSpec`、`FarSpec`）: 終了後の `parent'`・`depth'`・`cost_depth'` について
- `parent'[root] == root`、`depth'[root] == 0`、`cost_depth'[root] == 0`。
- 各頂点 `v < n` について、`parent'[v] >= 0` と「`v` が `root` から辺をたどって到達できる」ことは同値（到達できない頂点の `parent` は負のまま）。
- `root` 以外で到達できる頂点 `v` には、`u = parent'[v]` から `v` への辺 `p`（`head[u] <= p < head[u+1]`、`target[p] == v`）があり、`u` も到達済みで、`depth'[v] == depth'[u] + 1`、`cost_depth'[v] == cost_depth'[u] + cost[p]`。
- 到達できる頂点の `0 <= depth'[v] < n`、`|cost_depth'[v]| <= depth'[v] * C`。
- 最遠点 `F = stk'[n]` は `root` から到達できる頂点で、到達できる頂点の中で `cost_depth'` が最大（`FarSpec`）。同点なら元と同じく、スタックから最初に取り出された頂点が選ばれる（同じコードなので元と同じ結果。Lean の定理は「最大であること」まで）。
辺が対称な木なら、木の中の `root` から `v` への経路は一意なので、`parent'[v]` はその経路上の `v` の隣、`depth'[v]` は辺の数、`cost_depth'[v]` は費用の和になる（C++ のテストで確認している。Lean の定理には含めていない）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeRoot.lean` を生成する。`Proofs/Cpp/TreeRoot.lean` は、翻訳した関数の配列が旧来の純関数モデル（`Proofs/Math/TreeRootMath.lean` の `runL`、取り出した頂点の列 `stepD`、最遠点 `stepF`）の状態に常に一致することを示す（`RelS`、内側のループは `innerSt`。1 本の辺を見る `relax_rel`、頂点の取り出し `pop_init`/`pop_done`、空のスタック `outer_skip`）。モデルの不変条件 `Inv`・`GInv2` から、上の結果（`TreeSpec`、`FarSpec`）が従う。

- 定理は `Cost = long long`（Lean では `Int`）について述べる。差分テストの具体化と同じ。テンプレート自体は任意の `Cost` で使える。
- tick 数は `n + 1 + W` で、`W`（取り出した頂点の弧の数の和）は `head[n] = m` 以下（`sum_nodup_le`、`sum_outdeg`）。全体で `O(n + m)`。
- 定理に含めていないこと: 最遠点・高さ・直径・LCA・全方位木 DP など `Tree` の他の機能、対称な木での「親は経路上の隣」という上の最後の主張の Lean での定理、`parent` が負でない入力（その場合は結果が変わる）。

差分テスト（`tests/diff/tree_root.py`、対称な木と一般の有向グラフ）と C++ のテスト `tests/tree_root.cpp`（頂点数 1〜12 のランダムな木を参照実装（最遠点も元の取り出し順序で）と、頂点数 1〜9 の一般の有向グラフを到達可能性の閉包と照合する） で翻訳と実装を確かめる。
