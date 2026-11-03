# tree_edges

`cp::tree_edges_from_parent(parent, from, to, n)` は、親配列で与えられた木の辺（両方向）を辺リストに並べ、書いた辺の本数を返す。`experiments/library/cpp/tree/tree.hpp` のコンストラクタ `Tree(int root, vector<int> &parent)` の、隣接リストを作る部分を書き直した。

`i = 0, 1, ..., n - 1` の順に、`parent[i] != i` かつ `0 <= parent[i] < n` を満たす `i` について、辺 `parent[i] -> i` と `i -> parent[i]` をこの順で `from[k]`、`to[k]`（`k = 0, 1, ...`）に追加する。これは元が `adj[parent[i]]` と `adj[i]` に追加する順序と同じである。

元のソースからの変更:
- 隣接リスト（`vector<vector<E>>`）の代わりに 2 本の辺リスト（`from`、`to`）に書く。CSR 配列にするには、書いた長さ `m` に `from`、`to` を `resize` してから `cp::csr_build` に渡す（計数ソートは安定なので、各頂点の辺の並びは元の隣接リストと同じになる。C++ のテストで確認している）。
- 条件 `i != parent[i] && 0 <= parent[i] && parent[i] < n` を入れ子の `if` で書く（短絡評価と同じ結果）。
- 元のコンストラクタが続けて行う根の決定と `build_depth` は `tree_root` に対応する。根を持たない親配列版 `Tree(vector<int> &parent)` の根の決定、辺リスト版のコンストラクタ（`from`/`to`/`cost` を取るもの）は含めない。`docs/experiments_status.md` の違反一覧に載せた。

前提: `0 <= n < 2^30`、`parent.size() >= n`、`from.size() >= 2 * n`、`to.size() >= 2 * n`。

結果（`Proofs/TreeEdgesCall.lean`、一般の入力について証明）: 返り値 `m` は、条件を満たす `i` の個数の 2 倍で、`from[0..m)`、`to[0..m)` は上の順序に並んだ辺列、`m` 以降の要素は変わらない（`FFt`、`TTt`）。`parent` の要素が負でも範囲外でも未定義の挙動はない（`32` ビット整数として正しく比較される）。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて `420 * n + 200` 以下、書き込みは `4 * n` 回以下、追加領域は局所変数だけ。

証明は `Proofs/TreeEdgesExec.lean`（途中状態 `FFt`/`TTt`/`arcP`、6 つの文 `y3_exec`、入れ子の分岐 `bi_exec`、ループ全体 `body_exec`）、`Proofs/TreeEdgesPrepare.lean`/`Proofs/TreeEdgesCall.lean`（呼び出し）。C++ のテストは `tests/tree_edges.cpp`（根・範囲外の親を含むランダムな親配列で、元の構築と同じ隣接順序になることを `csr_build` との合成で確認する）。
