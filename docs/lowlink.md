# lowlink

`cp::lowlink(head, target, ord, low, par, sep, it, stk, n)` は、無向グラフの関節点と橋を求めるための DFS（lowlink）の反復版である。`experiments/library/cpp/graph/lowlink.hpp` の `ListGraph::lowlink` から、検証できる形に書き直した。

元のソースからの変更:
- グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。無向辺は向きの逆な 2 本の辺として持つ（元と同じ）。
- 再帰ラムダを、明示的なスタック `stk`（長さ `n`）を使った反復に置き換えた。
- 結果は元の「ソート済みの関節点の配列と橋の配列」ではなく、呼び出し側の配列に残す: `ord[v]`（DFS で最初に訪れた順、成分は添字順）、`low[v]`（`v` の DFS 部分木から、各頂点の親への辺を除く 1 本の辺で届く `ord` の最小値）、`par[v]`（DFS 木の親。根は `-1`）、`sep[v]`（`ord[v] <= low[c]` を満たす `v` の子 `c` の数）。
  - 辺 `{par[v], v}` が橋 ⇔ `par[v] >= 0` かつ `low[v] == ord[v]`。
  - `v` が関節点 ⇔ 根でない（`par[v] >= 0`）なら `sep[v] >= 1`、根なら `sep[v] >= 2`。
- 平行辺は区別しない（元のソースも親への辺をすべて飛ばすので、平行辺で結ばれた 2 点の間の辺は橋として数えられる。検証した仕様も「辺の集合」としてのグラフについて述べる）。自己ループは持たない。

使い方: 呼び出し側が `ord` の全要素を `-1`、`par` の全要素を `-1`、`sep` の全要素を `0` にし、`low`、`it`、`stk` は長さ `n` の作業配列として渡す（中身は何でもよい）。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、グラフは対称（辺 `u -> v` があれば `v -> u` もある）で自己ループがない、`ord`/`low`/`par`/`sep`/`it`/`stk` の長さは `n`、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。

結果（`Proofs/LowlinkCall.lean`、一般の入力について証明）: 返ったとき、`LLOut`（`Proofs/LowlinkCall.lean`）が成り立つ。
- `ord` は `[0, n)` への全単射、`par[v]` は `-1` または `v` に隣り合う頂点で `ord` が `v` より小さいもの。
- 橋: `par[v] = p >= 0` のとき、`low[v] == ord[v]` ⇔ 辺 `{p, v}` を除いたグラフで `p` と `v` が連結でない。
- 関節点: 上の条件（根でなければ `sep >= 1`、根なら `sep >= 2`）⇔ `v` に隣り合う 2 頂点 `a`, `b` で、`v` を除いたグラフで連結でないものがある（連結成分の数が増えることと同値）。
- 証明は `Proofs/LowlinkGraph.lean`（DFS 木の性質から橋と関節点の同値を示す）、`Proofs/LowlinkInv.lean`/`LowlinkScan.lean`/`LowlinkPop.lean`/`LowlinkPush.lean`/`LowlinkRoot.lean`（反復 DFS の抽象機械と不変条件の保存）、`LowlinkFinal.lean`/`LowlinkSpec.lean`（最終状態から仕様）、`LowlinkProg.lean`/`LowlinkExec*.lean`/`LowlinkIter.lean`/`LowlinkOuter.lean`/`LowlinkProgExec.lean`（C++ 本体の実行と、ループの仕事量）、`LowlinkPrepare.lean`/`LowlinkCall.lean`（呼び出し）。

時間と領域: 仕事量は呼び出し側の引数評価を除いて高々 `2670 * n + 1750 * m + 250`（`m = target.size()`、粗い上限。実際の反復は `O(n + m)` 回で、各反復は定数時間）。追加領域は局所変数だけ。

定理に含めていないこと: 元のソースの出力形式（ソート済みの配列を返す）、平行辺・自己ループのあるグラフでの動作の仕様、`priority_queue` など他の部品との関係。C++ のテストは `tests/lowlink.cpp`（頂点数 0〜10 のランダムな単純グラフを、頂点・辺を 1 つ取り除いた連結成分の数の基準と比較する）。
