# prim

`cp::prim(head, target, cost, dist, done, n, inf)` は、無向グラフの最小全域森（プリム法）の総コストを返す配列版である。`experiments/library/cpp/graph/prim.hpp` の `ListGraph::prim` から、検証できる形に書き直した。

元のソースからの変更:
- グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`、コストは同じ位置の `cost[...]`。無向辺は元と同じく向きの逆な 2 本の辺として持つ（逆向きの辺のコストは同じ）。
- `priority_queue` の代わりに、未訪問の頂点のうち `dist` が最小のものを線形探索で選ぶ。計算量は `O(n^2 + m)`（元は `O((n + m) log n)`）。
- 訪問済みの印 `done` と、各頂点を森に加えたコスト `dist` は呼び出し側が用意した作業配列で、終了時に `dist[v]` は頂点 `v` を森につないだ辺のコスト（各連結成分の最初の頂点は 0）になる。総コストはその和。
- 各連結成分は、元と同じく添字が最小の未訪問頂点から広げる。

使い方: `dist` の全要素を `inf`（辺がまだない印）、`done` を長さ `n` の 0 にして渡す。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size() == cost.size()`、すべての `target[p]` が `[0, n)`、すべての `cost[p]` が `[0, inf)`、`0 ≤ inf ≤ 2^62`、`dist.size() == done.size() == n`、`n < 2^31 - 2`、`target.size() < 2^31 - 1`、グラフが対称（逆向きの辺が同じコストで存在する）、総コスト `n * (最大コスト)` が `long long` に収まる。

結果（`Proofs/PrimCall.lean`、一般の入力について証明）: 返り値 `W` は最小全域森の重みである（`IsMSF`）。つまり、(1) 重み `W` の全域森（グラフの連結性を保つ森）が存在し、(2) 任意の全域森の重みは `W` 以上。
- 証明は `Proofs/PrimMath.lean`（根付き森、最小全域森の最適性。確定した辺の集合が各しきい値 `t` 未満の辺での連結性を保つことを示す）、`Proofs/PrimRelax.lean`（緩和ループ）、`Proofs/PrimStep.lean`（不変条件 `PInv`）、`Proofs/PrimExec.lean`（C++ 本体の実行）、`Proofs/PrimBridge.lean`（不変条件から `IsMSF`）、`Proofs/PrimPrepare.lean`/`Proofs/PrimCall.lean`（呼び出し）。

時間と領域: 仕事量は呼び出し側の引数評価を除いて高々 `(640 * n + 760) * n + 420 * m + 150`（`m` は辺の数）。追加領域は局所変数だけ。

定理に含めていないこと: 辺ごとの選択（どの辺が森に入るか）の内容、`priority_queue` 版、親の配列。C++ のテストは `tests/prim.cpp`（頂点数 0〜60 のランダムな多重辺・自己ループ・非連結グラフを、クラスカル法の基準と比較する）。

費用の型 `Cost` はテンプレート引数のままで、検証した具体化はヘッダー末尾の明示的な具体化 `prim<long long>`。
