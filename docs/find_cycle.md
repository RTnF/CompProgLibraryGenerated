# find_cycle

> 2026-11-11 に公開を取り下げた（検証待ち）。旧方式の証明が全件CIの30分予算を超えるため、新方式（`docs/redesign_2026-11.md`）で再検証してから公開する。旧証明は Git 履歴に残る。取り下げ前の記録。以下は取り下げ前の記録で、記載の `library/`・`Proofs/` のファイルには現在のツリーにないものがある。

`cp::find_cycle(head, target, state, it, stk, cyc, n)` は、有向グラフの閉路を 1 つ見つける反復 DFS である。`experiments/library/cpp/graph/find_cycle.hpp` の `ListGraph::find_cycle_directed` から、検証できる形に書き直した。

元のソースからの変更:
- グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。
- 再帰ラムダを、明示的なスタック `stk`（長さ `n`）を使った反復に置き換えた。
- 結果は辺の配列ではなく、閉路を作る頂点の列を呼び出し側の `cyc[0 .. k)` に書き、頂点数 `k` を返す。`cyc[i] -> cyc[i + 1]`（`i < k - 1`）と `cyc[k - 1] -> cyc[0]` が辺である。閉路がなければ `0` を返す（自己ループ `v -> v` は `k = 1` の閉路）。

使い方: `state` の全要素を `0` にして渡す（`it`、`stk`、`cyc` は長さ `n` の作業配列で、中身は何でもよい）。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、`state`/`it`/`stk`/`cyc` の長さは `n`、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。

結果（`Proofs/FindCycleCall.lean`、一般の入力について証明）: 返り値 `k` について `FCOut`（`Proofs/FindCycleProgExec.lean`）が成り立つ。
- `k == 0` なら、グラフに有向閉路はない（どの辺 `u -> w` についても、`w` から `u` へ辿れない）。
- `k > 0` なら、`k <= n`、`cyc[0 .. k)` は範囲内で互いに異なる頂点で、`cyc[i] -> cyc[(i + 1) % k]` が辺である。
- 証明は `Proofs/FindCycleInv.lean`/`FindCycleStep.lean`（探索の不変条件: 白・灰・黒、スタックは灰の頂点の道、黒の頂点の辺は終了時刻が小さい黒の頂点へ向かう）、`FindCycleSpec.lean`（最終状態から仕様）、`FindCycleProg.lean`/`FindCycleExec.lean`/`FindCycleIter.lean`/`FindCycleOuter.lean`/`FindCycleExtract.lean`/`FindCycleProgExec.lean`（C++ 本体の実行とループの仕事量）、`FindCyclePrepare.lean`/`FindCycleCall.lean`（呼び出し）。

時間と領域: 仕事量は呼び出し側の引数評価を除いて高々 `4000 * n + 1360 * m + 1360 * n + 3150`（`m = target.size()`、粗い上限。実際の反復は `O(n + m)` 回）。追加領域は局所変数だけ。

定理に含めていないこと: 見つかる閉路が元のソースと同じであること（どの閉路を返すかは仕様にない）、辺の構造体の配列で返す元の形。C++ のテストは `tests/find_cycle.cpp`（頂点数 0〜8 のランダムな有向グラフを、到達可能性の閉包の基準と比較する）。
