# find_cycle

`cp::find_cycle(head, target, state, it, stk, cyc, n)`（`library/graph/find_cycle.hpp`）は、有向グラフの閉路を 1 つ見つける反復 DFS である。`experiments/library/cpp/graph/find_cycle.hpp` の `ListGraph::find_cycle_directed` を、検証できる形に書き直した。

## 元のソースからの変更（違反一覧に記載）

- グラフは CSR 形式の配列で渡す。頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。
- 再帰ラムダを、明示的なスタック `stk`（長さ `n`）を使った反復に置き換えた。
- 結果は辺の配列ではなく、閉路を作る頂点の列とする。列は呼び出し側の `cyc[0 .. k)` に書き、頂点数 `k` を返す。
  - `cyc[i] -> cyc[i + 1]`（`i < k - 1`）と `cyc[k - 1] -> cyc[0]` が辺である。
  - 閉路がなければ `0` を返す。自己ループ `v -> v` は `k = 1` の閉路である。

`docs/experiments_status.md` の違反一覧に、元の形（`ListGraph` のメンバー関数で、辺の配列を返す）へ戻す作業として載せている。

## 使い方と前提

使い方: `state` の全要素を `0` にして渡す。`it`、`stk`、`cyc` は長さ `n` の作業配列で、中身は何でもよい。

前提（`Pre`）:

- `head.size() == n + 1`、`head` の要素は非負、`head` は広義単調増加。
- 辺はすべて `[0, n)` の頂点を結ぶ（すべての `target[p]` が範囲内で非負）。
- `state`/`it`/`stk`/`cyc` の長さは `n`。
- `head[n] + 3n < 2^62`（`int` に収まる入力はこれを満たす）。

## 結果（`Proofs/Cpp/FindCycle.lean` の `find_cycle_spec`）

返り値 `k` と書かれた `cyc` について `Out` が成り立つ。

- `k == 0` なら、グラフに有向閉路はない。どの辺 `u -> w` についても、`w` から `u` へ辿れない。
- `k > 0` なら、`k <= n` で、`cyc[0 .. k)` は範囲内の互いに異なる頂点であり、`cyc[i] -> cyc[(i + 1) % k]` が辺である（`CycOut`）。
- 手数は `5n + head[n] + 3` 以下、つまり `O(n + m)`。追加領域は局所変数だけである。

## 証明

- **探索の数学**（`Proofs/Math/FindCycleInv.lean`/`FindCycleStep.lean`/`FindCycleSpec.lean`/`FindCyclePhi.lean`）
  - 状態 `FS` は、色（白・灰・黒）、反復子、終了時刻（ghost）、スタックからなる。
  - 不変条件 `FInv`: スタックは灰の頂点の道であり、黒の頂点の辺は終了時刻が小さい黒の頂点へ向かう。
  - 4 つの遷移（根、push、黒の頂点の skip、pop）が `FInv` を保つ。
  - 最終状態から仕様を導く: 全部黒なら閉路なし（`acyclic_of_done`）、灰の頂点への辺があれば閉路（`Found`、`cycout_of_found`）。
  - ポテンシャル `phiF`（未走査の辺・白い頂点・スタックの高さ）が、ループの回数を抑える。
- **生成モデルとの対応**（`Proofs/Cpp/FindCycle.lean`）
  - C++ の配列を `FS` の欄として読み（`Abs`）、各ループに不変条件 `OI`/`II` を与える。
  - 後処理は 2 つのループである: 閉路の始点をスタック上で探すループと、`cyc` へのコピー。

## 検証

- `verifier/lean_translate.py` が関数全体を翻訳する。
- 差分テスト `tests/diff/find_cycle.py` は、頂点数 0〜10 のランダムな有向グラフで、モデルと C++ の結果を比べる。
- C++ のテスト `tests/find_cycle.cpp` は、頂点数 0〜8 のランダムな有向グラフで、到達可能性の閉包による基準と比較する（ASan/UBSan 付き）。

定理に含めていないこと:

- 見つかる閉路が元のソースと同じであること（どの閉路を返すかは仕様にない）。
- 辺の構造体の配列で返す元の形。
