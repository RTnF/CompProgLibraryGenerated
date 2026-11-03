# tree_path

`cp::tree_path(parent, out, from, to)` は、根 `from` の根付き木で `to` から `from` までの経路を求める。`experiments/library/cpp/tree/tree.hpp` の `Tree::path(from, to)` に対応する。

親配列 `parent`（`tree_root(..., from, n)` の出力）を `to` から `from` まで親へたどり、頂点を `out[0] = to`、`out[i + 1] = parent[out[i]]`、…、`out[len - 1] = from` と書き、`len` を返す。元の `Tree::path` も `to` から `from` の順に並べて返す（C++ のテストで、元の深さ優先探索の結果と一致することを確認している）。

元のソースからの変更:
- 元は `from` からもう一度深さ優先探索して経路を復元する。ここでは `tree_root` が求めた親配列をたどる（木では経路が一意なので同じ頂点列になる）。`from` と `to` が同じ頂点なら長さ 1 の経路 `[from]` を返す。
- 戻り値の `vector<int>` の代わりに、呼び出し側の `out` に書き、長さを返す。`to` が `from` から到達できない場合に元が返す空の経路は、前提条件（`to` が到達可能）として扱う。到達不能かどうかは `tree_root` 後の `parent[to] < 0` で判定できる。

前提: `parent` を `to` から親へ `m` 回たどると初めて `from` に着く（`tree_root` の出力では、`to` が `from` から到達可能なら `m = depth[to]`）。途中の頂点（`to`、`from` を含む）はすべて `[0, parent.size())` にある。`out.size() >= m + 1`、`m + 1 < 2^31`。

結果（`Proofs/TreePathCall.lean`、一般の入力について証明）: 返り値は `m + 1`、`out` の先頭 `m + 1` 要素が連鎖 `ch 0 = to`、…、`ch m = from`（`Ot`）、以降の要素は変わらない。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて `400 * m + 200` 以下、書き込みは `m + 1` 回以下、追加領域は局所変数だけ。`m < n` なので全体で `O(n)`。

証明は `Proofs/TreePathExec.lean`（1 反復 `b_body`、`while_exec`（`m - t` についての帰納）、全体 `body_exec`、途中状態 `Ot`）、`Proofs/TreePathPrepare.lean`/`Proofs/TreePathCall.lean`（呼び出し）。`tree_root` の出力との接続は `Proofs/TreePathMath.lean` の `tree_path_chain` で、`tree_root` の事後条件 `TreeSpec`（`HeadOK` の CSR 配列、`to` が到達可能）から、前提の連鎖 `ch`（`m = dep[to]`、`ch 0 = to`、`ch m = from`、`m` より前は `from` でない、`parent[ch i] = ch (i+1)`）の存在を導く。C++ のテストは `tests/tree_path.cpp`（`tree_root` との合成で、元の `Tree::path` と照合する）。
