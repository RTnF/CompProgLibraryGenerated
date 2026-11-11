# tree_path

`cp::tree_path(parent, out, from, to)` は、根 `from` の根付き木で `to` から `from` までの経路を求める。`experiments/library/cpp/tree/tree.hpp` の `Tree::path(from, to)` に対応する。

親配列 `parent`（`tree_root(..., from, n)` の出力）を `to` から `from` まで親へたどり、頂点を `out[0] = to`、`out[i + 1] = parent[out[i]]`、…、`out[len - 1] = from` と書き、`len` を返す。元の `Tree::path` も `to` から `from` の順に並べて返す（C++ のテストで、元の深さ優先探索の結果と一致することを確認している）。

元のソースからの変更:
- 元は `from` からもう一度深さ優先探索して経路を復元する。ここでは `tree_root` が求めた親配列をたどる（木では経路が一意なので同じ頂点列になる）。`from` と `to` が同じ頂点なら長さ 1 の経路 `[from]` を返す。
- 戻り値の `vector<int>` の代わりに、呼び出し側の `out` に書き、長さを返す。`to` が `from` から到達できない場合に元が返す空の経路は、前提条件（`to` が到達可能）として扱う。到達不能かどうかは `tree_root` 後の `parent[to] < 0` で判定できる。

前提: `parent` を `to` から親へ `m` 回たどると初めて `from` に着く（`tree_root` の出力では、`to` が `from` から到達可能なら `m = depth[to]`）。途中の頂点（`to`、`from` を含む）はすべて `[0, parent.size())` にある。`out.size() >= m + 1`、`m + 1 < 2^31`。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreePath.lean` を生成し、`Proofs/Cpp/TreePath.lean` が前提を満たす全入力について次を証明する。

- `tree_path_spec`: `parent` を `to` から `m` 回たどると初めて `from` に着く（`up parent to m = from`、`j < m` では `from` でない）、`m + 1 <= out.size()`、`m < 2^31` のとき、返り値は `m + 1`、`out[j] == up parent to j`（`j <= m`。`out[0] = to`、`out[m] = from`）、以降の要素と長さは変わらない。`while` ループの停止は測度 `m - k` で示す。
- tick 数はちょうど `m + 2`。`m < n` なので全体で `O(n)`。
- `tree_root` の出力がこの前提を満たすこと（`m = depth[to]`）は、旧方式の `Proofs/TreePathMath.lean` の `tree_path_chain` が示している。`tree_root` の移行時に新方式へ移す。

差分テスト（`tests/diff/tree_path.py`）と C++ のテスト `tests/tree_path.cpp`（`tree_root` との合成で、元の `Tree::path` と照合する）で翻訳と実装を確かめる。
