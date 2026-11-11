# tree_find_root

`cp::tree_find_root(parent, n)` は、根を指定しない親配列で与えられた木の根を返す: `parent[i] == i` または `parent[i] < 0` を満たす最後の添字 `i < n`、なければ `-1`。`experiments/library/cpp/tree/tree.hpp` のコンストラクタ `Tree(vector<int> &parent)` の根を探すループを書き直した。

元のソースからの変更:
- 条件 `parent[i] == i || parent[i] < 0` を、2 つの入れ子の `if`（`parent[i] == i` でなければ `parent[i] < 0` を調べる）で書く（短絡評価と同じ結果）。
- 根が見つからない場合、元は `assert(r >= 0)` で失敗する。ここでは返り値 `-1` で表し、呼び出し側が確かめる。
- 根を決めたあとの辺の構築（`tree_edges_from_parent`）と `build_depth`（`tree_root`）は別の公開部品。

前提: `0 <= n < 2^31 - 1`、`parent.size() >= n`。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeFindRoot.lean` を生成し、`Proofs/Cpp/TreeFindRoot.lean` が前提を満たす全入力について次を証明する。

- `tree_find_root_spec`: `0 <= n` のとき、返り値は `lastRoot parent n`（`i < n` で `IsRoot parent i`（`parent[i] == i` または `parent[i] < 0`）を満たす最後の `i`、なければ `-1`。`lastRoot_spec`）。
- tick 数はちょうど `n + 1`。

差分テスト（`tests/diff/tree_find_root.py`）と C++ のテスト `tests/tree_find_root.cpp`（自己親・負の親・大きな値を含むランダムな配列で、元のループと照合する）で翻訳と実装を確かめる。
