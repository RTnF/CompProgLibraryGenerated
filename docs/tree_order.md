# tree_order

`cp::tree_order(head, target, parent, ord, root, n)` は、根付き木の幅優先の頂点の並びを `ord` に書く。`tree_full_dp` に渡す `ord`（各頂点が親より後に来る並び）を作るための部品で、元のソース（`experiments/library/cpp/tree/tree.hpp` の `Tree::full_tree_dp`）が再帰の呼び出し順で暗黙に持っていた「親が先」の順序に相当する。

木は CSR 配列（頂点 `v` の隣接頂点は `target[head[v] .. head[v + 1])`）と、`tree_root` が書く親配列 `parent`（`parent[root] == root`、他の頂点 `w` では `w` から `root` への経路上の隣）で渡す。`ord[0] = root` から始め、`ord[i]` の子（`parent[w] == ord[i]` を満たす隣接頂点 `w`）を末尾へ追加していく。

前提: `n >= 1`、`n + 2 < 2^31`、`head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size() < 2^31 - 1`、すべての `target[p]` が `[0, n)`、グラフは対称な木（連結、自己ループ・閉路・多重辺なし）、`0 <= root < n`、`parent` は上のとおり（`parent.size() == n`）、`ord.size() == n`（呼び出し前の中身は何でもよい）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeOrder.lean` を生成し、`Proofs/Cpp/TreeOrder.lean` が前提を満たす全入力について次を証明する。

- `tree_order_spec`: 外側のループの `L` 回目のあと `ord[0 .. cnt)` は純粋なモデル `Proofs/Math/TreeOrderMath.lean` のキュー `qrun ... L` に等しく（`OInv`）、内側のループは頂点 `Q[L]` の先頭 `k` 本の弧から見つけた子を足した列に等しい（`IInv`、`inner_child`、`inner_skip`）。
- `tree_order_correct`: 前提（`TO`、`head` の要素が非負で広義単調増加、`target` の要素が非負、`ord.size() == n`）のもとで、終了後の `ord` は `0 .. n - 1` の順列（範囲内で単射）、`ord[0] == root`、`j >= 1` の各 `ord[j]` の親は `j` より前の位置にある（親が子より先）。純粋なモデルの性質は `order_spec`。
- tick 数は `n + 1 + W` 以下で、`W`（訪れた頂点の弧の数の和）は `head[n] = m` 以下（`W_le`）。全体で `O(n + m)`。
- 定理に含めていないこと: 前提を破る入力（未定義動作）、`parent` を作る部分（`tree_root`）。

差分テスト（`tests/diff/tree_order.py`）と C++ のテスト `tests/tree_order.cpp`（ランダムな木で、`ord` が順列であること、`ord[0] == root`、親が子より先であることを、`ord` の初期値を乱数にして確かめる） で翻訳と実装を確かめる。
