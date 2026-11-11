# tree_height

`cp::tree_height(cost_depth0, cost_depth1, h, n)` は、`h[i] = max(cost_depth0[i], cost_depth1[i])` を `i < n` について書く。`experiments/library/cpp/tree/tree.hpp` の `Tree::height`（各頂点から最も遠い頂点までの距離）の最後のループを、検証できる形に書き直した。`Cost` はテンプレートのまま残し、検証した具体化は `long long`。

`Tree::height` は、直径の両端 `f0`、`f1` を根にした 2 回の `build_depth` が作る `cost_depth` を使う。その 2 つの配列は呼び出し側が `tree_root` で求める: 任意の根（例えば 0）で `tree_root` を呼んだときの最遠点 `stk[n]` が一方の端 `f0`、`f0` を根にしたときの最遠点が他方の端 `f1`。`f0` と `f1` を根にした `cost_depth` を `cost_depth0`、`cost_depth1` として渡す。

元のソースからの変更:
- 2 本の `cost_depth` と出力 `h` を引数にする。元は `Tree` のメンバーの `cost_depth_[f0]`、`cost_depth_[f1]` を使い、`diameter()` と `build_depth` を内部で呼ぶ。
- `std::max(a, b)` を比較と分岐で書く（`a < b` なら `b`、そうでなければ `a`。同じ値）。
- `h` は呼び出し側が用意した長さ `n` 以上の vector で、先頭 `n` 個を書く（元は新しい vector を返す）。
- 元の関数全体としての検証（直径の両端を求め、距離の最大性を示すこと）は未完了。`Tree::diameter`、`Tree::height` は `docs/experiments_status.md` の違反一覧に残している。

前提: `0 <= n < 2^31 - 1`、`cost_depth0`、`cost_depth1`、`h` がどれも `n` 個以上の要素を持つ。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeHeight.lean` を生成し、`Proofs/Cpp/TreeHeight.lean` が前提を満たす全入力について次を証明する。

- `tree_height_spec`: 任意の `Cost` について、`0 <= n <= h.size()` のとき、終了後 `h[i] == pick cost_depth0[i] cost_depth1[i]`（`a < b` なら `b`、そうでなければ `a`。全順序では大きい方。`Int` では `pick_eq_max`）（`i < n`）、`n` 以降の要素と長さは変わらない。
- tick 数はちょうど `n + 1`。
- 定理に含めていないこと: 2 本の `cost_depth` が直径の両端を根にしたものであることと、そのとき `h[i]` が本当に最遠頂点までの距離であること。

差分テスト（`tests/diff/tree_height.py`）と C++ のテスト `tests/tree_height.cpp`（ランダムな配列で先頭 `n` 個が最大値になり、残りが変わらないことを確認する）で翻訳と実装を確かめる。
