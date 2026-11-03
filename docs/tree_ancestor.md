# tree_ancestor

`cp::tree_ancestor(anc, v, i)` は、ダブリング表 `anc` から頂点 `v` の `i` 個先の祖先を返す。`experiments/library/cpp/tree/tree.hpp` の `Tree::ancestor` から、検証できる形に書き直した。表 `anc[k][x]` は `x` の `2^k` 個先の祖先（`doubling` が作る形）。

元のソースからの変更:
- 表は `Tree` のメンバー `ancestor_` ではなく引数 `anc` で渡す（クラスの他のメンバーを使わない関数なので、元の `const` メンバー関数と同じ結果になる）。
- ビット `j` の判定 `i & j` を `(i / j) % 2 == 1` と書く。`i >= 0` で `j` が 2 のべきなら同じ値である（検証済みの式の言語が符号なしの型にしかビット演算を持たないため）。
- 元の `j <<= 1` は `j = j * 2`、`k++` は `k = k + 1` と書く。ループは `while` で、反復回数は `i` の上位ビットまでの桁数。

前提: `0 <= i < 2^30`（`j` が符号付き `int` であふれない）、`0 <= v < n`、`2^k <= i` を満たす各 `k` について行 `anc[k]` が存在して `n` 個の要素を持ち、すべて `[0, n)` にある。`n < 2^31`。

結果（`Proofs/TreeAncestorCall.lean`、一般の入力について証明）: 表が関数 `f` の `2^k` 回の合成になっている（`TabOK`: `2^k <= i` の各 `k` と各 `x < n` について `anc[k][x] == f^(2^k)(x)`、`anc[k][x] < n`、`x < anc[k].size()`）とき、返り値は `f^i(v)`（`i` 回適用）で `n` 未満である。`f` は任意の写像でよく、親配列そのものでなくてよい。

時間と領域: 反復は `bits(i)`（`i` の 2 進の桁数）回で、モデル上の仕事量は呼び出し側の引数評価を除いて `210 * bits(i) + 300` 以下（`i < 2^30` なので高々 30 桁）。追加領域は局所変数だけ。

証明は `Proofs/TreeAncestorMath.lean`（再帰版 `ancQ` と、表の正しさからの `ancQ T i 0 v = f^i(v)`）、`Proofs/TreeAncestorExec.lean`（`pexecM` による `while` の実行）、`Proofs/TreeAncestorPrepare.lean`/`Proofs/TreeAncestorCall.lean`（呼び出し）。

定理に含めていないこと: `anc` が `doubling` の出力であること（`doubling` の定理と合わせて使う）、`lowest_common_ancestor` などの他の `Tree` の機能。C++ のテストは `tests/tree_ancestor.cpp`（行数 0〜8 のランダムな表と一般の写像を素朴な反復と照合し、`i = 2^30 - 1` の 30 行の表も確認する）。
