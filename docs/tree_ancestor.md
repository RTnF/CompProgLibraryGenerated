# tree_ancestor

`cp::tree_ancestor(anc, v, i)` は、ダブリング表 `anc` から頂点 `v` の `i` 個先の祖先を返す。`experiments/library/cpp/tree/tree.hpp` の `Tree::ancestor` から、検証できる形に書き直した。表 `anc[k][x]` は `x` の `2^k` 個先の祖先（`doubling` が作る形）。

元のソースからの変更:
- 表は `Tree` のメンバー `ancestor_` ではなく引数 `anc` で渡す（クラスの他のメンバーを使わない関数なので、元の `const` メンバー関数と同じ結果になる）。
- ビット `j` の判定 `i & j` を `(i / j) % 2 == 1` と書く。`i >= 0` で `j` が 2 のべきなら同じ値である（検証済みの式の言語が符号なしの型にしかビット演算を持たないため）。
- 元の `j <<= 1` は `j = j * 2`、`k++` は `k = k + 1` と書く。ループは `while` で、反復回数は `i` の上位ビットまでの桁数。

前提: `0 <= i < 2^30`（`j` が符号付き `int` であふれない）、`0 <= v < n`、`2^k <= i` を満たす各 `k` について行 `anc[k]` が存在して `n` 個の要素を持ち、すべて `[0, n)` にある。`n < 2^31`。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeAncestor.lean` を生成し、`Proofs/Cpp/TreeAncestor.lean` が前提を満たす全入力について次を証明する。

- `tree_ancestor_spec`: `f` が `[0, n)` をそれ自身に写し、`0 <= v < n`、`0 <= i < 2^30`、表が `f` の `2^k` 回の合成になっている（`TabOK`: `2^k <= i` の各 `k` と `0 <= x < n` について `anc[k][x] == f^(2^k)(x)`）とき、返り値は `f^i(v)`（`i` 回適用）。`f` は任意の写像でよく、親配列そのものでなくてよい。
- tick 数はちょうど `bitWidth i + 2`（`O(log i)`）。ループの不変条件は、`j = 2^k` と、`v` がそれまでに読んだ下位 `k` ビットぶん進んでいること（`f^(i mod 2^k)(v)`。`mod_two_pow_succ`）。
- 定理に含めていないこと: `anc` が `doubling` の出力であること（`doubling` の定理と合わせて使う）、`lowest_common_ancestor` などの他の `Tree` の機能。

差分テスト（`tests/diff/tree_ancestor.py`）と C++ のテスト `tests/tree_ancestor.cpp`（行数 0〜8 のランダムな表と一般の写像を素朴な反復と照合し、`i = 2^30 - 1` の 30 行の表も確認する） で翻訳と実装を確かめる。

