# interval_union

`cp::interval_union_inclusive<T>(std::vector<std::pair<T, T>> &v)` は閉区間 `[l, r]` の集まりの和集合を、互いに離れた閉区間の昇順の列として返す。`v` は途中で並べ替えられる。元の `experiments/library/cpp/interval/interval_union.hpp` そのもの。

- 前提: すべての区間で `l <= r`、`v.size() < 2^31`。
- 計算量: O(n log n)（`std::sort` と 1 回の走査）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/IntervalUnion.lean` を生成する。`std::sort` は組の辞書式順序の整列（`Cpp.sortLex`）、構造化束縛 `auto &&[l, r]` は組の成分になる。`Proofs/Cpp/IntervalUnion.lean` の `interval_union_spec` が、任意の全順序 `T` と前提を満たす入力について次を証明する。

- 結果が覆う点の集合は入力と等しい（`cov`）。
- 結果の各区間は `l <= r`（`Valid`）で、隣り合う区間は前の終わりが次の始まりより小さい（`Sep`）。
- 呼び出し後の `v` は `Cpp.sortLex v`（整列結果）。
- tick 数は `1 + sortCost n + 2 n` 以下。

ループ不変条件は、処理済みの先頭部分と結果の被覆が等しいこと、結果の区間の始点が残りの区間の始点以下であること（整列による。`sorted_firsts`）。

差分テスト（`tests/diff/interval_union.py`）と C++ のテスト（`tests/interval_union.cpp`、元の実装の逐語コピーと点の被覆による照合）で翻訳と実装を確かめる。

## 元のソースからの変更

`std::` 修飾と名前空間のみ（2026-11-12 に元の形に戻した。それまでの公開版は 2 本の vector と挿入ソートに書き換えていた）。
