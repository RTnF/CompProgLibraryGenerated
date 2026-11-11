# element_count

`cp::element_count(v)`（`experiments/library/cpp/array/element_count.hpp` の `element_count`）は、列 `v` を同じ値が連続する最大の区間（連、run）に分け、各連の `(値, 長さ)` を先頭から順に `std::vector<std::pair<typename T::value_type, int>>` で返す。離れた位置にある等しい値は別の連になる（列全体の頻度表ではない）。空の `v` には空の結果を返す。

| 関数 | 内容 | 時間 | 追加領域 |
| --- | --- | --- | --- |
| `template <class T> element_count(const T &v)` | `v` の連の `(値, 長さ)` の列 | O(n) | O(連の個数)（結果） |

- 型 `T` は `value_type`・`size()`・`operator[]` を持つコンテナ（`std::vector`、`std::string`、`std::deque` など）。要素は複製でき、`==` が同値関係であること。
- 前提: `v.size() <= INT_MAX`（長さを `int` に入れる）。
- 境界: `n = 0` は空の結果。`n = 1` は 1 個の連 `(v[0], 1)`。全要素が等しければ 1 個の連 `(v[0], n)`。

## 元のソースからの変更

- 不具合の修正: 元のソースはテンプレート引数 `T` をコンテナ型として推論させながら、結果の型 `pair<T, int>` と局所変数 `T pre = v[0]` にも `T` を使っていたため、`std::vector<int>` などの標準コンテナでは具体化できなかった（`tests/imports/element_count.repro.cpp`、`tools/check_import_element_count.py`）。要素の型を `typename T::value_type` に直した。引数の形 `const T &v` は元のままで、意図されていたコンテナ全般（`std::string` なども）で使える。走査の処理は元と同じ。
- 公開側では `namespace cp` に置き、`std::` を明示した。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/ElementCount.lean` を生成する。`T::value_type` を使うテンプレート引数 `T` はランダムアクセスのコンテナとして、要素型 `T_value_type` の `Array` に翻訳する（`std::vector`、`std::string`、`std::deque` の `size()`・`operator[]` はドキュメント上同じ動作）。

`Proofs/Cpp/ElementCount.lean` の `element_count_spec` が、等しさが決定可能な任意の要素型と任意の `v` について、結果が `rle v`（`Proofs/Cpp/Lib/Rle.lean`）に等しいこと、tick 数が `2 n + 2` 以下であることを証明する。`unrle_rle`（連を展開すると `v` に戻る）と `rle_ok`（各連の長さは正、隣り合う連の値は異なる）が結果の意味を与える。`search_util` の `counts` も同じ `rle` を返す。

差分テスト（`tests/diff/element_count.py`、`std::vector<long long>` と `std::vector<int>`）と C++ のテスト（`tests/element_count.cpp`、他のコンテナと要素型を含む）で翻訳と実装を確かめる。
