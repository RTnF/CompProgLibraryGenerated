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

## 証明

検証した具体化は `element_count<std::vector<long long>>` と `element_count<std::vector<int>>`（ヘッダー末尾の明示的な具体化）。

- モデル: 結果の `vector<pair<A, B>>` は 2 行の入れ子 vector（行 0 が `first`、行 1 が `second`）として変換する。`pair<long long, int>` のように型が違う場合は、範囲が他方を含む広い型（`long long`）の行にし、`int` の値は拡大変換して格納する（`verifier/nested_ir.py`。狭いフィールドの読み書き・`std::sort`・範囲 for は未対応として拒否する）。`if (n == 0) { return ret; }` のように宣言のないブロックからの vector の返却は、ブロックのスコープを作らずに変換する（モデルのスコープ退出は、退出するスコープの根だけを移すため）。
- `Proofs/ElementCountCall.lean` の `element_count_ll_correct`・`element_count_int_correct`: すべての有効な入力 `X`（`v` の要素、`X.length < 2^31 - 1`）について、呼び出しは成功して結果の根を返し、
  - 結果の行 0 は `rle X` の値、行 1 は `rle X` の長さ（`Post.result`。`Proofs/RunLengthMath.lean` の `rle`）。`rle X` は連をつなぐと `X` に戻り（`rleFlat (rle X) = X`）、長さはすべて正で、隣り合う連の値は異なる（`AdjOK`）。
  - `v` のバッファは変わらない（`Post.input`）。呼び出し元のスカラー・束縛・スロット・スコープは元に戻る。
  - 時間: スカラーの仕事量は `90 n + 74` 以下、記憶域の仕事量（`emplace_back` の再確保を含む償却）は `10 n + 3` 以下の増加。
  - 追加領域: 記憶域のピークは `max(呼び出し前のピーク, 呼び出し前の生存領域 + 8 n + 13 − 基準領域)` 以下（`Post.storagePeak`。結果の 2 行の容量は各 `2 × 行の長さ + 1` 以下、`Proofs/AppendCapacity.lean`）。全体のピークは呼び出し元のピークと、スカラーの上界（呼び出し元の局所変数 + 定数）と記憶域の上界の和の大きい方以下（`Post.peak`）。
- 実行の証明は `Proofs/ElementCountExec.lean`（行の要素型 `ty` と行 1 に格納する式 `cv` について一般に示し、2 つの具体化で共有する）。ループ不変条件は、`t` 個を処理した後に `rleExt X t = (閉じた連) ++ [(pre, cnt)]`。行への追加は `Proofs/AppendCapacity.lean`、Family 上の宣言・代入・条件は `Proofs/FamilySteps.lean`。

定理に含めていないこと: `long long`・`int` 以外の要素型（`std::string`、`char` など）とコンテナ（`std::string`、`std::deque` など）の具体化。これらは C++ のテストで確認する。メモリ確保の失敗はモデルの前提（確保は成功する）。C++ のテストは `tests/element_count.cpp` で、長さ 8 以下の 3 値の全列（`vector<int>`・`vector<long long>`・`string`・`deque<int>`）、長さ 300 以下の乱数列、極値、長さ 100000 の 1 個の連、空入力、`vector<string>` を素朴な分割と比較する。
