# char_count

`cp::char_count(s)`（`experiments/library/cpp/string/char_count.hpp` の `char_count`）は、文字列 `s` を同じ文字が連続する最大の区間（連、run）に分け、各連の `(文字, 長さ)` を先頭から順に `std::vector<std::pair<char, int>>` で返す。離れた位置にある等しい文字は別の連になる（文字の頻度表ではない）。空の `s` には空の結果を返す。

| 関数 | 内容 | 時間 | 追加領域 |
| --- | --- | --- | --- |
| `char_count(const std::string &s)` | `s` の連の `(文字, 長さ)` の列 | O(n) | O(連の個数)（結果） |

- 前提: `s.size() <= INT_MAX`（長さを `int` に入れる）。
- 境界: `n = 0` は空の結果。`n = 1` は 1 個の連 `(s[0], 1)`。全文字が等しければ 1 個の連 `(s[0], n)`。`'\0'` や負の `char` 値も他の文字と同じに扱う。
- 任意のコンテナ版は `element_count`（`std::string` も渡せる）。

## 元のソースからの変更

- 公開側では `namespace cp` に置き、`std::` を明示し、ヘッダーで定義する関数に `inline` を付けた。本体は元と同じ。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/CharCount.lean` を生成する。`std::string` は各 `char` の数値を入れた `Array Int`、`int n = s.size()` は 32 bit への変換 `Cpp.toSigned 32` に翻訳される。

`Proofs/Cpp/CharCount.lean` の `char_count_spec` が、`s.size() < 2^31` の任意の `s` について、結果が `rle s`（`Proofs/Cpp/Lib/Rle.lean`）に等しいこと、tick 数が `3 n + 2` 以下（走査 `2 n + 1`、結果の返却が連の個数 `≤ n`）であることを証明する。`unrle_rle`（連を展開すると `s` に戻る）と `rle_ok`（各連の長さは正、隣り合う連の文字は異なる）が結果の意味を与える。

差分テスト（`tests/diff/char_count.py`、NUL・負の値・127 を含む）と C++ のテスト（`tests/char_count.cpp`、長さ 9 以下の 3 文字の全文字列と乱択、境界）で翻訳と実装を確かめる。
