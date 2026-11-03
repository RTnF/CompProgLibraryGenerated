# rolling_hash

`cp::RollingHash<T>` は整数列の多項式ハッシュ（`experiments/library/cpp/string/rolling_hash.hpp` の `SimpleRollingHash`）である。法は Mersenne 素数 `2^61 - 1`、基数は 131。列 `s`（`n` 要素）から `hash_sum_`（`hash_sum_[i]` は先頭 `i` 個のハッシュ、`hash_sum_[i + 1] = (hash_sum_[i] * 131 + s[i]) mod (2^61 - 1)`）と `pows`（`pows[i] = 131^i mod (2^61 - 1)`）を `O(n)` で作り、部分列のハッシュを `O(1)` で返す。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `RollingHash(const std::vector<T> &s)` | `hash_sum_` と `pows` を作る | O(n) |
| `hash(l, r)` | `s[l, r)` のハッシュ（`0 <= l <= r <= n`）。値は `[0, 2^61 - 1)` | O(1) |
| `hash(a)` | `s[0, a)` のハッシュ | O(1) |

型 `T` はテンプレート引数のままである。検証した具体化は `RollingHash<int>`（`template class RollingHash<int>;` で明示的に具体化している）。前提条件は `0 <= s[i] < 2^31`、`s.size() < 2^31 - 1`。

元のソースからの変更（検証できる形にするために書き換えた）:

- フィールド `n_` は持たない（常に `hash_sum_.size() - 1` に等しい）。基数 131 は構成子の局所変数にした。元の `mul` と `mod`（`rh_in`）は同じ演算でインラインに書いた（`mod61` と同じ計算）。
- 文字列を受け取る版、`match`、`match_custom`、`starts_with`、`ends_with` は含めていない（`std::string` と `npos` が未対応。台帳の違反一覧に載せている）。

証明する内容（`Proofs/RollingHashCall.lean`、一般の入力について）:

- `rolling_hash_build_correct`（構成子）: `hs`、`pw` が標準の構成子で作られた直後（長さ `n + 1`）で、`s` が前提条件を満たすとき、実行後に `hs = Hs 131 S n`（先頭 `i` 個のハッシュの漸化式の列）、`pw = Ps 131 n`（131 の冪の列）。仕事量は `2120 * n + 400` 以下、追加領域は局所変数の個数で押さえる。
- `rolling_hash_hash_correct`（`hash(l, r)`）: `hs`、`pw` が上の列であり `l <= r <= n` のとき、結果は `S[l, r)` の多項式ハッシュ `polyHash 131 ((S.drop l).take (r - l))`（Horner 法を `2^61 - 1` で割った余り）に等しい。

定理に含めていないこと: メンバー初期化子 `hash_sum_(s.size() + 1)`、`pows(s.size() + 1)` は標準ライブラリの `std::vector<T>(size_type)` の契約による（`docs/trust_policy.md`）。ハッシュの衝突確率（基数が固定なので敵対的な入力には弱い）。負の要素。C++ のテストは `tests/rolling_hash.cpp` で、`__int128` による素朴な多項式ハッシュを基準として、長さ 0〜500 の列（小さい値、乱数、最大値）の全区間を確認する。
