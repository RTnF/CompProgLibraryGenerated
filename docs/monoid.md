# monoid

`cp::MonoidMul<T>`、`cp::MonoidMax<T>`、`cp::MonoidMin<T>` は、1 つの `T` の値 `x` を持つ単位元つきの結合的演算である。セグメント木などで使う。元の `experiments/library/cpp/algebraic_structure/monoid.hpp` から作った。

元のソースからの変更（検証できる形にするために書き換えた。機能は減らしていない）:

- クラステンプレート `template <class T = ll>` の型パラメータ `T` は元のまま残した。検証した具体化は `T = long long`（`template struct MonoidMul<long long>;` などで明示的に具体化している）。`std::numeric_limits<T>::min()`/`max()` は元のまま使い、変換器が整数型の値としてモデルに取り込む。
- 静的メンバー `e()`（`MonoidMul::e()` は 1、`MonoidMax::e()` は `numeric_limits<T>::min()`、`MonoidMin::e()` は `max()`）を元のまま持つ。既定コンストラクタは単位元を直接書く（元は `e()` に委譲する）。
- `op(a, b)` は、フレンド関数ではなく、各モノイドの関数テンプレートにした（クラステンプレートの中のフレンド関数は使われるまで具体化されず、具体化した型についての検証ができないため）。実引数依存の名前探索で見つかるので、`op(a, b)` の呼び出しは元のままである。結果は `MonoidMul(a.x * b.x)`、`a.x < b.x` なら `b`、そうでなければ `a`（`Max`）、`b.x < a.x` なら `b`、そうでなければ `a`（`Min`）。
- `std::max`/`std::min` を `if` 文に書き換えた。

前提と結果（`Proofs/MonoidCall.lean`、一般の入力について証明）:

- `*_default_correct`（既定コンストラクタ）: 引数なしで `1`、`-2^63`、`2^63 - 1` を返す。
- `*_e_correct`（静的メンバー `e()`）: 引数なしで `1`、`-2^63`、`2^63 - 1` を返す。
- `*_new_correct`（`long long` から作る）: 引数の値をそのまま返す。
- `mul_op_correct`: 前提は `x`, `y`, `x * y` が `long long` に収まること（符号付き桁あふれは契約の外）。結果は `x * y`。
- `max_op_correct` / `min_op_correct`: 全 `long long` の組に対して `if x < y then y else x`（`Max`）と `if y < x then y else x`（`Min`）。いずれも前提なし。
- 時間は定数、追加領域は局所変数 3 個以下。

定理に含めていないこと: 結合律や単位元の法則そのもの（C++ のテストで確認している）、呼び出し側のオブジェクトの内容が変化しないこと（個数、使用領域、仕事量、スコープの保存は証明している）。C++ のテストは `tests/monoid.cpp` で、`std::max`/`std::min` と `__builtin_mul_overflow` を独立した基準として、極値を含む全組と乱数の結合律を確認する。
