# pow_mod

`cp::pow_mod(base, exp, m)` は繰り返し二乗法で `base^exp mod m` を返す。元の `experiments/library/cpp/modint/modint.hpp` の `ModInt::pow` の中核に対応し、クラスの状態を持たない `uint64_t` の関数に直した。

- 前提: `1 <= m <= 2^32`（このとき途中の積 `result * b` と `b * b` は `2^64` 未満に収まる）。`base` と `exp` は `uint64_t` の全値。
- 結果: `base^exp % m`（`m = 1` なら 0、`exp = 0` なら `1 % m`）。結果は `m` 未満。
- 時間と領域: 乗算は `exp` のビット数以下の回数（最大 64 回）、追加領域は定数個の局所変数。仕事量は 3000 以下を証明している（呼び出し側の引数評価を除く）。

ループは `e != 0` の間、`e & 1` で奇数なら `result` に `b` を掛け、`b` を二乗し、`e` を右に 1 ビットずらす。`Proofs/PowModStep.lean` が、直線的なスカラー断片の実行器 `pexec`（`Proofs/StraightLine.lean`）の上で 1 反復の結果（`iter`）とループ全体（`loop_exec`）を求め、`pw_spec` が `pw m n r b e = r * b^e % m` を示す。`Proofs/PowModCall.lean` の `pow_mod_correct` が、前提を満たす全入力について呼び出しの結果、停止、未定義動作の不在（`1 % m` と `% m` の除数が 0 でないこと、積が桁あふれしないこと）、仕事量と追加領域の上界を証明する。

定理に含めていないこと: `m = 0` や `m > 2^32` の入力（前提違反）、呼び出し側のオブジェクトの内容が変化しないこと（個数、使用領域、仕事量、スコープは保存を証明している）。C++ のテストは `tests/pow_mod.cpp` で、128 bit の剰余を独立した基準にして、境界値と乱数、フェルマーの小定理を照合する。
