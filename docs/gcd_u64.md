# gcd_u64

`cp::gcd_u64(unsigned long long a, unsigned long long b)` は最大公約数をユークリッドの互除法で返す。`gcd(0, 0) = 0`、`gcd(a, 0) = a`（`std::gcd` と同じ）。`experiments/` の `Ratio`、`factorize` などが使う `gcd` の基礎部品。

- 前提: なし（`a`、`b` は `unsigned long long` の全値）。
- 結果: 返り値は `Nat.gcd a b`。
- 時間と領域: ループの反復は `2 * floor(log2 b) + 1` 回以下（`b = 0` なら 0 回）。隣り合う 2 回の反復で `b` が半分未満になることを示した（`mod_half`）。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `80 * log2 b + 100`。追加領域は局所変数 1 個（`t`）と引数 2 個。

証明は `Proofs/GcdU64Call.lean`: `g_iter`（1 反復で `(a, b)` が `(b, a % b)` になる）、`gsteps`/`gsteps_le`（反復回数と対数の上界）、`g_loop`、`body_exec`、呼び出し定理 `gcd_u64_correct`。`std::gcd` の符号付き整数の版（`abs`）は扱わない。

C++ のテストは `tests/gcd_u64.cpp`（0〜60 の全組、極値、最悪例のフィボナッチ数、乱数）。
