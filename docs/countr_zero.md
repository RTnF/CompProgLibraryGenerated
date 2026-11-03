# countr_zero

`cp::countr_zero_u64(n)` は `n` の末尾に連続する 0 ビットの個数を返す（C++20 の `std::countr_zero` の `unsigned long long` 版で、`n = 0` なら 64）。`experiments/library/cpp/fps/convolution.hpp` の `countr_zero_constexpr` に対応する。

元のソースからの変更:
- ビット判定 `n & (1 << x)` を、2 で割れるかどうか `n % 2 == 0` と `n = n / 2` の繰り返しに書き換えた（検証した式の言語のビット演算は unsigned 型のみで、`1 << x` は `int` では `x = 31` でオーバーフローする）。結果は元と同じ。
- 引数を `unsigned int` から `unsigned long long` に広げた（`unsigned int` の値はすべてそのまま受け付ける）。
- `n = 0` で元は無限ループ（コメントの前提は `1 <= n`）だったが、`x < 64` の条件を足して 64 を返す（`std::countr_zero(0)` と同じ）。
- `constexpr` は付けない。

前提: なし（`unsigned long long` の全値）。

結果（`Proofs/CountrZeroCall.lean`、一般の入力について証明）: `n ≠ 0` なら返り値 `r` は `2^r ∣ n` かつ `¬ 2^(r+1) ∣ n`、`n = 0` なら 64。

時間と領域: ループの反復は `r + 1` 回以下（高々 64）。モデル上の仕事量は呼び出し側の引数評価を除いて `13100` 以下、追加領域は局所変数だけ。

証明は `Proofs/CountrZeroExec.lean`（反復回数 `cz`、`cz_spec`、条件式 `cond_val`（`&&` の短絡評価）、1 反復 `b_iter`、`while_exec`、全体 `body_exec`）、`Proofs/CountrZeroPrepare.lean`/`Proofs/CountrZeroCall.lean`（呼び出し）。C++ のテストは `tests/countr_zero.cpp`（`__builtin_ctzll` と元の実装との照合、2 冪、`n = 0`、乱数、`-fsanitize=address,undefined`）。
