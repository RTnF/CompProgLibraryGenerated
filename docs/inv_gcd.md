# inv_gcd

`cp::inv_gcd(out, a, b)` は拡張ユークリッドの互除法で、`gcd` と `a` の逆元に当たる値を求める。AtCoder Library の `inv_gcd`（`experiments/library/cpp/fps/convolution.hpp`）に対応する。

`a' = a mod b`（`[0, b)` の代表元）として、`g = gcd(a', b)`（`a' = 0` なら `g = b`）を `out[0]` に、`0 <= x < b / g` かつ `x * a' ≡ g (mod b)` を満たす `x` を `out[1]` に書く。`g = 1` なら `x` は `a` の `b` を法とする逆元である。

元のソースからの変更:
- 戻り値の `pair<ll, ll>` の代わりに、呼び出し側の `out`（2 要素以上の `vector<long long>`）に書く。ベクトル引数を先頭に置く（検証の枠組みがベクトルのスロットを先に取るため）。
- `a == 0 (mod b)` のときの早期 `return {b, 0}` は書かず、ループが 0 回で終わって同じ `(b, 0)` になる形にした。`safe_mod(a, b)` は関数の先頭に展開した（`a % b` を取って負なら `b` を足す）。`constexpr` は付けない。
- 元の `|m0| < b / g` などのコメントで述べていた不変条件は、Lean の定理として証明した。

前提: `1 <= b`（`long long` の範囲）、`out.size() >= 2`、`a` は `long long` の全値。どの入力でも符号付きオーバーフローは起きない（途中の値の絶対値は高々 `b`）。

結果（`Proofs/InvGcdCall.lean`、一般の入力について証明）: `out[0] = Nat.gcd b an`、`an = a mod b`、`0 <= out[1] < b / out[0]`、`b ∣ out[1] * an - out[0]`。`out[2..]` は変わらない。

時間と領域: ループの反復は `2 * log2(b) + 1` 回以下（`gcd_u64` と同じ `gsteps` の評価）。モデル上の仕事量は呼び出し側の引数評価を除いて `1040 * log2(b) + 900` 以下、書き込みは 2 回、追加領域は局所変数だけ。

証明は `Proofs/InvGcdMath.lean`（ループの不変条件 `Inv`: `s ≡ m0 * a`、`t ≡ m1 * a (mod b)`、`s*|m1| + t*|m0| <= b`、`s*|m0| < b`、`t < s`、`gcd s t = gcd b a`。`inv_step`、`inv_bounds`（途中の値が `b` 以下でオーバーフローしないこと）、`inv_final`、`inv_out`）、`Proofs/InvGcdExec.lean`（前処理 `pre`、1 反復 `b_iter`、`while_exec`、`if_post`、全体 `body_exec`）、`Proofs/InvGcdPrepare.lean`/`Proofs/InvGcdCall.lean`（呼び出し）。C++ のテストは `tests/inv_gcd.cpp`（元の実装との一致、`a` が負の場合、`b` が `LLONG_MAX` 付近、フィボナッチ数、仕様の直接確認、`-fsanitize=address,undefined`）。
