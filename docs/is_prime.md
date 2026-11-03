# is_prime

`cp::is_prime(n)` は 64 bit 整数 `n` の素数判定（決定的ミラー–ラビン法）で、`experiments/library/cpp/number_theory/is_prime.hpp` の `is_prime` に対応する。基底は元と同じく先頭 12 個の素数 `2, 3, 5, …, 37` を、`基底 <= n - 2` の間この順に使う。

同じヘッダーに、判定の部品を公開関数として置いた。

| 関数 | 内容 | 前提 |
| --- | --- | --- |
| `mul_mod_u64(a, b, m)` | `a * b mod m`（途中の値が 2^64 を超えない 2 倍法） | `a < m`、`b < m` |
| `pow_mod_u64(x, y, m)` | `x^y mod m`（繰り返し二乗法） | `x < m`、`2 <= m` |
| `mr_base(i)` | `i` 番目の基底（`i = 0..11` で `2, 3, …, 37`、それ以上は 37） | `i >= 0` |
| `mr_witness(n, d, r, a)` | `a` が `n` の合成性の証拠（ミラー–ラビンの witness）なら `true` | `2 <= n`、`a < n`、`n - 1 = d * 2^r` のとき意味を持つ |
| `is_prime(n)` | 素数判定 | `unsigned long long` の全値 |

元のソースからの変更:
- `(__uint128_t)a * b % m` を使わず、`mul_mod_u64` の 2 倍法（`u + v` は `u >= m - v` のときだけ 2^64 を超えるので、その場合は `u - (m - v)` に置き換える）で積を求める。途中の値はすべて `m` 未満で、結果は元と同じ。`__uint128_t` を使わないので検証した言語の範囲に収まる。
- ラムダ `powmod64` を `pow_mod_u64` に、基底の列挙 `{2, 3, …, 37}` を `mr_base` に分けた。`p > n - 2` での `break` は、基底が増える順なので「`p <= n - 2` のときだけ試す」と同じ結果になる。内側の `break` は旗 `cf` を使うループ条件 `i < r - 1 && cf` にした。
- `n & 1` を `n % 2`、`d >>= 1` を `d = d / 2` に書き換えた（ビット演算は検証した言語の unsigned 型に限られるため）。
- 名前空間 `cp` に置き、`mul_mod_u64` などの小さい関数には `[[gnu::always_inline]]` を付けた（変換器が呼び出し元へ展開する。`docs/scalar_converter.md`）。
- 元と同じ入力に同じ結果を返すことを `tests/is_prime.cpp` で、元の実装（`__uint128_t` 版）との照合により確認している。

結果（`Proofs/IsPrimeCall.lean`。`unsigned long long` の全値について証明）:
- `mul_mod_u64_correct`: 返り値は `(a * b) % m`。
- `pow_mod_u64_correct`: 返り値は `(x ^ y) % m`。
- `mr_base_correct`: 返り値は `mrb i`（上の表）。
- `mr_witness_correct`: 返り値は `mrwx n r (a ^ d % n)`（Lean のモデル。`a^d ≡ 1` または `a^(d·2^i) ≡ -1`（`0 <= i < r`）でなければ `true`）。さらに `n - 1 = d * 2^r` かつ `0 < a` のとき、`true` なら `n` は素数でない（素数に witness はない。`Proofs/IsPrimeMr.lean` の `mrwx_prime`、フェルマーの小定理と `y^2 ≡ 1` の解の議論）。
- `is_prime_correct`: 返り値は `ispSpec n`。`n` が素数なら `ispSpec n = true`（無条件で証明）。逆方向「`ispSpec n = true` なら `n` は素数」は仮説 `MRWitnessSet`（「`n < 2^64` の奇数の合成数 `n >= 3` には、先頭 12 個の素数の中に `n - 2` 以下の witness がある」。先頭 12 個の素数は `3.18 × 10^23` 未満のすべての `n` に対する決定的な基底の集合であるという、公表された計算結果）の下で証明した。**この仮説は Lean では証明していない**。定理は仮説として明示し、公理にはしていない。
- すべての定理に、呼び出しの前後のモデル上の仕事量・追加領域・記憶の復元が付く（`ScalarPostMB`）。

時間と領域: `mul_mod_u64` は反復 64 回以下、`pow_mod_u64` は乗算 128 回以下（計 64 × 64 規模）、`is_prime` は 12 個の基底それぞれに `pow_mod_u64` と高々 `r <= 63` 回の `mul_mod_u64` を行い、全体で O(12 · 64 · 64)。モデル上の仕事量は呼び出し側の引数評価を除いて `TOPC + 400`（`Proofs/IsPrimeRun.lean`、約 6.4 × 10^7）以下、追加領域は局所変数 O(1)。

証明の構成: `Proofs/IsPrimeBody.lean`（関数本体の式）、`Proofs/IsPrimeExec.lean`（乗算・冪・witness 1 反復の実行）、`Proofs/IsPrimeWit.lean`（witness を、前に局所変数が並ぶ位置にも置ける形で証明。`is_prime` の中へ展開された `mr_witness` に使う）、`Proofs/IsPrimeMr.lean`（素数に witness がないこと）、`Proofs/IsPrimeTop.lean`（`mr_base`/`is_prime` の本体と生成モデルの一致）、`Proofs/IsPrimeRun.lean`（`is_prime` 全体の実行、`ispSpec`）、`Proofs/IsPrimeSpec.lean`（素数と `ispSpec`）、`Proofs/IsPrimeFun.lean`（5 つの関数の本体全体）、`Proofs/IsPrimePrepare.lean`/`Proofs/IsPrimeCall.lean`（呼び出し）。C++ のテストは `tests/is_prime.cpp`（試し割り、元の実装、`__uint128_t` による乗算・冪・witness の照合、既知の強擬素数、`2^64 - 1` 付近、`-fsanitize=address,undefined`）。
