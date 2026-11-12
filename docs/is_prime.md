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

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/IsPrime.lean` を生成し、`Proofs/Cpp/IsPrime.lean` が 5 つの関数を証明する（`unsigned long long` の全値）。数学側は `Proofs/IsPrimeMath.lean`（旧 `Proofs/IsPrimeMr.lean` の純粋な部分: `wrun`/`mrwx`/`mrb`、素数に witness はない `mrwx_prime`、`badBase`、`MRWitnessSet`）と `Proofs/Fermat.lean`。
- `mul_mod_spec`: `a < m` のとき返り値は `a * b mod m`、tick 数はちょうど `2 + bitWidth b`。ループ不変条件は `r, x < m` と `(r + x * y) mod m = a * b mod m`。`r + x` は `r >= m - x` のときだけ `r - (m - x)` にする（`addmod_ge`/`addmod_lt`）。
- `pow_mod_spec`: `x < m`、`2 <= m` のとき返り値は `x^y mod m`、tick 数はちょうど `1 + powLoop m x y`（`powLoop m b e <= 1 + 133 * bitWidth e`）。
- `mr_base_wp`: 返り値は `mrb i`（`i >= 0`）。11 個の `if` は `i` の値で場合分けする（`mr_base_eq`）。
- `mr_witness_spec`: `2 <= n`、`a < n`、`0 <= r < 2^31` のとき返り値は `mrwx n r (a^d mod n)`、tick 数はちょうど `witCost n d r a`（`<= 12804`）。
- `is_prime_spec`: `n` が素数なら `true`（無条件）。仮説 `MRWitnessSet`（「`n < 2^64` の奇数の合成数 `n >= 3` には、先頭 12 個の素数の中に `n - 2` 以下の witness がある」。公表された計算結果で、**Lean では証明していない**。定理の仮説として明示し、公理にはしない）の下で、`true` なら素数。tick 数は `t0 + 160000` 以下。
- 呼び出し先の仕様は tick 数が入力の関数として決まる形（`mul_mod_wp`、`pow_mod_wp`、`mr_witness_wp`）にして、呼び出し元のループの中で `mvcgen` が使う。

差分テスト（`tests/diff/is_prime.py`）と C++ のテストで翻訳と実装を確かめる。

時間と領域: `mul_mod_u64` は反復 64 回以下、`pow_mod_u64` は乗算 128 回以下（計 64 × 64 規模）、`is_prime` は 12 個の基底それぞれに `pow_mod_u64` と高々 `r <= 63` 回の `mul_mod_u64` を行い、全体で O(12 · 64 · 64)。追加領域は局所変数 O(1)。

C++ のテストは `tests/is_prime.cpp`（試し割り、元の実装、`__uint128_t` による乗算・冪・witness の照合、既知の強擬素数、`2^64 - 1` 付近、`-fsanitize=address,undefined`）。
