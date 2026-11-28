# floor_sum の仕様と検証

元の `experiments/library/cpp/number_theory/floor_sum.hpp` は保持する。公開正本は `library/number_theory/floor_sum_unsigned.hpp`（API `cp::floor_sum_unsigned`）と `library/number_theory/floor_sum.hpp`（signed 版、API `cp::floor_sum`）で、どちらも `verifier/lean_translate.py` がヘッダから Lean のモデルを生成する（`docs/translation.md`）。数学側の補題（相反則・正規化など）は `Proofs/Math/FloorSumArithmetic.lean`、`Proofs/Math/FloorSumReciprocity.lean`、`Proofs/Math/FloorSumSignedArithmetic.lean` にある。

## 対象とする仕様

整数入力 `0 ≤ n < 2^32`、`1 ≤ m < 2^32`、`0 ≤ a,b < 2^64` に対して、`sum(i=0..n-1, floor((a*i+b)/m))` を `2^64` の剰余として返す仕様を証明対象にする。入力範囲を無制限に広げない。法0では C++ にゼロ除算があり、実行テストでは使わない。結果の積や累積は符号なしの剰余演算であり、自然数の無制限の積・和のままではモデルと一致しない。

元の unsigned 関数のコメントには入力上限がなく、signed 呼び出し側にだけ `n,m < 2^32` の条件がある。unsigned 関数でも条件を明示する必要がある。`n=4294967297,m=1,a=1,b=0` では、元の C++ と生成モデルの結果は `2147483648` であり、数学的な和の64 bit 剰余 `9223372039002259456` と一致しない。`n*(n-1)` が除算前にラップするためである。この入力を UBSan 付き C++ と生成 Lean で再現し、自然数の計算で差が生じることも Lean の `unrestricted_triangle_counterexample` で証明する。元ソースを変更せず、証明対象の前提条件として追跡する。

## 検証（新方式、`floor_sum_unsigned`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/FloorSumUnsigned.lean` を生成する（`unsigned long long` は `UInt64` で、積と和は C++ と同じく 2^64 を法とする）。`Proofs/Cpp/FloorSumUnsigned.lean` の `floor_sum_unsigned_spec` が、`n < 2^32`、`0 < m < 2^32`（`a`、`b` は 64 bit の全値）のとき、返り値が `Σ_{i<n} ⌊(a i + b) / m⌋ mod 2^64`（`directSum`）であることを示す。

- ループの不変条件 `Inv`: 累積した `ans` と残りの和の合計が 2^64 を法として目標に等しい。1 回の反復は `a`・`b` を `m` で割った余りに直し（`normalize`。三角数 `n(n-1)/2` は `n < 2^32` で途中が折り返さないので正確、`triangle_intermediate_exact`）、`a n + b < m` なら終わり、そうでなければ相反則 `directSum_reciprocity` で `(n, m, a, b)` を `((a n + b)/m, a, m, (a n + b) mod m)` に移す（`round`）。
- 停止と計算量: 対 `(m, a mod m)` はユークリッドの互除法と同じ列を進むので、測度 `gcdCost m (a mod m)`（Basic の `gcdCost_step`）が毎回 1 以上減る。tick 数は `gcdCost m (a mod m) + 2` 以下で `O(log m)`。
- 差分テスト（`tests/diff/floor_sum_unsigned.py`）と C++ のテストで翻訳と実装を確かめる。

## 検証（新方式、signed 版 `floor_sum`）

`verifier/lean_translate.py` が `Proofs/Cpp/Gen/FloorSum.lean` を生成する。`uint64_t` から `int64_t` への変換は 2 の補数での値 `Cpp.toSigned 64`（C++23 [conv.integral]）に翻訳する。`Proofs/Cpp/FloorSum.lean` の `floor_sum_spec` は `0 <= n < 2^32`、`1 <= m < 2^32`、`a`、`b` が signed 64 bit の全範囲のとき、返り値が `signedDecode64 (signedSum m a b n)`（総和を 2^64 を法として signed 64 bit に復号した値。総和が範囲内なら総和そのもの: `signedDecode64_exact`）であり、tick 数が `t0 + 10 + 2 * log2 m` 以下であることを示す。

- `a < 0` の補正 `0 - n*(n-1)/2 * ((a2 - a) / m)` は `UInt64.ofInt (triangle n * (a / m))` に等しい（`tri_eq`、`coef_eq`、`ansA_eq`）。`b < 0` も同様（`ansB_eq`）。`a2 - a` は `2^63 + 2^32` 未満なので折り返さない。
- 和の分解は旧来の `Proofs/Math/FloorSumSignedArithmetic.lean` の `signedSum_normalization` から `sum_norm_a`、`sum_norm_b` を導き、非負の係数では `signedSum_of_nat` で `directSum` に移す。`floor_sum_unsigned` の呼び出しには `floor_sum_unsigned_wp`、仕事量には `gcd_bound`（`gcdCost m x <= 3 + 2 log2 m`）を使う。

差分テスト（`tests/diff/floor_sum.py`、型の最小・最大と範囲外の結果を含む）と C++ のテストで翻訳と実装を確かめる。

## 元のソースからの変更

公開版（`library/number_theory/safe_mod.hpp`、`floor_sum_unsigned.hpp`、`floor_sum.hpp`）は、元の `experiments/library/cpp/number_theory/floor_sum.hpp` の3関数（`safe_mod`、`floor_sum_unsigned`、`floor_sum`）をそれぞれ1部品にしたもので、アルゴリズム・式・assert は元のままである。変更は次の3点だけで、いずれも元と同じ入力に同じ結果を返す。

- 名前空間 `cp` に入れ、`ll`/`ull` を `std::int64_t`/`std::uint64_t`（LP64 では同じ型）に書いた。`inline` を付けた。
- `floor_sum_unsigned` の `n = (ull)(y_max / m); b = (ull)(y_max % m);` の冗長な `(ull)` を外した（同じ型）。
- `floor_sum_unsigned` の事前条件 `n < 2^32`、`0 < m < 2^32` をヘッダーに明記した（元は signed 版のみ assert）。

公開ヘッダーから生成したモデルが登録済みのモデルと一致することは公開 bridge 検査（`floor_sum_unsigned`/`floor_sum`/`safe_mod`）が毎回確認する。元ヘッダーとの違いは上の3点だけである（旧方式で行っていた元ヘッダーからの生成モデルの全文照合は、旧変換器とともに削除した）。

