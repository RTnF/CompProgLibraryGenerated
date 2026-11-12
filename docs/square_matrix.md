# square_matrix

行優先で持った `n × n` 行列（長さ `n * n` の `std::vector<T>`）に対する演算 `cp::mat_mul`、`cp::mat_add_assign`、`cp::mat_sub_assign`、`cp::mat_zero`、`cp::mat_negate`、`cp::mat_identity`、`cp::mat_equal`、`cp::mat_pow`。`experiments/library/cpp/number/square_matrix.hpp` の `SquareMatrix`（`operator*=`、`+=`、`-=`、零行列、単位行列）を、`vector` を引数に取る平坦な形に直したもの。複数 vector を同時に扱う証明の枠組み（`Proofs/MultiVec.lean`）を使う。

| 関数 | 結果 | 時間 | 追加領域 |
| --- | --- | --- | --- |
| `mat_mul(a, b, c, n)` | `c = a * b`（`c[i * n + j] = (Σ_{k<n} a[i * n + k] * b[k * n + j]) mod 2^64`） | `O(n^3)` | `O(1)` |
| `mat_add_assign(a, b, n)` | `a[i] = (a[i] + b[i]) mod 2^64`（`i < n * n`） | `O(n^2)` | `O(1)` |
| `mat_sub_assign(a, b, n)` | `a[i] = (a[i] - b[i]) mod 2^64`（`i < n * n`） | `O(n^2)` | `O(1)` |
| `mat_zero(a, n)` | `a[i] = 0`（`i < n * n`） | `O(n^2)` | `O(1)` |
| `mat_negate(a, n)` | `a[i] = (0 - a[i]) mod 2^64`（`i < n * n`。元の単項 `operator-` に相当） | `O(n^2)` | `O(1)` |
| `mat_identity(a, n)` | `a[i * n + j] = (i == j)`（`i, j < n`） | `O(n^2)` | `O(1)` |
| `mat_equal(a, b, n)` | 先頭 `n * n` 要素がすべて等しければ `true`（元の `operator==` に相当。早期 return でなく旗 `same` を立てて最後まで走査する） | `O(n^2)` | `O(1)` |
| `mat_pow(a, r, y, t, n, e)` | `r = a^e`（`e = 0` は単位行列。`r[i * n + j] = PW(a, e)[i][j]`。`PW(A, 0) = I`、`PW(A, k + 1) = PW(A, k) * A` で、積は `mat_mul` と同じ mod 2^64）。`y`、`t` は作業用。繰り返し二乗法（下位ビットが 1 のとき `r *= y`、毎回 `y *= y`、`e /= 2`）。`a` は変化しない | `O(n^3 log e)` | `O(1)` |

- 前提: 各 vector の長さは `n * n` 以上、`n * n < 2^31`（`mat_pow` は `n * n < 2^31 - 1`、`r`、`y`、`t` の長さも `n * n`、`a`、`r`、`y`、`t` は互いに別の vector）、値は `unsigned long long`。`a`、`b`、`c` は互いに別の vector（`mat_mul` の `a` と `b` は同じでもよい）。`mat_mul` の `c` の元の内容は使わない。`b` は変化しない。範囲外の添字は読まない。
- 時間は、モデル上の仕事量が `mat_mul` で `n` の 3 次式、他は `n * n` の 1 次式（`mat_identity` は `n` の 2 次式、反復ごとの定数は証明の定理に明記）。追加領域は局所変数の個数（高々 5 個）で `n` によらない。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/SquareMatrix.lean` を生成する。`Proofs/Cpp/SquareMatrix.lean` が次を証明する。

- 任意の要素型 `T` について（代数的な仮定なし）: `mat_add_assign_spec`、`mat_sub_assign_spec`、`mat_zero_spec`、`mat_negate_spec`（先頭 `n * n` 要素が成分ごとの値、残りは変わらない: `EW`）、`mat_identity_spec`（`Idf`）、`mat_equal_spec`（返り値が `true` ⇔ 先頭 `n * n` 要素が等しい）、`mat_mul_spec`（`c[i n + j] = MM a b n i j n`、ループの順に足した積和）。tick 数はそれぞれ `1 + n^2`、`1 + n (1 + n)`、`1 + n (1 + n (1 + n))` ちょうど。
- `T = unsigned long long`（`UInt64`）について `mat_pow_spec`: `r` の先頭 `n × n` 要素が `PW n A e`（`Proofs/MatPowMath.lean`。積は 2^64 を法とする）。ループの不変条件は `R · Y^e ≡ A^E`（1 回の反復は `pow_round`。結合則 `mulF_assoc`、二乗の冪 `PW_sq`）。`mat_mul` の呼び出しは、その結果を明示した仕様 `mat_mul_wp`（`mulRes`）で扱う。tick 数は `O(n^3 log e)`。

差分テスト（`tests/diff/square_matrix.py`、全関数）と C++ のテストは `tests/square_matrix.cpp`（大きさ 0〜14 のランダムな行列に対して、ループ順を変えた積の参照実装、成分ごとの和差、零行列、単位行列、`I * A == A * I == A`、フィボナッチ行列の冪を比較）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <unsigned long long>(...)`）だけ。

## 元のソースからの変更

- 元の `SquareMatrix<T, N>`（非型テンプレート引数 `N` のクラス、`operator*`、`operator==`、`pow` を持つ）は、変換器が扱えない C 配列と非型テンプレートを避け、`vector` と `int n` に置き換えた。`operator-` が何もしない、`operator==` が存在しないメンバーを使う、`pow` が移植できない書き方、という元の不具合は引き継いでいない。
- `operator==` / `!=` は `mat_equal`（`!=` は `!mat_equal(a, b, n)`）、冪 `pow` は `mat_pow` として移植した。`mat_pow` は、元の `r *= y`・`y *= y` が作る一時行列の代わりに作業用の vector `t` を引数に取り（結果を `t` に書いて `r`/`y` へ写す）、`e` は `unsigned long long`（元は `long long` で、負の `e` は元では終わらないため非負に限る）。`+`/`-`/`*` を返す形（コピーを作る形）は `mat_add_assign` などの代入形で足りるので別関数にしない。
