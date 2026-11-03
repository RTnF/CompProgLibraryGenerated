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

証明:
- `Proofs/MatMulExec.lean`（`mat_mul` の三重ループ。実行の補題 `k_body`/`k_loop`、`j_body`/`j_loop`、`i_body`/`i_loop`、`body_exec`、結果の仕様 `matC_spec`）と `Proofs/MatMulPrepare.lean`（3 本の vector と 1 つのスカラーを束縛する呼び出しの準備）。
- `Proofs/SquareMatrixEw.lean`（`mat_add_assign`/`mat_sub_assign`、二項演算に対して一般の `body_execEw`）、`Proofs/SquareMatrixZero.lean`（`mat_zero`）、`Proofs/SquareMatrixNeg.lean`（`mat_negate`）、`Proofs/SquareMatrixEq.lean`（`mat_equal`。旗の不変条件 `EqInv`、`body_execEq`）、`Proofs/SquareMatrixId.lean`（`mat_identity` の二重ループ。`id_inner_iter`/`id_inner_loop`、`id_outer_iter`/`id_outer_loop`、`body_execId`）、`Proofs/SquareMatrixPrepare.lean`（呼び出しの準備）。
- `Proofs/SquareMatrixCall.lean`: 呼び出し定理 `mat_add_correct`、`mat_sub_correct`、`mat_zero_correct`、`mat_negate_correct`、`mat_identity_correct`、`mat_equal_correct`（返り値は「`i < n * n` で `a[i] = b[i]`」なら 1、そうでなければ 0）、`MatMul.mat_mul_correct`。結果の vector、仕事量、局所領域を `ScalarPostM` で述べる。
- 共有基盤は `Proofs/MultiVec.lean`・`Proofs/MultiVecCall.lean`（複数 vector の純粋な実行器と健全性、`call_vecm_unit`）、`Proofs/MultiKit.lean`、`Proofs/ForLoopM.lean`・`Proofs/ForLoopC.lean`。

テストは `tests/square_matrix.cpp`（大きさ 0〜14 のランダムな行列に対して、ループ順を変えた積の参照実装、成分ごとの和差、零行列、単位行列、`I * A == A * I == A`、フィボナッチ行列の冪を比較）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <unsigned long long>(...)`）だけ。

## 元のソースからの変更

- 元の `SquareMatrix<T, N>`（非型テンプレート引数 `N` のクラス、`operator*`、`operator==`、`pow` を持つ）は、変換器が扱えない C 配列と非型テンプレートを避け、`vector` と `int n` に置き換えた。`operator-` が何もしない、`operator==` が存在しないメンバーを使う、`pow` が移植できない書き方、という元の不具合は引き継いでいない。
- `operator==` / `!=` は `mat_equal`（`!=` は `!mat_equal(a, b, n)`）、冪 `pow` は `mat_pow` として移植した。`mat_pow` は、元の `r *= y`・`y *= y` が作る一時行列の代わりに作業用の vector `t` を引数に取り（結果を `t` に書いて `r`/`y` へ写す）、`e` は `unsigned long long`（元は `long long` で、負の `e` は元では終わらないため非負に限る）。`+`/`-`/`*` を返す形（コピーを作る形）は `mat_add_assign` などの代入形で足りるので別関数にしない。
