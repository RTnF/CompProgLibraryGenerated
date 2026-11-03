# mat_mul

`cp::mat_mul(const std::vector<unsigned long long> &a, const std::vector<unsigned long long> &b, std::vector<unsigned long long> &c, int n)` は、行優先で持った `n × n` 行列 `a`, `b` の積 `a * b` を `c` に書き込む（各成分は 2^64 を法とする）。`experiments/library/cpp/number/square_matrix.hpp` の `SquareMatrix::operator*=` を、`vector` を 3 本取る平坦な形に直したもので、複数 vector を同時に扱う証明の枠組み（`Proofs/MultiVec.lean`）の最初の利用例でもある。

- 前提: `a.size() == b.size() == c.size() == n * n`、`n * n < 2^31`。`c` は `a`、`b` と別の vector（`a` と `b` が同じ vector でもよい）。`c` の元の内容は使わない。
- 結果: 呼び出し後の `c[i * n + j]` は `(Σ_{k<n} a[i * n + k] * b[k * n + j]) mod 2^64`（証明では `dsum a b n i j n % 2^64`）。`a`、`b` は変化しない。
- 時間と領域: 三重ループで `n^3` 回の反復。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `cI n + 100`（`n` の 3 次式）、vector への書き込みは `n * n` 回。追加領域は局所変数 5 個（`i`、`j`、`s`、`k` と引数 `n`）。

証明は `Proofs/MatMulExec.lean`（実行の補題: `k_body`/`k_loop`、`j_body`/`j_loop`、`i_body`/`i_loop`、`body_exec`、および結果の仕様 `matC_spec`）、`Proofs/MatMulPrepare.lean`（3 本の vector と 1 つのスカラーを束縛する呼び出しの準備 `prepare_mm`）、`Proofs/MatMulCall.lean`（呼び出し定理 `mat_mul_correct`）で行った。共有基盤は `Proofs/MultiVec.lean`・`Proofs/MultiVecCall.lean`（複数 vector の純粋な実行器と健全性、`call_vecm_unit`）、`Proofs/MultiKit.lean`、`Proofs/ForLoopM.lean`・`Proofs/ForLoopC.lean`（添字ループ。`ForLoopC` は各反復で変わる累積変数を持てる）。

定理に含めていないこと: `ModInt` など任意の要素型（要素は `unsigned long long` に固定）、`c` が `a` または `b` と同じ vector である場合（別の vector であることが前提）。C++ のテストは `tests/mat_mul.cpp`（大きさ 0〜14 のランダムな行列を、ループの順序を変えた参照実装と比較）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <型>(...)`）に書いた型だけ。
