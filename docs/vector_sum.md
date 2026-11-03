# vector_sum

`cp::vector_sum(const std::vector<long long> &x)` は `x` の全要素の和を返す（空なら 0）。元の `experiments/library/cpp/template/template.cpp` の `sum<T>`（`accumulate` を呼ぶテンプレート）に対応し、変換器が扱える形（`long long` に具体化した添字ループ）に書き換えた。

- 前提: `x.size() < 2^31`、各部分和 `x[0] + ... + x[k]` が `long long` に収まること（符号付き桁あふれは検証済みの契約の外）。
- 結果: `x` の要素の総和。
- 時間と領域: 時間 O(x.size())、追加領域は局所変数 2 個。仕事量は呼び出し側の引数評価を除いて高々 `20 * x.size() + 20`。入力 vector は変更しない。

共通の入れ子 vector 生成器（`verifier/nested_ir.py`）が C++ の AST から Lean の本体（`Proofs/Generated/VectorSum.lean`）を生成する。`Proofs/VectorSumCall.lean` の `vector_sum_correct` が、前提を満たす全入力について、呼び出しの結果、停止、未定義動作の不在（添字が範囲内であること、加算が桁あふれしないこと）、仕事量と追加領域の上界を証明する。実行器は読み取り専用ベクタ断片の `pexecV`（`Proofs/VecStraight.lean`）、呼び出し定理は `call_vec`（`Proofs/VecCall.lean`）である。

定理に含めていないこと: 呼び出し側の `v` 以外のオブジェクトが変化しないこと、入力 vector の内容が呼び出し後も同じであることの明示的な主張、前提違反が必ず異常終了すること。

C++ のテストは `tests/vector_sum.cpp` で、`std::accumulate` を独立した基準として、3 値ベクタ（長さ 7 以下）の全件、極値、乱数の大きなベクタを照合する。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化は `long long`（`template ... vector_sum<long long>(...)` で明示的に具体化している）。
