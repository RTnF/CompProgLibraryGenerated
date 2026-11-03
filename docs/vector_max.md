# vector_max

`cp::vector_max(const std::vector<long long> &x)` は空でない `x` の最大要素を返す。元の `experiments/library/cpp/template/template.cpp` の `max<T>(const vector<T>&)`（`*max_element`）に対応し、変換器が扱える形（`long long` に具体化した添字ループ）に書き換えた。

- 前提: `0 < x.size() < 2^31`。空のときは `assert`（検査として扱う）で停止し、定理の対象外である。
- 結果: `x` に含まれ、かつ全要素以上の値。
- 時間と領域: 時間 O(x.size())、追加領域は局所変数 2 個。仕事量は呼び出し側の引数評価を除いて高々 `27 * x.size() + 40`。入力 vector は変更しない。

共通の入れ子 vector 生成器（`verifier/nested_ir.py`）が C++ の AST から Lean の本体（`Proofs/Generated/VectorMax.lean`）を生成する。`Proofs/VectorMaxCall.lean` の `vector_max_correct` が、前提を満たす全入力について、呼び出しの結果、停止、未定義動作の不在（添字が範囲内であること）、仕事量の上界を証明する。実行器は `pexecV`（`Proofs/VecStraight.lean`）、呼び出し定理は `call_vec`（`Proofs/VecCall.lean`）である。

定理に含めていないこと: 呼び出し側の `v` 以外のオブジェクトが変化しないこと、入力 vector の内容が呼び出し後も同じであることの明示的な主張、空 vector での異常終了の証明。

C++ のテストは `tests/vector_max.cpp` で、`std::max_element` を独立した基準として、3 値ベクタ（長さ 1〜7）の全件、極値、乱数の大きなベクタを照合する。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化は `long long`（`template ... vector_max<long long>(...)` で明示的に具体化している）。
