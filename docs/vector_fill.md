# vector_fill

`cp::vector_fill(std::vector<long long> &x, long long value)` は `x` の全要素を `value` にする。元の `experiments/library/cpp/template/template.cpp` の `fill` 系の操作（`fill(ALL(x), value)`）に対応し、変換器が扱える形の添字ループで書いた。

- 前提: `x.size() < 2^31`。`value` は `long long` の全値。
- 結果: 呼び出し後の `x` は、要素数が変わらず、全要素が `value`。
- 時間と領域: 時間 O(x.size())、追加領域は局所変数 2 個（`i` と値の引数）。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `19 * x.size() + 30`。vector の記憶域の仕事量は `x.size()` 回の書き込み。

これは vector への書き込みを扱う最初の部品である。共通の入れ子 vector 生成器（`verifier/nested_ir.py`）が Lean の本体（`Proofs/Generated/VectorFill.lean`）を生成し、`Proofs/VecWrite.lean` の実行器 `pexecW`・健全性 `soundW`（vector の内容を状態に持つ）と `Proofs/VecWriteCall.lean` の呼び出し定理 `call_vecw_unit` を使って、`Proofs/VectorFillCall.lean` の `vector_fill_correct` が、前提を満たす全入力について、結果、停止、未定義動作の不在（添字が範囲内であること）、呼び出し後の内容（`List.replicate x.size() value`）、仕事量と追加領域の上界を証明する。

定理に含めていないこと: 呼び出し側の `x` 以外のオブジェクトが変化しないこと（個数、使用領域は保存を証明している）、`x` の容量が変わらないことの明示的な主張。C++ のテストは `tests/vector_fill.cpp` で、長さ 0〜20 と極値、大きな乱数 vector を確認する。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化は `long long`（`template ... vector_fill<long long>(...)` で明示的に具体化している）。
