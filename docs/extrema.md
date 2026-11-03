# extrema（chmax / chmin）

`cp::chmax(S &a, const T &b)` は `a < b` のとき `a` を `b` にして `true` を返し、そうでなければ何もせず `false` を返す。`cp::chmin` は `b < a` のとき同様に `a` を `b` にする。元の `experiments/library/cpp/template/template.cpp` の `chmax<S, T>` / `chmin<S, T>` と同じ型引数を持つ関数テンプレートのまま公開し、検証した具体化は `S = T = long long`（`template bool chmax<long long, long long>(...)` で明示的に具体化している）。ほかの型の組は、整数型の全組で個別に証明した版が `Proofs/IntegralExtrema*.lean` にある（未公開）。

- 前提: `a` と `b` は有効な `long long` を指す。同じオブジェクトを指してもよい。
- 結果: `chmax` は `a` を `max(a, b)` にし、`a < b` かどうかを返す。`chmin` は `a` を `min(a, b)` にし、`b < a` かどうかを返す。`b` は変わらない。
- 時間と領域: 定数時間、局所変数 1 個（`bool`）。仕事量は 60 以下。

共通の入れ子生成器（`verifier/nested_ir.py`）が C++ の AST から Lean の本体を生成する。スカラーの参照引数（`T &`、`const T &`）は、呼び出し側のセルのアドレスを被呼び出し側の束縛にする方式で扱う（`Proofs/CppNestedCall.lean` の `NArgument.scalarReference`）。`Proofs/ExtremaCall.lean` の `chmax_correct` と `chmin_correct` が、結果、停止、書き込み先のセルだけが変わること（呼び出し側のメモリは `a` のセル以外を保存する）、仕事量と追加領域の上界を証明する。本体の証明は `Proofs/ExtremaRef.lean` にある。

元の実装は `if` ブロックの中で `return 1` していたが、公開版は局所変数 `changed` に結果を置き、最後に 1 回だけ `return` する形に書き換えた（共通生成器のスコープ内 `return` を避けるため）。C++ のテストは `tests/extrema.cpp` で、境界値の全組、同一オブジェクト、乱数列の累積を `std::max` / `std::min` と照合する。
