# extrema（chmax / chmin）

`cp::chmax(S &a, const T &b)` は `a < b` のとき `a` を `b` にして `true` を返し、そうでなければ何もせず `false` を返す。`cp::chmin` は `b < a` のとき同様に `a` を `b` にする。元の `experiments/library/cpp/template/template.cpp` の `chmax<S, T>` / `chmin<S, T>` と同じ型引数を持つ関数テンプレートのまま公開し、検証した具体化は `S = T = long long`（`template bool chmax<long long, long long>(...)` で明示的に具体化している）。ほかの型の組は、整数型の全組で個別に証明した版が `Proofs/IntegralExtrema*.lean` にある（未公開）。

- 前提: `a` と `b` は有効な `long long` を指す。同じオブジェクトを指してもよい。
- 結果: `chmax` は `a` を `max(a, b)` にし、`a < b` かどうかを返す。`chmin` は `a` を `min(a, b)` にし、`b < a` かどうかを返す。`b` は変わらない。
- 時間と領域: 定数時間、局所変数 1 個（`bool`）。仕事量は 60 以下。

新方式（`docs/translation.md`）: `verifier/lean_translate.py` が `Proofs/Cpp/Gen/Extrema.lean` を生成する。型引数は `S`、`T` のまま Lean の型変数になり、`a < b` は `Cpp.HLt S T`、代入 `a = b` は `Cpp.Conv T S`（具体化での C++ の演算）である。`Proofs/Cpp/Extrema.lean` の `chmax_spec`/`chmin_spec` が任意の型引数について結果（比較の結果と、真なら変換した `b`、偽なら `a`）と tick 数 1 を示し、`chmax_int`/`chmin_int` が具体化 `S = T = long long` で `max a b`/`min a b` になることを示す。参照引数 `a` は戻り値の組の第 2 要素として返る（`docs/translation.md`）。差分テストは `tests/diff/extrema.py`。

元の実装は `if` ブロックの中で `return 1` していたが、公開版は局所変数 `changed` に結果を置き、最後に 1 回だけ `return` する形に書き換えた（共通生成器のスコープ内 `return` を避けるため）。C++ のテストは `tests/extrema.cpp` で、境界値の全組、同一オブジェクト、乱数列の累積を `std::max` / `std::min` と照合する。
