# floyd_warshall

`cp::floyd_warshall(std::vector<long long> &d, int n)` は、行優先で持った距離行列 `d`（`d[i * n + j]` が `i -> j` の辺の長さ、辺がないときは大きな値）を、全点対の最短距離に置き換える（ワーシャル–フロイド法）。`experiments/library/cpp/graph/warshall_floyd.hpp` の `MatrixGraph::warshall_floyd` から、親の行列と負閉路の検出・到達不能の正規化を除き、`vector<vector<>>` を平坦な 1 本の vector に直したもの。

- 前提: `d.size() == n * n`、`n * n < 2^31`、全ての要素が `[0, 2^62)`（2 要素の和が `long long` に収まる）。辺の長さは非負（`Nat` として扱う）。
- 結果: 呼び出し後の `d[p * n + q]` は、頂点 `0 .. n-1` だけを通る `p -> q` の最短の歩道の長さ。正確には `Dm W n p q`（`W p q = d の元の値`）で、`Dm W 0 = W`、`Dm W (k+1) p q = min (Dm W k p q) (Dm W k p k + Dm W k k q)`。さらに `Walk`（辺 1 本、または途中の頂点 `m < k` でつないだ 2 つの歩道）の帰納的な定義で、`Dm W k p q` を長さとする歩道が存在し（`Walk_exists`）、それより短い歩道はない（`Walk_ge`、途中の頂点が `< k` の閉包 `Dm_tri` を使う）ことを示した（`floyd_warshall_shortest`）。要素は `[0, 2^62)` のまま保たれる。
- 時間と領域: 三重ループで `n^3` 回の反復。tick 数はちょうど `1 + n (1 + n (1 + n))`。追加領域は局所変数だけ。

in-place の更新が反復をまたいで正しい理由: 反復 `k` の中で行 `k` と列 `k` は変化しない（`Dm (k+1) p k = Dm k p k`、`Dm (k+1) k q = Dm k k q`。要素が非負なので `min a (a + b) = a`）。証明は `Em W k i j p q`（行 `< i` と行 `i` の最初の `j` 列だけが第 `k+1` 版）を不変条件に、`Proofs/FloydWarshallCall.lean` の `fw_jbody`（内側 1 反復）、`jbody_step`/`ibody_step`/`kbody_step`、三重ループの `body_execF`、呼び出し定理 `floyd_warshall_correct` で行った。数え上げのループの一般形は共有基盤 `Proofs/ForLoop.lean`（`for_loop_run`、`for_stmt_run`: `for (int t = 0; t < n; t++) B` を、本体の仕様から、結果・停止・費用の上界つきで扱う）に切り出した。

定理に含めていないこと: 負の辺、到達不能の正規化（`UNREACHABLE / 2` を超えた値を `UNREACHABLE` にする後処理）、親（経路復元）の行列。C++ のテストは `tests/floyd_warshall.cpp`（大きさ 0〜25 のランダムなグラフを、全頂点を何度も試す素朴な緩和と比較）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <型>(...)`）に書いた型だけ。


## `vector<vector<T>>` の形（`floyd_warshall(std::vector<std::vector<T>> &d)`）

元の `MatrixGraph::mat` と同じ、行の vector で持った正方行列を直接更新するオーバーロード。`n = d.size()`。三重ループの本体は、行へのアクセス `d[i][k]` などを別々の宣言に分けて書いてある（`T dik = d[i][k]; T dkj = d[k][j]; T via = dik + dkj; T dij = d[i][j]; if (via < dij) d[i][j] = via;`）。

- 前提: すべての行の長さが `d.size()`、全ての要素が `[0, 2^62)`、`n + 1 < 2^31`。時間 `O(n^3)`、追加領域 `O(1)`（局所変数 8 個）。
- 証明: `floyd_warshall_vec_spec`（下の新方式の節）。呼び出し後の各行の内容が `Dm W n p q`（平らな形と同じ再帰。`W` は元の行列）、行の長さは変わらない。
- 定理に含めていないこと: 負の辺、親の行列、行の長さが `d.size()` でない入力。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/FloydWarshall.lean` を生成する（2 つの多重定義は `floyd_warshall_vec_int` と `floyd_warshall_vec`）。`Proofs/Cpp/FloydWarshall.lean` が `T = long long`（Lean では `Int`）について次を証明する。

- `floyd_warshall_vec_int_spec`（平らな形）と `floyd_warshall_vec_spec`（行の vector）: 要素が非負のとき、終了後の `d[p][q]`（`d[p * n + q]`）は `Dm W n p q`、tick 数はちょうど `1 + n (1 + n (1 + n))`。
- 三重ループの不変条件は、ラウンド `k` の行 `< i` と行 `i` の先頭 `j` 個を更新した状態 `Em W k i j`（旧方式の `Proofs/FloydWarshallCall.lean` の定義と補題 `Em_col`・`Em_row`・`Em_next`・`Em_end` を使う）。1 回の比較と更新は `fstep`/`nstep'`。
- `Dm W n p q` が最短の歩道の長さであることは `Walk_ge`・`Walk_exists`（同じファイル）が示す。

差分テスト（`tests/diff/floyd_warshall.py`、両方の形）と C++ のテスト `tests/floyd_warshall.cpp` で翻訳と実装を確かめる。
