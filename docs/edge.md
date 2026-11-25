# edge

`cp::Edge<T>` は有向辺 `from -> to` の値で、費用 `cost` と番号 `id` を持つ。元の `experiments/library/cpp/graph/edge.hpp` をそのまま公開する（`ListGraph` の既定の辺の型）。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `Edge(from, to, cost)` | フィールドを引数にし、`id` に具体化ごとのカウンタ `next_id` の値を入れて 1 増やす | O(1) |
| `Edge(from, to)` | 費用 `1` で同じ | O(1) |
| `from`, `to`, `id`, `cost` | 公開フィールド | — |
| `operator<<` | `id: from -> to (cost)` を出力する | O(1) |

- カウンタは `Edge<T>` の具体化ごとに別で、プログラムの開始時に 0。コピーは番号を変えない。カウンタの値が `int` に収まることを前提とする（2^31 回未満の構築）。
- `T` に必要な操作: `T` からの構築と `1` からの変換（2 引数の構築子）、出力（`operator<<`）。

## 元のソースからの変更

- `namespace cp` に置き、`std::ostream` を明示した。本体は元のまま。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がクラスを構造体 `cp.Edge T` に、`next_id` を具体化ごとの状態 `cp.GlobalState_… T tag`（タグは C++ の `T` の綴り）に翻訳する（`Proofs/Cpp/Gen/Edge.lean`）。構築子は状態を受け取り、構築した値と更新した状態を返す。`operator<<` は利用者の決定（2026-10-12、入出力と番号の管理は本質から外れる）により翻訳から除き、C++ のテストだけで確かめる。

証明（`Proofs/Cpp/Edge.lean`、任意の `T`）:

- `init_globals_spec`: カウンタの初期値は 0。
- `init_cost_spec`、`init_unit_spec`: 構築した値は `⟨from, to, next_id, cost⟩`（2 引数では費用 `1`）、カウンタは 1 増える。1 手。

C++ のテスト（`tests/edge.cpp`）は具体化ごとのカウンタ、コピー、`double`、出力を確かめる。差分テスト（`tests/diff/edge.py`、`T = long long` と `int`）は 2 種の構築子を混ぜて 300 個作り、全フィールドを比べる。
