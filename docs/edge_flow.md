# edge_flow

`cp::FlowEdge<T>` はフロー用の有向辺 `from -> to` の値で、逆辺の位置 `rev`（`to` の隣接リストでの添字）、容量 `cap`、費用 `cost`、番号 `id` を持つ。元の `experiments/library/cpp/graph/edge_flow.hpp` をそのまま公開する（`graph_flow` の辺の型）。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `FlowEdge(from, to, rev, cap, cost)` | 容量は `max(cap, 0)`。`id` に具体化ごとのカウンタ `next_id` の値を入れて 1 増やす | O(1) |
| `FlowEdge(from, to, rev, cap)` | 費用 0 で同じ | O(1) |
| `FlowEdge(from, to, rev)` | 容量・費用 0 で同じ | O(1) |
| `from`, `to`, `rev`, `id`, `cap`, `cost` | 公開フィールド | — |
| `operator<<` | `id: from -> to (cap, cost)` を出力する | O(1) |

- カウンタは `FlowEdge<T>` の具体化ごとに別で、プログラムの開始時に 0。コピーは番号を変えない。構築は 2^31 回未満とする。
- `T` に必要な操作: `0` からの変換、`std::max`、出力。

## 元のソースからの変更

- `namespace cp` に置き、`std::max`・`std::ostream` を明示した。本体は元のまま。

## 検証（新方式、`docs/translation.md`）

`edge`（`docs/edge.md`）と同じく、`next_id` を具体化ごとの状態 `cp.GlobalState_… T tag` に翻訳する（`Proofs/Cpp/Gen/EdgeFlow.lean`）。`std::max(a, b)` は Lean の `max`（全順序で同じ値）。`operator<<` は方針により翻訳から除き、C++ のテストだけで確かめる。

証明（`Proofs/Cpp/EdgeFlow.lean`、任意の `T`）: `init_globals_spec`（初期値 0）、`init_cap_cost_spec`・`init_cap_spec`・`init_spec`（構築した値は `⟨from, to, rev, next_id, max cap 0, cost⟩`、省略した容量・費用は 0、カウンタは 1 増える、1 手）。

C++ のテスト（`tests/edge_flow.cpp`）は 3 種の構築子、負の容量、具体化ごとのカウンタ、`double`、出力を確かめる。差分テスト（`tests/diff/edge_flow.py`、`T = long long` と `int`）は 3 種の構築子を混ぜて 300 個作り、全フィールドを比べる。
