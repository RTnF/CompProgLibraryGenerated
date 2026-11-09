# experiments/library と experiments/library3 の重複の整理

2026-10-08 時点。`experiments/library3` は `experiments/library` の古い版か別名の版で、検証の対象は `experiments/library` に一本化する。`library3` のファイルは削除せず、この表で「統合済み（検証対象外）」と記録する。差分に新しい機能があった場合は、`library/` 側へ移してから検証する。

| library3 | library（正本） | 類似度 | 判断 |
| --- | --- | --- | --- |
| `Template/SmallTemplate.hpp` | `template/small_template.hpp` | 1.00 | 同一。正本のみ使う。 |
| `Graph/Dijkstra.hpp` | `graph/dijkstra.hpp` | 0.90 | 正本が新しい。差分は整形と名前。 |
| `SegmentTree/SegmentTree.hpp` | `segment_tree/segment_tree.hpp` | 0.91 | 正本のみ。 |
| `Graph/Lowlink.hpp` | `graph/lowlink.hpp` | 0.87 | 正本のみ。 |
| `Graph/Prim.hpp` | `graph/prim.hpp` | 0.85 | 正本のみ。 |
| `Graph/TopologicalSort.hpp` | `graph/topological_sort.hpp` | 0.85 | 正本のみ。 |
| `Graph/WarshallFloyd.hpp` | `graph/warshall_floyd.hpp` | 0.86 | 正本のみ。 |
| `Graph/BellmanFord.hpp` | `graph/bellman_ford.hpp` | 0.79 | 正本のみ。 |
| `Array/SortUtil.hpp` | `array/sort_util.hpp` | 0.79 | 正本のみ（`inv_perm` は検証済みの `library/array/sort_util.hpp`）。 |
| `NumberTheory/IsPrime.hpp` | `number_theory/is_prime.hpp` | 0.77 | 正本のみ。 |
| `ModInt/ModInt.hpp` | `modint/modint.hpp` | 0.71 | 正本のほうが機能が多い（`mod()`、`set`、`pow` の負の指数、入出力）。検証済みは `library/modint/modint.hpp`。 |
| `NumberTheory/Factorize.hpp` | `number_theory/factorize.hpp` | 0.64 | 正本のみ。 |
| `Array/CumulativeSum.hpp` | `array/cumulative_sum.hpp` | 0.38 | 書き方が異なる。正本（2 次元を含む）のみ。 |
| `AlgebraicStructure/Monoid.hpp` | `algebraic_structure/monoid.hpp` | 0.41 | 正本が機能的に上位。 |
| `AlgebraicStructure/Group.hpp` | `algebraic_structure/group.hpp` | 0.40 | 正本が上位。 |
| `Graph/UnionFind.hpp` | `union_find/union_find.hpp` | 0.19 | 別実装。正本（経路圧縮、サイズ）のみ。 |
| `Graph/GraphM.hpp` | `graph/graph_matrix.hpp` | — | 名前だけ違う同じ部品。正本のみ。 |
| `Graph/GraphL.hpp` | `graph/graph_list.hpp` | — | 同上。 |
| `Geometry/Point.hpp` | `geometry/vector.hpp` | — | 判断（2026-10-09）: 統合しない。`Point` は整数の外積で比較する偏角順序（象限を保持）で、`Vec2` は `EPS` つきの浮動小数向けと用途が異なる。`library3` の `Point`/`Point3` は固有の部品として別に検証する。 |
| `AlgebraicStructure/Mapping.hpp` | `algebraic_structure/monoid_lazy.hpp` | — | 判断（2026-10-09）: 統合しない。`Mapping.hpp` はアフィン写像 `Affine`（合成・逆）で、`monoid_lazy.hpp` は区間加算・最大最小などの具体的な遅延作用であり、重複する宣言はない。`Affine` は固有の部品として別に検証する。 |

命名規則は `library/` を優先する（スネークケースのファイル名、`cp::` 名前空間の公開部品）。`library3` のコードは検証済みの部品（`library/*.hpp`）に取り込まれないので、検証の台帳（`docs/verification_inventory.json`）の対象も `library/` 側の宣言に一本化する。

`Point` と `Mapping` は 2026-10-09 に上記のとおり判断した（統合なし、固有部品として検証対象）。重複の判断は全件完了。
