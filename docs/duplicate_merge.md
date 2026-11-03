# 重複実装の統合方針と対応表

`experiments/library/`（snake_case）と `experiments/library3/`（CamelCase）の重複を、正規化した文字列（空白・大小・`_` を無視）の類似度で調べた。命名は `library/` の snake_case を優先する。統合は検証と同時に行う。検証前の原本は削除せず、統合先の候補を下表に記録する。

| 統合先（正本候補） | 重複元 | 類似度 | 判断 |
| --- | --- | --- | --- |
| `library/cpp/template/small_template.hpp` | `library3/.../SmallTemplate.hpp` | 1.00 | 同一内容。公開部品はすでにこの小テンプレートを先頭で include する。 |
| `library/cpp/template/template.cpp` | `library3/.../Template.cpp` | 0.99 | ほぼ同一。差分確認後に統合。 |
| `library/cpp/union_find/union_find.hpp` | `library/cpp/union_find/disjoint_set_union.hpp` | 1.00 | 同一内容の別名。名前は `union_find` を採用。 |
| `library/cpp/segment_tree/segment_tree.hpp` | `library3/.../SegmentTree.hpp` | 1.00 | 同一内容。 |
| `library/cpp/graph/lowlink.hpp` | `library3/.../Lowlink.hpp` | 0.97 | ほぼ同一。差分確認後に統合。 |
| `library/cpp/graph/prim.hpp` | `library3/.../Prim.hpp` | 0.95 | ほぼ同一。 |
| `library/cpp/graph/dijkstra.hpp` | `library3/.../Dijkstra.hpp` | 0.96 | ほぼ同一。 |
| `library/cpp/array/sort_util.hpp` | `library3/.../SortUtil.hpp` | 0.94 | ほぼ同一。 |
| `library/cpp/array/cumulative_sum.hpp` | `library3/.../CumulativeSum.hpp` | 0.93 | ほぼ同一。 |
| `library/cpp/graph/graph_matrix.hpp` | `library3/.../GraphM.hpp` | 0.93 | ほぼ同一。 |
| `library/cpp/modint/modint.hpp` | `library3/.../ModInt.hpp` | 0.89 | 差分あり。意味差を確認してから統合。 |
| `library/cpp/graph/graph_list.hpp` | `library3/.../GraphL.hpp` | 0.77 | 差分あり。API の違いを確認する。 |
| `library/cpp/number_theory/factorize.hpp` | `library3/.../Factorize.hpp` | 0.77 | 差分あり。 |
| `library/cpp/modint/modint.hpp` | `library/cpp/modint/dynamic_modint.hpp` | 0.74 | 別物（実行時の法）。統合しない。 |
| `library/cpp/template/marathon_template.cpp` | `library3/.../MMTemplate.cpp` | 0.94 | ほぼ同一。 |

類似度 0.6 未満の組（`edge` と `graph_*` など）は共通の補助語による偽陽性で、統合しない。台帳の `duplicate_candidates` は宣言名の一致を基準にした粗い候補であり、上表が実質的な重複である。

統合の手順は、(1) 正本候補だけを検証して公開し、(2) 重複元の差分を `diff` で確認し、意味差があれば修正候補として別途検証し、(3) 台帳の `verification_target` を正本へ向ける、とする。現時点で検証済みの部品に重複元はない。
