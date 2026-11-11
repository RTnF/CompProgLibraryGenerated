# 公開ライブラリ

`experiments/library/cpp/` に合わせて分野別に配置する。各部品の `.hpp` と `.toml` は同じディレクトリに置き、TOML の `source` は `library/` からの相対パスで指定する。部品名・C++ API・依存名はディレクトリ移動で変更しない。

| ディレクトリ | 部品 |
| --- | --- |
| `algebraic_structure/` | `group`, `monoid`, `monoid_lazy` |
| `array/` | `cumulative_sum`, `doubling`, `search_util`, `sort_util`, `vector2d_sum`, `vector_fill`, `vector_max`, `vector_min`, `vector_sum` |
| `graph/` | `bellman_ford`, `csr_build`, `dijkstra`, `find_cycle`, `floyd_warshall`, `lowlink`, `prim`, `topological_sort` |
| `interval/` | `interval`, `interval_union` |
| `modint/` | `dynamic_modint`, `mod61`, `modint` |
| `number/` | `extrema`, `ratio`, `square_matrix` |
| `number_theory/` | `bit_width_u64`, `countr_zero`, `enumerate_quotients`, `floor_sum`, `floor_sum_unsigned`, `gcd_u64`, `inv_gcd`, `is_prime`, `pow_mod`, `safe_mod` |
| `random/` | `xorshift` |
| `segment_tree/` | `fenwick_tree`, `lazy_segment_tree`, `segment_tree`, `segtree_sum` |
| `string/` | `rolling_hash`, `run_length` |
| `tree/` | `tree_ancestor`, `tree_arc_costs`, `tree_arcs`, `tree_distance`, `tree_edges`, `tree_find_root`, `tree_full_dp`, `tree_height`, `tree_lca_same_depth`, `tree_order`, `tree_path`, `tree_root` |
| `union_find/` | `union_find` |

利用例: `#include "library/segment_tree/fenwick_tree.hpp"`。リポジトリルートを include path に指定する。テンプレートを先行includeする検査は、現在も `experiments/library/cpp/template/small_template.hpp` を使う。テンプレート自身の原本検証は継続中。

部品名を指定するコマンドは従来どおり使える。

```sh
python3 tools/public.py
python3 tools/public.py --include-check enumerate_quotients --output /tmp/enumerate-quotients-included.cpp
python3 tools/check_public.py --timeout-seconds 7200
```

登録は下位ディレクトリも走査し、同じ部品名の重複・未登録ファイル・依存循環を拒否する。ヘッダ配布ZIPもディレクトリ構造を保持する。検証範囲は各TOMLの `spec`、原本移植の残件は [進捗](../docs/agent/handoff.md) と [原本台帳](../docs/verification_inventory.json) を参照する。
