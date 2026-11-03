# UnionFind の全体の rank 分布

`Proofs/UfGlobalPopulation.lean` は、成分内の個数上界を全 node へ集約する。rank が `k` 以上の node の総数を `c`、node 数を `n` とすると、`GlobalPopulation` はすべての `k` について `c * 2^k ≤ 2*n` を表す。C++ の表現・API は変更しない。

まず `Valid` な forest の各有効 node が負の値を持つ根へ到達することを既存の停止証明から導く。`roots.flatMap members` が重複を持たず、`List.range n` と同じ要素からなることを示す。`components_perm` はその分割が permutation であることを証明する。成功した探索を根の存在の前提として仮定しない。

`component_sizes_sum` は各成分のサイズの合計が `n` になること、`component_counts_sum` は任意の predicate を満たす node の総数が各成分での個数の合計になることを示す。`Population` の各成分の `Budget` から `c*t ≤ 2*s` を取り出し、合計と積を分配して全体の上界へ接続する。新たな Mathlib module の import は加えず、既存の list と pairwise の補題を用いる。

`global_calls` は全5メソッドを含む任意の有効な有限操作列に適用する。`constructed_global_calls` と `default_global_calls` は両実構築子から接続し、全体の上界を入力前提に置かず実初期状態から導く。既存の実終了、`Represents`、`HistoryWithPopulation`、長さと回答数の条件を保持する。

`tests/test_union_find_global_population.py` は生成モデルと native UBSan の混在列、両構築子、一般の操作列、元の node 数を用いた上界を確認する。8-node starで root rank 3、他の rank 2という、点ごとの `History` を満たしても全体上界を満たさない反例も示す。

未完了なのは level/index と potential、実際の2段階の走査・書込み・仕事量との対応、操作列全体の償却時間である。この rank 分布上界だけを逆 Ackermann 関数による計算量の証明とは扱わない。公開版の違反、caller 資源、他の旧ライブラリに関する検証義務も残る。
