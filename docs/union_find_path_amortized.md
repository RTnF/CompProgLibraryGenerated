# UnionFind root の実仕事量と償却上界

`Proofs/UfPathAmortized.lean` は、候補 C++ の生成済み `root.callFuel` の終了・結果・圧縮後の `Represents` を存在証明し、次を示す。

```
out.work + 91*forestPotential(vec,rho)
  ≤ s.work + 91*forestPotential(ps,rho) + 324*(alpha(n)+1)
```

`n=ps.length`。前提は既存の `Represents`、履歴 rank の `History`、有効な添字であり、成功した実行や仕事量上界を前提に要求しない。仕事量は既存の `NState.work`（scalar と storage の累積操作数）であり、実測の CPU 時間ではない。

`Trace` は親を辿る決定的な列で、根を除いた訪問 node を記録する。一意性・存在から正確な `depth` を定義し、これが既存の停止用 `Forest` を満たすことを証明する。`root_work_trace` はこの depth を既存の生成 program の実行定理に渡し、prepare/finish と2-pass探索・書込みを含む仕事量を `91*nodes.length+142` で抑える。結果の `Represents` は元の rank のまま保つ。

`index_next` は最大 index の次の反復が親 rank を越えることを示す。同じ最終 level の正 rank の辺は potential を少なくとも1減らし、最終 level が下がる辺は level 差へ課金する。経路に沿って合計し、rank 0 の先頭と根の隣も含めて、経路長と更新後の経路 potential の和を更新前の和に `alpha(n)+2` を加えた値で抑える。

訪問列の重複がなく range n に含まれることと、経路外の potential 非増加を使い、全 forest にこの不等式を移す。`Trace.forest_budget` と実仕事量を組み合わせた結果が `root_amortized`。`alpha(0)=alpha(1)=0` の境界を落とさず、正の単位 `alpha(n)+1` を使う。`alpha_positive_unit` はこれを `3*(diagonalAlpha(n)+1)` 以下とする。

`tests/test_union_find_path_amortized.py` は一般定理を適用し、深さ3の実経路、圧縮後の再探索、既に根である場合の生成モデルの仕事量を検査する。候補 C++ は同じ操作と1-node境界を UBSan で実行する。C++ 実行中には ghost potential や Ackermann 関数を計算しない。

全5メソッド・任意操作列・両構築子の実仕事量への拡張は `docs/union_find_method_amortized.md` へ進んだ。caller 資源、公開版の違反、他の旧ライブラリの検証も残る。
