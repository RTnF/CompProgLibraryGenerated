# 元ObjectRefのrootとsizeの償却評価

`Proofs/UfObjectRootAmortized.lean` と `Proofs/UfObjectSizeAmortized.lean` は生成されたUF候補の実呼出しへ親経路長の仕事量と数学的potentialを接続する。元ObjectRef、currentBuffer、正常State、添字条件を使う。C++候補と公開版の相違解消は引き続き未完了である。

## 実経路長による上界

`root_trace_work` / `size_trace_work` は停止用の任意rankの代わりに `depth(state.math)` と `depth_forest` を元本体のPRWへ適用する。[実compact仕事量](compact_work.md)、実引数準備、finishとrestoreの対応を合わせ、Traceの親経路長を `k` として次を証明する。

```
root: work(out) ≤ work(source) + 91*k + 90
size: work(out) ≤ work(source) + 91*k + 110
```

`depth_of_trace` で数学的depthと実経路長を同定する。元Stateの停止用rankを粗くしてもこの上界は増えない。各定理は供給された成功fuelの実結果へ適用し、別のContextへ証明を流用しない。

## potentialと正常終了の同時保証

数学的 `UfHistoricalRank.History parents rho` を前提とし、`Trace.forest_budget` と圧縮後Historyを使う。`FP` は `forestPotential`、`n` は要素数である。

```
work(out) + 91*FP(after,rho)
  ≤ work(source) + 91*FP(before,rho) + C*(alpha(n)+1)
C = 272 (root), 292 (size)
```

`actual_root_amortized` / `actual_size_amortized` は実成功fuelのStep、返却意味、次Stateと数学的Historyを保持する。`root_amortized_step` / `size_amortized_step` は元Stateから正常終了するfuelを構成し、成功を入力前提にしない。`*_amortized_resources` は同じ実結果へ既存scalar/heap/全体peak上界を付ける。heap側のHeadersLive条件も保持する。potentialは証明情報でありC++の実行時メモリには数えない。

## 検査と残件

`tests/test_uf_object_query_amortized.py` は初期4要素と3回のunite履歴から `parents=[-4,0,0,2]` の数学的Historyを構成する。停止用rankを1000増やした同じStateに対し、添字3の親経路 `[3,2]` によるrootの仕事量増分≤272、sizeの増分≤292、正常終了/元Stepの意味/数学的History、償却不等式、全領域上界を検査する。

[same/unite](union_find_object_binary_amortized.md)と[全5method混在列のα償却評価](union_find_object_amortized.md)を追加した。元caller/constructorからの初期State/HeadersLive、寿命操作との混在、元callerの評価順/副作用、公開UF相違と他旧ライブラリは未完了である。この候補モデルの評価を全experiments完了とは扱わない。
