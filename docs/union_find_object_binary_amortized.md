# 元ObjectRefのsameとuniteの償却評価

`Proofs/UfObjectSameAmortized.lean` と `Proofs/UfObjectUniteAmortized.lean` は元Stateと数学的 `UfHistoricalRank.History` から、候補C++の生成モデルの2回の経路圧縮を扱う。元の返却型を保ち、sameのboolをi32返却へ変更しない。

## 実仕事量と意味の対応

既存 `UfMethodAmortized.same_body_paths` / `unite_body_paths` は、1回目の圧縮前と2回目の圧縮前に対応する別のTraceを返す。これを実prepare/compact/body/finish/restoreへ接続し、経路長 `k1,k2` について次を証明する。

```
same:  work(out) ≤ work(source) + 91*k1 + 91*k2 + 192
unite: work(out) ≤ work(source) + 91*k1 + 91*k2 + 354
```

`actual_*_amortized` は `Compressed.unique` により、これらの数学的中間vectorと実Stepの中間vectorを同定する。uniteでは両rootも同定し、実Stepの最終vectorを元の `uniteVec` へ接続する。成功fuelと実結果Contextを変更して評価を流用しない。

## potentialと正常終了

両Traceへ `forest_budget` を適用し、uniteには併合による `unite_potential` も合わせる。`FP=forestPotential`、`n=要素数` とすると次を得る。

```
work(out) + 91*FP(after,nextRho)
  ≤ work(source) + 91*FP(before,rho) + C*(alpha(n)+1)
C = 556 (same), 718 (unite)
```

sameでは数学的rank `rho` を保つ。uniteでは併合後の数学的Historyを満たす `nextRho` を構成し、停止用rankと混同しない。元Stepの返却意味、接続性、成分数、次Stateを維持する。`*_amortized_step` は元Stateから正常終了を構成し、成功を前提にしない。`*_amortized_resources` は同じ実結果に既存scalar/heap/全体peak上界を付け、HeadersLive条件も保持する。

`tests/test_uf_object_binary_amortized.py` は停止用rank+1000の同じState、sameの接続/非接続、2成分からのuniteで成分数2→1、同一成分内でのuniteで1を保持する場合を検査する。元の数学的unite履歴からHistoryを構成し、償却・意味・領域を同時確認する。

[全5methodの混在列](union_find_object_amortized.md)へ合成する。元caller/constructorからの初期State/HeadersLive、寿命操作混在、元caller AST/評価順/副作用、公開UF相違と他旧ライブラリは未完了である。
