# 元ObjectRefのUF列全体に対する一定スカラー上界

`Proofs/UfObjectUniformScalarPeak.lean` は[全5methodの実scalar上界](union_find_object_scalar_peak.md)と[引数評価・準備のscalar量](move_argument_peak.md)を合成し、操作列の長さに依存しない上界を導く。

## 元callerの量による予算

予算は次のとおりである。

```
max source.scalars.peak
    (max (source.scalarLive + 5) (source.receiverPrefix長 + 100 - source.baseMemory))
```

元receiverの3引数と外部添字0〜2個から、引数費用とparameter数は高々5となる。Stateの既存条件baseMemory≤receiverPrefix長を使い、元memory長まで基準量を狭めない。実prepared scalar peakをこの元caller予算へ収め、call_peakの返却/restore後のscalar上界も同じ予算で評価する。

## 任意長列への合成

実callのLayoutはmemory長、bindings、slots、baseMemoryを保持する。このため予算のうちpeak以外の項が変わらず、中間scalar peakが元予算以下なら中間予算も元予算以下である。

`history_peak` はこの性質を全Stepへ帰納適用する。`actual_peak` は供給された実成功scriptにも同じ上界を与える。過去の全体peakや操作数をscalar予算へ加算しない。

`execute_resources` は元State、各添字条件、heapのHeadersLiveから、正常終了するscript、結果列、次State、全History/Charges、仕事量上界、一定scalar/heap上界、heap生存量/基準量/Header保持を同時構成する。完成済み中間Stateや各callの成功を入力にしない。

## 検査と残件

`tests/test_uf_object_uniform_scalar_peak.py` は過去の全体peak=1,000,000を保つ元Stateから、任意の有限操作列について正常終了/返却意味/仕事量とscalar peak≤111を構成する。元memory長4より大きいbaseMemory9（prefix長11以内）でも任意列を実行し、scalar peak≤102を確認する。さらに同じ実行について意味・仕事量・scalar/heap上界を同時に保持することを検査する。

[列全体の全体peak上界](union_find_object_total_peak.md)へ接続した。rank/償却、元caller/constructor初期State/HeadersLive、寿命操作との混在、公開UF相違と他旧ライブラリも未完了である。
