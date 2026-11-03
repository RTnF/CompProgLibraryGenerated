# 元ObjectRefの任意長UF列の全体peak

`Proofs/UfObjectTotalPeak.lean` は[実callの全体peak合成](move_call_outer.md)、[一定scalar予算](union_find_object_uniform_scalar_peak.md)、[一定heap予算](union_find_object_heap_peak.md)を合わせる。

## 各呼び出しと任意長列

予算は次である。

```
budget(source) = max source.peak (scalarBudget(source) + heapBudget(source))
```

`invoke_components` は元State、実引数のpure条件、全5methodのAllowed/返却型、元context/所有条件から一般call_outerを適用する。`invoke_bounds` は両component上界と、中間callerでも予算が増えないこと、HeadersLive保持を導く。

`history_peak` はそのまま全Stepへ帰納適用し、操作列の長さに依存しない全体上界を得る。`actual_peak` は供給された実成功scriptにも同じ上界を与える。各callで予算を足して列長倍にする扱いはしない。

`execute_resources` は元State、各添字条件、HeadersLiveから正常終了するscriptを構成し、返却数・size保持、最終State、全History/Charges、仕事量、scalar/heap/全体peak、生存量/基準量/Header対応を同時に保証する。

## 新しい測定基準での追加領域

scalar基準を元memory長、heap基準を元liveSpaceとすると、`baseline_budget` は予算をcallerのbindings/slotsと初期peakだけの式へ書き直す。さらに各初期peakを0とした実成功scriptについて、`actual_additional` は次を保証する。

```
out.peak ≤ max (source.bindings数 + 5) (source.slots数 + 101) + 1
```

この式に要素数や操作数は含まれない。単位はモデルの抽象領域であり、C++バイト数、実メモリ使用量や実測値ではない。元callerの基準量と初期peakの条件を省かない。

## 検査と残件

`tests/test_uf_object_total_peak.py` は元move後の実data/fieldsを保ち、scalar基準4・heap基準7・各初期peak0のStateを構成する。任意の有限操作列について正常終了/返却意味/仕事量とscalar≤107、heap≤1、全体≤108を同時に検査し、任意の実成功scriptへ追加領域定理も適用する。過去の全体peak=1,000,000を持つ場合も、操作数によらずその予算内に収まることを確認する。

元caller/constructorからの初期State/HeadersLive、rank/償却、copy/move/return/destructorが混在する寿命列、評価順/副作用、公開UF相違と他旧ライブラリは未完了である。現在の仕事量は各中間rankに依存する和であり、この領域証明でα償却計算量まで証明したとは扱わない。
