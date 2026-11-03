# compact呼び出しのスカラー領域と全体peakの分離

`Proofs/CppCompactScalarPeak.lean` は、vector書込みを含む生成本体の実行で、過去の全体peakをscalar peakの上界へ混ぜずに扱う。`Proofs/UfObjectRootScalarPeak.lean` はこの補題を元ObjectRefのroot本体と実callへ適用する。

## 一般の本体実行

`body_run` は元PRW実行、QS/FW、scalar初期peak、localsとneedの上界、scopeの条件から、実runFuelとQpostW全体を構成する。補助outerBudgetには元の全体peak、storage peak、生存量+1を含め、scalar予算は独立して与える。補助予算をheapの精密な上界とは呼ばず、heap上界は既存の別定理を用いる。

`actual_body_peak` は、構成した本体実行と供給された実成功fuelの結果一意性から、実結果のscalar上界を導く。正常終了の存在構成も残す。

`call_parts` は共通compact Context callの実成功を、実prepareArguments、compact、本体runFuel、breaking=false、finish、restoreContextへ分解する。失敗判定を除去せず、後段へ別の結果stateを渡さない。

## rootへの適用

root本体では元body_correctが保証するneed≤prefix長+80を使う。実結果scalar peakの上界は次である。

```
max initial.scalars.peak (prefix長 + 80 - initial.scalars.baseMemory)
```

`root_call_peak` は元Stateから共通prepare/QS/FWを構成し、実prepare/compactと同定する。実本体のscalar上界とrestored_finish_countersから、返却・restore後にも次の上界を導く。

```
max (max source.scalars.peak
         (max prepared.scalars.peak (prefix長 + 80 - source.scalars.baseMemory)))
    (source.scalars.memory.length - source.scalars.baseMemory + source.scalars.bindings.length)
```

元の全体peakやheap peakはこの式に含めない。元の正常終了・圧縮・Forest・work・heap・全体peakの各postは既存stepに残す。call_peakは実成功への空間の効果定理であり、成功を仮定して停止証明の代替にはしない。

## 検査と残件

`tests/test_uf_object_root_scalar_peak.py` は元move後の同じ実scalar/heap/fieldに対し、Contextの過去の全体peakだけを1,000,000とした正常rootを構成する。結果scalar peak≤91と全体peak≥1,000,000を同時に導く。receiverPrefix長は11で、vector参照の1単位も含む。元rootのEffectとscalar上界が同じ実結果に対応することも確認する。

[全5メソッドへの適用](union_find_object_scalar_peak.md)を登録している。prepared scalar peakの元caller量による評価、列全体のscalar/全peak、初期State構成と償却は残る。
