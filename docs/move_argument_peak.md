# ObjectRef引数評価・準備のスカラー上界

`Proofs/CppMoveArgumentPeak.lean` は、共通Contextのpure値引数とvector/scalar参照引数について、実評価と準備のscalar peakを元callerの量で評価する。Tyや引数数をUFへ固定しない。

`eval_peak` はCppNestedEval.Goodから、pure式の実evalExpression結果のscalar peakがmax(元scalar peak,元scalarLive+式nodes)以下であることを導く。参照捕捉はchargeの実scalar peakを使う。`resolve_arguments_peak` は左から順の実resolveとStableのscalarLive保持に沿い、引数のargumentsWorkの和で上界を合成する。

`prepare_live_raw` は実prepareSavedのmemory/bindingsとarguments_footprintから次を導く。

```
scalarLive(out) ≤ (caller.memory長 + caller.slots長 + 2*引数数 - caller.baseMemory) + 2*引数数
```

自然数の切捨て減算をそのまま扱い、baseline≤元caller memory長を追加しない。元Stateが許す、準備prefix内にある基準量の範囲を保つ。

`prepare_peak` は実prepareArguments成功から、値評価のscalar上界とprepareSaved_peak/raw footprintを合成する。

```
max (max source.scalarPeak (source.scalarLive + argumentsWork))
    ((source.memory長 + source.slots長 + 2*parameter数 - source.baseMemory) + 2*parameter数)
```

全体peakをscalar予算へ含めない。成功済み実行に対する効果定理であり、停止は既存のReady/resolve/prepare構成と正常callから導く。

`tests/test_cpp_move_argument_peak.py` は元move後Contextでfield読取り・算術・literalの実resolve/prepareを構成し、scalar peak≤22を証明する。[UF列全体の一定scalar上界](union_find_object_uniform_scalar_peak.md)がこの一般定理を使う。
