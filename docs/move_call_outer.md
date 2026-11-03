# compact呼び出しの全体peakと構成要素

`Proofs/CppMoveArgumentOuter.lean` と `Proofs/CppMoveCallOuter.lean` は、実引数評価・準備・本体・返却・復元を通して、全体peakをscalarとheapのpeakへ接続する。UFへ型や返却値を固定しない。

## 引数評価・準備

`Effects` は次を保持する。

- scalar peakが元より減らない。
- 元heapが保たれる。
- 結果outer peak≤max(元outer peak,結果scalar peak+元heap peak)。

pure値式にはCppNestedEval.Good、参照捕捉には実chargeを使い、実resolveを左から合成する。prepareBase、実bindSaved、任意長bindSavedAll、prepareSaved、prepareArgumentsも同じ効果を保つ。基準量を元memory長まで狭める条件は追加しない。

## 実呼び出しの合成

`call_outer` はscalarを返す生成NProgramについて、pure引数、Allowed本体、元context上界、OwnsAll、実成功callを入力に取る。実call_partsでprepare/compact/body/finish/restoreを取得し、元callerから本体初期状態のcontext上界を構成する。

CppPeakRun.run_growsが与える本体のcomponent単調性と全体peak上界、実restored_finish_countersを合成して次を示す。

```
out.peak ≤ max source.peak (out.scalars.peak + out.objects.heap.peak)
```

準備や本体で生じたpeakを落として、単に返却時の生存量を数えた式ではない。各componentのpeakが途中の最大値を覆うことを使う。過去の全体peakもmaxで保持する。

`tests/test_cpp_move_call_outer.py` は実field/算術/literalのprepareで単調性・heap保持・全体peak合成を検査する。空vectorと元size4/counter1を持つmoved-from弱getterでも、正常終了と返却1を構成して一般call上界を適用する。通常UFのStateを弱getterへ強制しない。[任意長UF列の全体peak](union_find_object_total_peak.md)がこの一般定理を利用する。
