# 元ObjectRefの全UFメソッドのスカラー上界

`Proofs/UfObjectMethodScalarPeak.lean` は[本体のscalar/全体peak分離](compact_scalar_peak.md)を全5メソッドへ接続する。共通の元ObjectRef、宣言順field、生成NProgram、実prepare/compact、本体、finish、restoreを使う。

## 本体の上界

`actual_prefix_peak` は元PRW実行のlocals/need上界から、次のscalar予算を導く。

```
max initial.scalars.peak (prefix長 + allowance - initial.scalars.baseMemory)
```

same/sizeのallowanceは80、uniteは100、getterは6である。rootの80は別のroot定理を利用する。uniteは元の実counter cellとValid、sizeは元Validから得るWeightsも使う。getter本体の補題には不要なsize=vector長やForestを追加しない。

## 共通の実呼び出し

`expressions_ready` は元の添字条件とStateの長さ上限から、外部index literalの実denote/type条件を構成する。`call_peak` は全5methodの同型parameter profileを照合し、共通prepareを一度構成する。各methodの正確なlocals/QSへ接続して本体上界を得た後、実返却型（sameはbool、他はi32）に応じたfinishを扱う。

全methodをまとめるcall上界ではallowanceを100に統一する。

```
max (max source.scalars.peak
         (max prepared.scalars.peak (prefix長 + 100 - source.scalars.baseMemory)))
    (source.scalars.memory.length - source.scalars.baseMemory + source.scalars.bindings.length)
```

実callから得たpreparedと、元Stateから構成したpreparedを同定する。実本体のfuelや返却結果を別のものへ置き換えない。元の正常終了/意味/状態保持/work/heapの証明はそのまま利用できる。

## 検査と残件

`tests/test_uf_object_method_scalar_peak.py` は全5methodについて、正常callとEffectを構成し、過去の全体peak=1,000,000を保ちつつ結果scalar peak≤111を導く。これはテストのprefix長11と共通allowance100からの上界である。2成分からのuniteでも、実結果のEffectとscalar上界を同時に検査する。

[引数評価・準備を含む列全体の一定scalar上界](union_find_object_uniform_scalar_peak.md)へ接続した。列全体の全peak、rank/償却、元caller/constructorからの初期State、寿命操作との混在、公開UF相違と他旧ライブラリは残る。通常Stateを使うこのcall合成は、moved-from弱状態のgetter経路の代替ではない。
