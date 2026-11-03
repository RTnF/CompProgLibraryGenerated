# 元ObjectRefの全5method列の償却評価

`Proofs/UfObjectAmortized.lean` は[root/size](union_find_object_query_amortized.md)、[same/unite](union_find_object_binary_amortized.md)、getterの仕事量を、実ObjectRef呼出しの任意の有限列へ合成する。元の正常State、数学的 `UfHistoricalRank.History`、各添字の範囲条件を保持する。

## 各操作と任意長列

`actual_step_amortized` は元の生成プログラムの実成功fuelへ評価を接続する。root/size/sameは同じ数学的rankを保持し、uniteは新たな数学的rankを構成する。getterは元Stepのvector不変条件と実仕事量≤10を使う。全操作の係数を718へ揃える際は自然数の単調性を使い、potential定義を巨大な式へ展開しない。

`step_amortized` は元Stateから正常終了するfuelを構成する。`execute_amortized` は操作列に帰納し、各実結果のStateと数学的Historyを次呼出しへ渡す。成分数が変わっても要素数 `n` は保たれ、各段のpotential項を相殺できる。

操作数を `m`、`FP=forestPotential` とすると、次を保証する。

```
work(out) + 91*FP(after,nextRho)
  ≤ work(source) + 91*FP(before,rho) + 718*m*(alpha(n)+1)
```

初期potentialは省略しない。これはモデルの抽象仕事量であり、実時間やC++バイト数の実測ではない。数学的rank/potential/履歴は証明情報であり、実行時メモリへ加算しない。

同じ構成で正常終了するscript、全返却値、次State、要素数/size保持と全Stepの意味を持つHistoryも返す。`actual_amortized` は異なるfuelでの成功結果一意性により、供給された任意の実成功scriptへ同じ保証を転送する。成功を仮定することで停止証明を代替しない。

## 領域との同時保証と検査

`execute_resources` は同じ最終結果へ既存scalar/heap/全体peak上界を付ける。元HeadersLive条件と、操作数に依存しない領域予算を維持する。

`tests/test_uf_object_amortized.py` は停止用rankを1000増やした同じStateから任意の有限操作列を実行し、αpotentialと意味・全領域を同時に確認する。空列、2成分からgroups/unite/size/same/root/groupsを混在させた列、各fuelを17増やした供給実scriptへの転送も検査する。

初期State/HeadersLiveを元caller/constructorから作る証明、copy/move/return/destructor混在、元callerの評価順/副作用、公開UFの元機能との相違解消は未完了である。正常State上の候補メソッド列の証明を、元C++全寿命や全experiments検証完了とは扱わない。

[singleton初期Stateの評価](union_find_object_initial_amortized.md)では初期potential=0を証明し、仕事量≤元仕事量+718*操作数*(alpha(n)+1)を得る。元constructorから正常Stateを作る接続は別途残る。
