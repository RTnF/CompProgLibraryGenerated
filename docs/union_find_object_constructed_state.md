# 元constructorから正常UF状態とメソッド列へ

`Proofs/UfObjectConstructionContext.lean` と `Proofs/UfObjectConstructedState.lean` は[元constructorの実heap export](union_find_object_construction_export.md)と[実field/slot配置](constructor_layout.md)から、メソッド列の証明で使う正常Stateを構成する。

## Contextと正常State

`exported` は実after.scalars/scope/peakを保ち、新owned heapと新viewを登録する。NStateで先頭に並ぶimmutable grant分のvector location offsetを外す。scalar slotは不変で、`field_of_cell` は実constructorのscalarCellからaddress/index/value/writableとprimitive layout factsを取り出す。

`located_vector` / `resolved_vector` / `receiver` は元ObjectRefに対応するnew view/headerとcounter/sizeを構成する。`initialized_state` は正常Stateに必要な型・所有・currentBuffer・readable・数学的不変条件・size・counterの分離・基準量・scope条件を全て証明し、data.items=replicate n(-1)とHeadersLiveも返す。[header/contextのscope対応](move_frame_scopes.md)により、既存heapに空headerがある場合も扱う。

元NStateと新Contextのowner ID全体が同じとはしない。新allocationは表の末尾へ登録し、実bufferの内容/capacity/limit/epochを保つ。既存grant/readの保持は元constructorのFrame Extendsと登録heapのread保持をそれぞれ使う。

## 正常終了・意味・全資源の合成

`construct_sized_resources` / `construct_default_resources` は、任意の許容callerから実constructorの正常終了、初期State、実method script、返却値列、最終State、全History、数学的History、size保持を同時に構成する。元constructorのwellFormed/HeapModels/scope/基準量/長さ、元heapの所有・生存・型条件と、各操作の添字条件を保持する。

操作数をm、元サイズをnとすると、constructorを含む仕事量は次である。

```
sized:   work(out) ≤ work(caller) + argument.nodes + n + 30 + 718*m*(alpha(n)+1)
default: work(out) ≤ work(caller) + 12 + 718*m*(alpha(0)+1)
```

同じ実結果へ既存scalar/heap/全体peak上界を付ける。予算は構築後の実Contextを基準にし、constructorの実peakを含めて引き継ぐ。成功callを仮定して停止の代替にせず、元constructorと各methodの正常終了を構成する。

`tests/test_uf_object_constructed_state.py` は空callerと任意n<2^31、default構築後の任意回getter、任意有限method列について実constructor費用も含めて検査する。既存move後のheapから構築する場合も正常Stateと全領域を構成し、有効grant0の値2、無効grant1のnoneを保持する。既存scalarを持つcallerのconstructor配置も併せて検査する。

## 残件

元caller全体のNState再番号付けを含む意味対応、copy/move/return/destructorが混在する寿命列、元caller AST/評価順/副作用、公開UF相違の解消、他旧ライブラリは未完了である。これらの候補モデルの構築・操作列の証明を、全C++ callerや全experiments検証完了とは扱わない。

[構築前からのcaller状態の保持](union_find_object_construction_preserve.md)により、同じContextで旧UFと新UFの正常Stateを同時に構成する。交互callとcaller全体の再番号付けの意味対応は残る。
