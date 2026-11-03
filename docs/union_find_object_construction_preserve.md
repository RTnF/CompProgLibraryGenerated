# 別のUFを構築した後の既存状態の保持

`Proofs/UfObjectConstructionPreserve.lean` は、[元constructorからのContext構成](union_find_object_constructed_state.md)が既存callerのslot・field・viewと正常UFを保つことを証明する。

## 実配置と参照

`inverse_location` / `map_project_slots` はimmutable grant分のoffsetを外して元slotsを復元する。実Layoutから全slotsが「元slots、新vector slot、新scalar slots」の連結となることを導き、元slotとscalar bindingのlookupを保つ。

`old_memory` / `old_field` は元UF constructorのInitializedから、元memoryとtyped Fieldのslot/index/address/writable/valueを保持する。これはUF constructorが元memoryを保つpostを使う。任意のconstructorのcaller書込みを消す定理ではなく、一般constructorのprefixは[実calleeの値](constructor_layout.md)を使う。

`old_resolve` / `old_receiver` は既存viewの解決とreceiverのfield/header/viewを保持する。`current_payload` はcurrentBufferの内容/capacity/limit/epochを保持し、`old_readable` は元のreadableを保つ。

空headerのcurrentBuffer ownerはallocation表長に依存する。新allocationの追加後はownerを更新し、元の番号を固定しない。内容が空の元UFを、新しく構築したUFのallocationと取り違えないためにも必要となる。

## 正常Stateの保持と両constructor

`old_state` は既存ObjectRefの正常Stateを構築後のContextへ移し、親配列・rank・成分数・sizeを保つ。所有・型・currentBuffer・readable・基準量・scopeを再構成する。

`construct_sized_pair` / `construct_default_pair` は既存正常UF、元constructorのHeapModels/基準量/型付き引数条件とHeadersLiveから、実constructor正常終了と、同じ構築後Contextにおける旧UF・新UFの正常Stateを同時に構成する。wellFormedと長さは元Stateのallocation妥当性とmaterializeから導く。新UFはreplicate n(-1)、既存UFの内容は変えない。

`tests/test_uf_object_construction_preserve.py` は既存move後heapのUF（parents=[-4,0,0,2]、成分数1、size4）と新UFの共存を任意n<2^31で確認する。空headerを持つ既存UFでは、内容[]・成分数0・size0を保ちながらownerが2→3となることも検査する。両fixtureでsized/defaultの一般定理を適用する。

構築後の異なるUFへのgetter交互callは[全buffer保持](union_find_object_getter_frame.md)で接続する。更新methodの非干渉、元caller全体のNState再番号付けを含む意味対応、寿命操作の混在、const view/元caller ASTの評価順と副作用、公開UF相違と他旧ライブラリは未完了である。
