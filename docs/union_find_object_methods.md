# 元ObjectRefからのsame/size/unite正常call

`Proofs/UfObjectMethods.lean` は、[元ObjectRefの共通prepare](union_find_object_call.md)を使い、same/size/uniteの正常終了を一般に構成する。これで元candidateの全5methodについて、ObjectRefの正常配置とheap・式・UF条件から実resolve/prepare/compact/QS/FWを導き、既存のbody/call証明へ接続できる。元C++のAPI・型・入力範囲は変更しない。

## 元状態からの正常終了と意味

各定理は、ObjectRefのReceiver、現在のvector内容、size field=vector長、型が合うpure添字式の意味、元heapのreadable/所有/型妥当性・limit、baselineとscope条件から呼び出しを構成する。成功済み実引数評価・完成済み準備/QS/FW・本体成功を入力仮定にしない。

| 定理 | UFの条件 | 保持する意味上の結果 |
| --- | --- | --- |
| `same_call` | Forest、型内の長さ、両添字が範囲内 | 2回の圧縮、更新Forest、返却boolと元Connectedの同値 |
| `size_call` | Forest、Weights、型内の長さ、範囲内添字 | root重みの負数を返却、圧縮、Forest/Weights保持、元Valid時の成分cardinalityと更新Valid |
| `unite_call` | 元counter値をgroupsとするValid、両添字が範囲内 | 2回の圧縮、uniteVec/uniteX、新rankのValid、countAfter/updatedMemory、元Connectedとの同値 |

uniteのgroupsはReceiverの実counter.valueへ結び付ける。別の成分なら元counter addressだけをgroups−1へ更新し、同じ成分なら元scalar memoryを保つ。callerのsizeや他のscalarを0へ正規化しない。

## workと追加領域

既存call定理のpost全項目を残す。sameのworkはprepared work+91rank(a)+91rank(b)+181、sizeは+91rank(a)+101、uniteは+91rank(a)+91rank(b)+343。scalar/heap/合成peakは実initial stateとbaselineを使う既存上界で、caller memory保持/正確なcounter更新と、更新buffer payloadも維持する。

実prepared/initial stateとFWも返すため、任意に大きい予算を選ぶだけの存在条件にはしない。式評価・準備の費用は実prepared stateに記録される。元callerからの総費用、償却計算量と任意混在寿命列への一般接続は残る。

[呼び出し後の配置・heap条件保持](move_call_layout.md)を追加し、同じObjectRefを結果stateのReceiverとして再構成する経路とunite→getterの正常終了へ接続した。

## 検査と残件

`tests/test_uf_object_methods.py` は元move後のObjectRefへ全3一般定理を適用し、同一TUから再生成したarguments_of_fields/call_of_argumentsでsource wrapperの正常終了へ転送する。sizeは元ValidからのWeights、sameは算術式を含む外部引数も扱う。

2成分の正常状態は、元initial_validから2回のunite_vecでValidを構成する。3と1が別成分であることをReachとrootの一意性から証明し、一般unite定理のConnected/updatedMemory postから、counterが2→1、他scalarは不変となることを導く。完成済み本体実行や固定fuelの計算結果をこの証明の入力にしない。元C++は変更せず、既存native照合を維持する。

元caller ASTからのObjectRef/正常field配置・評価順/副作用、constructor/copy/move/return/destructorからの配置保持、償却証明・任意混在寿命列、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは未完了である。
