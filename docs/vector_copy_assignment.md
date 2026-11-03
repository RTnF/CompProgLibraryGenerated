# scalar vector のコピー代入と要素寿命

`Proofs/CppVectorCopyAssign.lean` は、自己代入、容量を再利用する代入、再確保を伴う代入を区別した scalar vector の操作モデルと、その flat store への接続を定義する。UnionFind の暗黙コピー代入を共通生成器へ接続するための基盤であり、現時点で C++ クラスの代入全体を検証済みとは扱わない。

容量と自己代入の方針は、この環境の固定 GCC 13.3/libstdc++ の `bits/vector.tcc` にある `vector::operator=(const vector&)` を確認した。対象は固定幅 scalar と標準 allocator、確保が成功する経路。異なる allocator、ユーザー定義要素の副作用・例外はこの primitive の契約外であり、それらを必要とする元 API の義務を解消したとはしない。

`copyAssign` は両 buffer の有効性、代入先の書込み権限、代入先の最大サイズを検査する。自己代入は要素・容量・epoch・要素寿命を保つ。別 owner からの代入は元の値をコピーし、容量は `max(oldCapacity, newSize)` とする。容量内であれば生き残る先頭要素の参照を保ち、再確保では epoch を増やして以前の参照を無効化する。

## 縮小後の参照を再有効化しないための記録

従来の `ElementRef` の owner/epoch/index だけでは、容量を保ったまま末尾要素を破棄し、後で同じ位置へ要素を構築する場合を区別できない。縮小直後は添字が範囲外なので読めても、その後の再拡張で同じ古い参照が再び読めてしまう。コピー代入を既存の範囲代入で代用すると先頭参照まで無効化するため、必要な意味を保てない。

新しい `Tracked` と `Reference` は、buffer の epoch に加えて要素ごとの寿命世代を記録する。容量を再利用した縮小では、破棄される末尾の世代だけを増やす。生存する要素の世代は変えない。再確保では buffer の epoch を増やす。これらは証明用の情報であり、C++ が補助配列を確保するという主張ではない。

`prefix_read` は、生き残る位置への既存の参照で更新後の値を読めることを示す。`erased_retired` と `reallocated_retired` は、要素破棄／再確保による無効化を示す。`copy_preserves_retired` と `Assignments.no_resurrection` は、成功した任意のコピー代入列の後も、以前に無効化された参照が読めないことを証明する。新しい参照は現在の世代を持ち、再構築した要素を読める。

## store と資源

`LifetimeStore` は既存の flat `Store` に寿命情報を付ける。`storeAssign` は対象・元を lookup し、copyAssign の結果を既存の commit に渡す。有効な store と lookup、サイズ条件から `store_runs` が実成功を導き、`store_valid` が更新後の有効性を保つ。成功した操作を無条件に仮定して終了証明を省略しない。

`store_target` は更新対象、`store_other_reference` は対象外の buffer・参照の保存を示す。異なる owner の元も対象外なので保持される。自己代入では同じ store slot を読むため、同じ owner に異なる値を持つ架空の source を置かない。`store_retired_unreadable` は対象への無効な参照が store 経由でも読めないことを示す。

固定幅要素について、仕事量のモデル予算は自己代入1、それ以外は oldSize+newSize+1。古い要素の退役と新しい要素のコピーを数えた線形上界であり、実測 CPU 時間ではない。単独 buffer の peak は再利用で oldCapacity+2、再確保で oldCapacity+newSize+2。`store_work/space/peak` は既存 liveSpace・baseline・過去 peak を保った正確な合成式を与える。寿命情報はこれらの C++ 資源量に加算しない。

## 検査と残り

`tests/test_cpp_vector_copy_assign.py` は32通りのサイズ／容量と一般定理適用で、内容・容量・epoch・仕事量・peak、自己代入、先頭参照保持、破棄参照の縮小／再拡張後の無効化を検査する。tombstone と別 owner を含む store で、元と他の参照の保存、非零 baseline と過去 peak、readonly／不正 owner／最大サイズ／不正要素の拒否も確認する。

固定 GCC の `int` と `long long` では147通りずつのサイズ／余剰容量、自己代入、縮小／再拡張を ASan/UBSan で実行する。縮小で無効になった C++ ポインタは再使用せず、先頭の生存するポインタと新たに取得した要素だけを読む。ptrace 下で実行できない LeakSanitizer は既存テストと同様に無効化し、ASan/UBSan は有効にする。

既存 `Frame`／`NState` の参照、暗黙 `operator=` の AST 監査・生成・意味対応、クラスの宣言順 scalar 代入、move／move 代入への接続は未完了。現在の Frame に寿命情報を黙って捨てた形でこの primitive を接続しない。旧モデルの定義や公開定理は変更していない。公開候補の昇格と、全旧ライブラリの検証は引き続き未完了である。

Frameの型・権限・nested資源への接続は [frame_copy_assignment.md](frame_copy_assignment.md) へ進んだ。NStateと実生成class operator=、任意混在操作列への寿命伝播は未完了である。
