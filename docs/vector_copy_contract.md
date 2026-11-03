# vectorコピーとUnionFindの暗黙特殊メンバー

## 契約の範囲

`Proofs/CppVectorCopy.lean` は、固定幅scalar要素のvectorコピー構築をモデル化する。割り当て成功、対象GCC 13.3/libstdc++、C++17/LP64を前提とする。新bufferは元と同じ要素列・limitを持ち、capacity=要素数、epoch=0、別ownerとなる。capacityの等式は移植可能なC++一般の保証ではなく、固定した[GCC 13.3のvector実装](https://raw.githubusercontent.com/gcc-mirror/gcc/releases/gcc-13.3.0/libstdc%2B%2B-v3/include/bits/stl_vector.h)のコピー構築プロファイルである。元bufferは変更しない。

結果の動作は定義で表し、新しい公理は置かない。work=n+1、追加peak=n+2は既存fillと同じモデル単位で、実測値でもコンパイラ命令数でもない。元bufferの常駐領域を追加peakに重ねて数えない。STL契約とC++からの意味対応は`trust_policy.md`の信頼境界に従う。

## 新しいownerと参照

`copyConstruct`単独は元ownerとの差だけを検査する。`copyStore`はストアのobjects長を新ownerとして割り当て、全既存ownerと破棄済みIDから分離する。`copy_store_runs/valid/new/old/reference/cost`は、有効ストア内の任意の元bufferからの実成功、新bufferの有効性、既存lookupと参照の保存、work・常駐領域・peakの正確な増分を証明する。コピー先への参照は新owner/epoch=0で作る。元参照をコピー先に流用しない。

flatストアに加え、以下のnested forest/Frameへの一般接続を追加した。クラスのscalarフィールド、暗黙C++ ASTを共通生成器へ接続した証明はまだない。このモデルだけをUFコピー構築全体の検証済み扱いにしない。

## 暗黙copy/moveで維持する意味

C++17では、暗黙に定義されたcopy/move構築と代入は、メンバーを宣言順に処理する。UFの場合は_ps、_num_groups、_nの順となり、scalarのmoveは元scalar値を変更しない。根拠は[C++17 class.copy](https://timsong-cpp.github.io/cppwp/n4659/class.copy)。

move後の標準ライブラリ型は、別途保証がなければ有効だが状態未規定である。[C++17 lib.types.movedfrom](https://timsong-cpp.github.io/cppwp/n4659/lib.types.movedfrom)に従い、移動元vectorを一般に空と固定しない。UFの_nや_num_groupsも0へ変更しない。_psの長さと_nの一致はmove元で保証できず、通常メソッドのクラス不変条件をそのまま適用できない。有限照合ではgetter/破棄/再代入を扱い、indexedメソッドは有効なreceiverへ復元してから呼ぶ。

copy代入はrange assignとは別操作である。固定libstdc++で容量が足りる場合、保存した先頭要素参照を保って代入できる。このため、常にepochを更新し自己range代入を拒否する既存assignRangeでcopy代入を代用しない。自己copy、自己move、容量再利用、moveによる要素参照の移動先への帰属も残る一般証明の対象である。

## 回帰検査と残る義務

`tests/test_cpp_vector_copy.py`は12種類の元buffer、整数境界、過剰容量、同owner/不正値の拒否、コピー後の読書きを検査する。破棄済みスロットと別bufferを含むストアへのコピーでは、一般定理適用、全旧参照保存、新owner、コピー先だけの書換え、非零baselineと過去peakを確認する。

`tests/imports/union_find_special_members.cpp`をGCC 13.3/UBSanでコンパイルし、元クラスと候補のcopy/move構築・代入、自己代入、容量再利用、元scalar保持、要素参照保持、move後の復元をn=0/1/2/4/17で照合する。private観測はテスト翻訳単位の-fno-access-controlに限定する。移動元長さ不一致の観測は固定実装の有限結果であり、標準一般の事後条件にしない。

固定ClangのASTでも候補の3フィールドと、実際に生成・使用された暗黙特殊メンバー4件のdefault定義本体を確認する。これは構造の証拠であり、共通変換器の受理・意味保存証明ではない。FrameとUF状態不変条件への接続は以下の追記を参照する。共通変換器の暗黙copy/move対応とクラス全体の意味保存は未完了で、公開版の置き換え条件は満たしていない。


## nested forestとFrameへの接続（2026-10-18）

`CppNestedCopy.copyRoot`は、有効な任意forestのscalar vectorを独立した新rootとしてコピーする。元はrootでもchildでもよく、既存forest/storageを延長する。新bufferのcapacityは要素数、epochは0で、元limitを保存する。旧buffer、親のchildren、scopeは変更しない。`copy_runs/copied_root_valid`は、元の型付きlookupとwellFormedから実成功・新状態のwellFormedを導く。

`clone_cost`はwork増分n+1、常駐領域増分n+1、peak=max旧peak(旧live+n+2-baseline)を証明する。nested `State.liveSpace`を使い、親容量に既に含まれる子headerを重ねて数えない。旧nodeSpaceの保存と新rootのn+1から、forest全体の正確な常駐領域を計算する。これはモデル単位で実測bytesではない。

`CppFrameCopy.copyVector`は元slotをresolveして、コピー先のrootWritableとbindingをそれぞれ1件追加する。元がreadonlyでもコピー先をwritableにでき、コピー先のpermissionは独立して指定する。`copy_vector_runs/extends/success`は対応型のresolve成功と通常の長さ条件から終了・Extendsを導き、任意実成功についてもExtendsを証明する。`copy_vector_keeps_read`はコピー前に成功した任意参照の同じ値を保存する。元で拒否された架空ownerへの参照すべてまで同一化する定理ではない。

`copied_resolve/copied_element_ref`は新bindingのresolveと新owner/epoch=0の要素参照取得を証明する。`copied_write_old`は、その新参照への実書込み後に全旧ownerのbufferが変わらないことを示す。単に同じ値を持つbufferを作るだけでなく、旧参照のgrantと新bindingを含むFrameへ接続した。

`tests/test_cpp_nested_copy.py`は、別root・tombstone・過剰容量のある混合forestからreadonly childとreadonly rootをコピーし、コピー先の両permission、新owner・新binding、旧参照保存、書込み分離を確認する。親だけ/コピーだけのscope退役では、それぞれ独立した寿命を検査する。空vector、過去peak、非零baseline、型不一致・不正slot・flags長不一致も扱う。native C++のコピーでも親reserve後の元要素参照と、親clear後のコピーの寿命を照合する。

scalarフィールドの順序付きコピーとUFのStrong/操作列への接続は以下に追加した。暗黙特殊メンバーのASTからの生成・意味保存は未完了である。nested vectorそのものの再帰deep copyやmove/代入の証明にも、このscalar vectorコピーを無条件で流用しない。


## UF scalarフィールドとの接続（2026-10-18）

UfCopyFields/UfCopyReceiverは、新vector・新scalar2セルの独立コピーと両receiverのStrong、コピー先の任意有限有効操作列の終了/workを証明した。コピー先の任意有効列の後も元receiverと全旧成功参照を保つ接続をUfCopyPreserveに追加した。暗黙C++ ASTからのモデル生成・意味対応は未完了。詳細は[union_find_copy.md](union_find_copy.md)。

## コピー代入の要素寿命基盤（2026-10-20）

`CppVectorCopyAssign`で容量内の先頭参照保持と、縮小で破棄した末尾参照の再拡張後の無効化を両立する寿命世代を追加した。flat storeの実成功・有効性・元/他参照保存・work/space/peakを接続し、成功した任意代入列で無効参照が復活しないことを証明する。既存Frameへの参照寿命と暗黙class operator=の生成/意味対応は未完了であり、class copy/move代入完了とは扱わない。詳細は[vector_copy_assignment.md](vector_copy_assignment.md)。
