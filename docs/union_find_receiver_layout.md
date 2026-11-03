# 元UFのreceiverからメソッド本体の証明条件を構成

`Proofs/UfReceiverLayout.lean` と `Proofs/CppMoveReceiverFrame.lean` は、元のUnion-Findの呼び出しについて、実引数評価の結果と元heapの正常条件から、実prepare/compactの成功、scalar配置の `QS`、vector状態の `FW` を構成する。[receiver配置](move_receiver_layout.md)から既存の5methodのbody/call証明へ接続する段階であり、元C++のAPI・汎用性・入力範囲は変更しない。

## scalar配置と元fields

`prepare_qs` は、借用vector・counter参照・型妥当なi32値列という実 `resolveArguments` の結果から、実 `prepareArguments` とcallee binding整理の成功を導く。元scalar baseline、元scope+1、元frame.stateとrootWritableを保持し、整理後のvector bindingが元headerを指すことも導く。完成済みprepareやcompactを入力仮定にしない。

値列を既存のbody証明が使う正確なfieldsへ変換する。

| 定理 | 値列 | 元fieldsと対象method |
| --- | --- | --- |
| `qs_two` | `[n,a]` | `UfFieldsRoot.fields`、root/size |
| `qs_three` | `[n,a,b]` | `UfFieldsSame.fields`、same/unite |
| `qs_one` | `[n]` | `UfFieldsCounter.fields`、num_groups |

`prefix_length` / `prefix_take` / `prefix_cell` は、元caller memoryが実準備用prefixの先頭に残り、元counter cellも同じaddressにあることを示す。call後のmemory復元やuniteのcounter更新に必要な前提を、完成後memoryの仮定へ置き換えない。

## source heapからのvector証明条件

`CppMoveReceiverFrame.current_entry` は、元headerの存在とreadable、所有者の一意性と全live allocationの被覆から、実 `currentBuffer` の成功・投影entry・buffer妥当性・元limitとownerを構成する。allocationを持つheaderと、空headerの両方を扱う。空headerでは既存モデルと同じ容量0の補助bufferを使い、旧allocationを復活させない。

`fw_from_entry` は、元entry、全allocationの型妥当性と型のsupport、実準備によるstate/rootWritable/binding対応、元scope条件から `VecWrite.FW` を構成する。forest/storage lookup、書込み権限、buffer owner/limit、scopeの厳密な不等式を含む。完成済みFWやbodyの成功を入力仮定にしない。calleeのresource contextには実initial stateのliveSpace/work/objects数を記録する。

`prepare_qs_fw` はこれらを元UFのi32 receiverへ合成する。元headerのlimitがこの型のsizeLimitであること、元caller内の全projected scopeがcaller.scope以下であることも要求する。buffer長のu64内性は、readableが与えるbuffer妥当性とlimitから導く。readonly viewでは `wV=false` を保ち、rootWritableの最大権限trueと混同しない。

## 検査

`tests/test_uf_receiver_layout.py` は元move後UFの全5methodについて、実resolve結果から正確な元fields/QSとFWを一般定理で構成する。rootではこれらを既存 `root_call` へ渡し、正常終了と圧縮を導く。moved-fromの空vectorでも元 `_n=4` とcount=1を保ち、`counter_call` の正常終了から1の返却を導く。`_n=vector長` をgetterの不要な前提にしない。

readonly vectorのFWと、元scalar prefix/counter cellの保持も検査する。元methodのC++実装とnative照合は既存登録テストを維持する。

[pure scalar式からの実resolve構成](move_receiver_resolve.md)を追加し、field cellと式の意味上の結果から実引数評価を導けるようにした。ObjectRef/slotの選択と任意callerへの一般接続は残る。

## 残件

実引数評価の成功はこの一般定理の入力条件であり、検査の有限例だけから任意callerの評価成功を主張しない。[同一TU receiver生成](context_method_receiver.md)のObjectRef、元caller ASTのcallee/receiver/引数評価順と副作用からの一般構成、償却証明と任意混在寿命列への接続は残る。構築・返却・destructor、割当/resize/nested/異種vector、公開UFの元sourceとの相違と他旧ライブラリも未完了である。
