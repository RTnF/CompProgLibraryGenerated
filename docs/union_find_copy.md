# UFコピーの状態モデルと不変条件

`Proofs/UfCopyFields.lean`と`Proofs/UfCopyReceiver.lean`は、UFのvectorと2つのscalarメンバーを独立コピーする状態モデルを、通常メソッドの不変条件へ接続する。元C++と候補C++は変更しない。**暗黙copy構成子のASTからこのモデルを共通生成する対応は未完了**であり、C++クラスのcopy全体を検証済みとは扱わない。vector側のSTL契約・固定GCCプロファイルと信頼境界は[vector_copy_contract.md](vector_copy_contract.md)に従う。

## 状態の構築順と所有位置

`copyReceiver`は元vectorSlotを解決し、Frameの`copyVector`で新root・bindingを作る。その後に元の_num_groupsと_nをscalarCellから読み、`fields`で新しいscalarセル2件とbinding2件を追加する。slotsの順はvector/count/nで、元C++のメンバー宣言順に合わせる。コピー先layoutはコピー前状態の`layoutOf`である。

新scalarメンバーのwritableはtrueである。コピー元の式がconstであることから、コピー先メンバーもreadonlyとすることはしない。既存構成子のcaptureAll/restoredは元writableを保存するため、そのままconst元からのコピーへ流用しない。コピー後の元メンバーと旧aliasは元の位置・permissionを保持する。

`fields_count/n/vector`は新メンバーを正確なslotから解決し、`fields_old_scalar/vector`は全ての成功した旧scalarCell/vectorSlot解決を保存する。元セルとコピー先セルのアドレスは重ならず、コピー先vectorは新owner・epoch=0を持つ。

## 不変条件と操作列

`new_ok`は新vectorのwellFormed、binding・owner・scope・flag・baseを`VOKWF`へ接続する。旧contextはforestのprefixから保存し、新rootのcontextを現在scopeに置くので、scopeの上界を失わない。`new_represents`は新bufferと2つの新scalarセルに、元の数学的ps/count/rankの条件を結ぶ。

`old_ok/old_represents`は、Frame延長と旧scalarCell保存から、コピー直後の元receiverも同じ不変条件を満たすことを示す。`copy_strong`は、任意のStrongな元receiverからコピー操作の実成功と、同じ出力状態における元・コピー両receiverのStrongを構成する。`actual_copy_strong`は任意の実成功結果にもこの結論を適用する。

`state_cost`はコピーのwork増分n+4、vector常駐領域増分n+1、scalarセル/binding長それぞれ+2、scalar baseline保存、storage peak=max旧peak(旧live+n+2-storage baseline)を証明する。nはbufferの要素数で、UFではps.lengthに等しい。単位は既存モデルのcell/binding/headerとworkで、実測値ではない。scalar/outerのコピー全体の一様上界は、以下のUfCopyPeakで追加した。

`copy_calls`はコピー後の任意有限有効操作列の終了、コピー先のStrong、長さ・返却数を構成し、全workをコピー前work+n+4+m*(182*log2(n)+405)以下に抑える。これはO(n+m log n)で、逆アッカーマン償却境界ではない。この定理は操作列終了後の元receiverのStrong保持を含まない。新receiverの操作が全旧receiver/aliasを保つ強い一般接続は、以下のcopy_calls_bothへ追加した。

## 回帰検査と残る義務

`tests/test_union_find_copy_receiver.py`は実構成子から作った4要素receiverをコピーし、両Strongを一般定理へ接続する。新保存先、旧scalar・vector保持、独立permission、正確なwork/常駐領域、コピーの再コピー、空のdefault receiver、slot不正の拒否、任意Strong・任意有効列への定理適用を検査する。

コピー先で全5メソッドを含む混在12操作を実行し、期待値[4,0,2,0,2,0,0,1,4,1,0,1]、コピー先の更新と元buffer/count/nの保持を確認する。同じ操作列をconstな元からコピーした旧C++・候補C++へ実行し、内部状態と照合する。native検査は固定GCC 13.3/UBSanで実行し、private観測はテスト翻訳単位だけで有効にする。

残る義務は、暗黙copy構成子のAST監査・共通生成・意味対応、copy/move代入とmove、逆アッカーマン償却である。公開版の番兵/経路圧縮違反と他分野の未検証部分も未解消である。


## コピー先の任意操作列後の元receiverとalias保存（2026-10-18）

`UfScalarOther.scalar_other`は全5操作の任意の成功fuelについて、対象カウンタのアドレス以外にある全scalarCellを保存する。4操作はscalar全件を保ち、uniteだけが対象カウンタを変更する。既存ready証明の出力と任意実成功をCppCallUniqueで同一化するので、特定のfuelや有限ケースの一致に依存しない。

`UfScalarTrace.binding_same`は、CallEffectsのslots/scalarBindings保存から、同じscalar slotのbindingが実行前後で同じであることを導く。カウンタ値が変わってもその保存先は変わらない。`calls_work_other`はこの事実でカウンタのアドレスを操作列全体にわたって固定し、任意有限有効列の終了/Strong/work/metadataと、カウンタ以外の全scalarCell保存を同じ出力状態へ構成する。

`UfCopyPreserve.Inv.after_other/calls_keep_inv`は、別ownerのbuffer保存とカウンタにaliasしないscalar保存を元receiverのInvへ復元する。`copy_calls_both`ではコピー先カウンタをコピー前のmemory長に置き、全ての旧scalarCellのアドレスがその長さ未満であることを読取り成功から導く。元receiverとコピー先のownerも同様に分離する。

この結果、任意Strongな元receiverのコピーから任意有限有効列の実終了、操作列終了後の元・コピー先の両Strong、work≤コピー前work+n+4+m*budget(n)を同じ出力状態で証明した。さらにコピー前に成功した全scalarCellの解決と、コピー前に成功した任意vector要素参照の同じ値を保存する。元で拒否されていた参照すべての結果が同じとは主張しない。コピー先の要素参照やコピー先カウンタは実操作で更新される。

`tests/test_union_find_copy_preserve.py`は、既存の実構成→コピー→全5method混在12操作の結果をrun_calls_uniqueで一般定理の出力へ同一化する。終了後の元Strongを回復し、元receiverで再び同じ操作列を実行できることを確認する。空列、再コピー、任意Strong/任意有効列/異なる型の同slot bindingへの一般定理適用も検査する。

この接続もcopyReceiverの状態モデル上の証明である。暗黙C++ copy構成子のAST監査・共通生成・意味保存、代入/moveと償却αは引き続き未完了。


## コピー前から任意操作列までの全ピーク境界（2026-10-18）

`UfCopyPeak.initial_components`はコピー直後のliveSが旧+4、vector binding長が旧+1、scalar peakがmax旧scalarPeak(liveS旧+4)、outer peakがmax旧outer(新scalarPeak+新storagePeak)であることを示す。scalar baseが旧memory長以下であることを前提とし、自然数減算の切捨てを無視しない。

`copy_envelopes`は通常構成子と同じ常駐増分を使い、既存`UfConstructedPeak.receiver_envelopes`をnodes=0で再利用する。コピー後のmethod budgetはコピー前を基準に、scalarEnvelope=max旧scalarPeak(liveS旧+旧vector bindings長+117)、storageEnvelope=max旧storagePeak(旧nested live+n+2-旧storage baseline)以下となる。

`actual_history_peak`は、任意実成功のcopyReceiverと任意有効操作列の実結果に、scalar/storage/outerの境界を適用する。outerはmax旧outer(scalarEnvelope+storageEnvelope)以下で、過去のouterだけが大きい状態も保持する。追加の計数は操作数mを含まず、scalar側にはnも現れない。これは既存モデルのcell/binding/header単位で、実測bytesではない。

`copy_history`は実コピー・実操作列の終了、元・先Strong、全旧成功scalarCell/整数要素参照保存、work、常駐増分と全3ピークを同じoutにまとめる。最終liveSはコピー前+4、最終nested liveSpaceはコピー前+n+1である。`UfConstructedPeak.scalar_resident/storage_resident`もそのまま適用でき、常駐領域と一時領域の増分を分離できる。

`tests/test_union_find_copy_peak.py`は混在12操作の実出力、outer履歴だけ1億、scalar/storageの小さい別履歴、scalar/storageの非零baselineへ一般境界を適用する。12/24操作で同じ全ピーク、空列、default0のgetter列、任意Strong・任意有効列、常駐領域基準の補題を検査する。

これらのexact work/peakは直接copyReceiverモデルの定義による。暗黙C++ ASTを通常NProgramのprepare/body/finish経由で生成する場合には、それらの一時binding・復元コストを含む実生成モデルへ境界を接続する必要がある。AST受理・生成・意味保存、代入/move、償却αと公開版違反は未完了。


## 暗黙copy ASTの実体化・宣言監査（2026-10-18）

class_copy.pyで原ヘッダーからconst元の暗黙copyを実体化し、field/sourceパラメータの同一宣言ID、初期化順、標準vectorコピーのidentityを監査する経路を追加した。coverageはmember_identity_onlyで、共通Lean実行モデル生成・copyReceiverへの意味保存はまだ未完了。プロファイルと拒否条件は[class_copy_audit.md](class_copy_audit.md)。


## 共通評価器とのwhole state同値

`UfClassCopyBridge.copy_equiv`は、generic `CppClassCopy.copyClass`のi32 vector+scalar2件profileを、任意NState/LayoutのcopyReceiverへOption結果ごと同一化する。成功したStrongだけに限定せず、const元やnとvector長が異なる表現状態も同じ値をコピーする。既存work/peakは同じstateの成分として保持する。監査計画から生成したprofile/copy定義を同じ同値証明へ接続した。source field/slot対応とcall site loweringの証明はまだ未完了。詳細と検査は[class_copy_audit.md](class_copy_audit.md)。
