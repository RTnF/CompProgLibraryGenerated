# コピー代入を型付き Frame と参照寿命へ接続する

`Proofs/CppFrameCopyAssign.lean` は、scalar vector のコピー代入を、既存の型付き nested `Frame` の resolve/grant/object/commit へ接続する。`TrackedFrame` は Frame に要素寿命の世代情報を添え、`TrackedReference` は従来の型・権限・アドレスを持つ参照に取得時の世代を添える。これらは証明用の情報であり、C++ が追加の配列を確保するという主張ではない。

既存の Frame/ElementRef/NState の定義、公開定理の文、候補 C++ は変更しない。この段階では、生成済み NProgram のクラス代入や暗黙 `operator=` の意味対応まで接続したとは扱わない。

## 実行と不変条件

`copyAssign` は代入先と元を同じ scalar 型で resolve し、代入先の書込み権限と最大サイズを検査する。前段のコピー代入 primitive を実行し、既存の Frame.commit を通して更新する。元は readonly の binding でもよい。自己代入では同じ owner の buffer を使い、内容・容量・epoch・寿命を保つ。

`assign_runs` は両 resolve・権限・サイズ条件から実成功と更新後の wellFormed を導く。`assign_result` は特定の primitive の結果を同じ成功へ接続する。逆向きの `assign_success` は成功した任意の Frame 代入からこれらの条件・結果・更新後の有効性を取り出す。正常終了を入力前提に要求するだけの定理で全入力の終了証明を代用しない。

`after_metadata` と `after_grant` は binding、root の権限、forest、参照への grant を保つ。`after_object_other` と `after_read_other` は異なる owner の元や他の buffer と参照を保持する。対象の parent、scope、型も変えない。

## 参照寿命

`elementRef` は現在の世代を記録する。read/write は世代が一致した後に、既存の型・owner・epoch・権限チェックを通す。`read_buffer` が flat な寿命モデルとの読取りの一致を示し、`prefix_read` は容量を再利用したときの生存する先頭要素の参照から更新後の値が読めることを示す。

`after_target_retired` と `read_retired` は、要素破棄や再確保で無効となった参照が読めないことを示す。`assign_retired` は成功した任意の Frame コピー代入について、この無効化を保つ。`Assignments.no_resurrection` は代入列全体に一般化し、元の木や型、代入先が途中で変わる場合も含む。`write_retired` は同じ参照からの書込みも拒否する。現在の世代を持つ新しい参照からは再構築された要素を読み書きできる。

この列定理の対象はコピー代入列である。reserve/clear/erase/resize、scope 退去などを含む任意の混在操作列への寿命情報の伝播は別の義務として残る。

## 資源量

Frame.commit は nested liveSpace と既存の baseline を使う。子の vector header は親の領域に含まれるため、flat Store.liveSpace の値へ置き換えない。

`after_space` は `newLive+oldCapacity = oldLive+newCapacity` を示す。root/child の header 数は変わらず、対象の容量の差だけが常駐領域に反映される。`after_work_peak` は仕事量への primitive 予算の加算と、`max oldPeak (nestedLive+(primitivePeak-(oldCapacity+1))-baseline)` を示す。これは Frame のコピー代入 primitive のモデル単位であり、class caller の prepare/finish 等の仕事量や実測 bytes/CPU 時間ではない。

## 検査と残る接続

`tests/test_cpp_frame_copy_assign.py` は親 vector と3つの child、別 root、tombstone、readonly alias を含む Frame で、縮小・再拡張・再確保・自己代入を確認する。古い末尾参照は再拡張後も読めず書けない一方、新しい参照は読み書きできる。元と他の参照、型／権限、非零 baseline、過去 peak の保持も確認する。

再確保の peak は nested 領域で33となり、子 header を二重計上する flat 領域では一致しない例を検査する。親の reserve で header が移動した場合、保存済みの子要素参照は読み取れ、古い child binding を resolve して新たな代入を行うことは拒否される。固定 GCC の nested vector で同じ内容・先頭参照・親 reserve・自己代入を ASan/UBSan で照合する。無効な C++ ポインタは使用しない。

次は NState/実 NProgram の参照・コマンド列への伝播、暗黙 class operator= の AST 監査・生成・意味対応、宣言順の scalar 代入への接続が必要となる。生成済みクラスのコピー代入、move、公開候補への昇格、他の旧ライブラリの検証は未完了である。

NState上の宣言順scalar代入と、データ射影／外側ghost世代の持上げは [class_assignment.md](class_assignment.md) へ進んだ。暗黙operator= ASTと実caller境界の生成接続は未完了。
