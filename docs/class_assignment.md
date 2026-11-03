# vector と scalar フィールドを持つクラスのコピー代入評価器

`Proofs/CppClassAssign.lean` は、vector と宣言順の scalar フィールドを持つクラスのコピー代入を NState 上で実行する評価器を定義する。対象の形は既存の `CppClassCopy.Profile` と `ObjectRef` を使う。vector の代入後に各 scalar の値を読み、対応する代入先へ順に書く。結果は代入先そのものの ObjectRef とし、コピーした別オブジェクトを返さない。

この段階は評価器とその意味・資源・参照寿命の証明である。暗黙 C++ operator= の AST 監査と profile 生成は [class_assignment_audit.md](class_assignment_audit.md) を参照する。実 caller の ObjectRef/layout と呼出し境界の接続は未完了。候補 C++ や既存の公開定理、NState の定義は変更していない。

## 実コマンドとの対応と終了

`assignScalar` は source と target の scalarCell、型、有効値、書込み権限を検査する。`scalar_command` と `scalar_success` はこれが既存の `NStmt.assign target ty (.variable ty source)` の実行と一致することを示す。

`assignFields` は各代入の直前に source を読む。すべての source 値を先に snapshot する処理にはしない。既存の alias を含む状態でも宣言順の読書きを保つ。`fieldsCommand` と `fields_program` は同じ代入列を既存の Command/runFuel で実行し、状態・仕事量・正常終了が一致することを証明する。

`Ready` は各 scalar フィールドが読取り可能で、代入先が書込み可能という入力状態の条件。書込み後も他のセルの型と値の有効性が保たれるため、`fields_terminate` はこの初期条件から終了を導く。成功した代入列を前提にして終了の証明を代用しない。

`assignClass` は vector slot と同型の Frame を resolve し、前段のコピー代入を行った後に scalar 列を実行する。`class_terminate` は vector の型・権限・最大サイズと Ready から終了を示す。移動元などで vector 長と UF の scalar n が一致しない場合も、通常 UF メソッドの不変条件をコピー代入の入力条件として要求しない。scalar の読取り型や有効性、vector の型と領域の条件は維持する。

`class_success` は任意の実成功について戻り値が代入先に等しく、slots、scope、scalar binding と memory 長を保つことを示す。`class_wellFormed` は更新後 Frame の wellFormed を示す。自己代入では元と先の同じ buffer とセルを使う。

## データと寿命情報の対応

`primitive_data` と `frame_data` は、vector 代入の buffer/仕事量/peak/Frame の結果が ghost 世代関数に依存しないことを示す。`dataAssign` は世代0で定義した Frame への射影であり、任意の世代関数での実行と同じデータを返す。

`trackedAssignClass` は NState の外側で世代情報を入力・出力する。`tracked_class_data` はそのデータ射影が assignClass と一致することを示し、`data_lifts` は assignClass の任意の成功を任意の初期世代での成功へ持ち上げる。

scalar 代入が Frame を変えないことから、vector 代入時の世代更新がクラス代入の最後まで保たれる。`tracked_retired` と `ClassAssignments.no_resurrection` は、成功した任意のクラスコピー代入列でも、以前破棄された要素への参照が読めないことを示す。保存済み外部参照はこの世代を持つ TrackedReference で読む。単に世代を捨てて旧 Frame.read へ通すことは、この対応には含めない。

現在の NExpr.read/NStmt.write は vector 要素参照をその都度取得してすぐ使い、NArgument.scalarReference は scalar セルを指す。vector 要素への保存済み参照変数を今後 caller に追加するときは、その取得・読書きにも世代を接続する必要がある。reserve/clear/erase/resize 等を混ぜた任意操作列への寿命伝播も残る。

## 資源

scalar 代入は既存コマンドで各2仕事量。クラス評価器は vector primitive の仕事量にこれらと制御・戻り参照の1を加える。`class_success` の式は `out.work = initialScalarWork+updatedStorageWork+2*scalarFields.length+1`。Frame の vector 資源は既存の nested liveSpace/baseline による境界を使う。

`fields_metadata` は scalar memory/binding の個数が増えないことを示す。`fields_peak/class_peak` は scalar peak を `max initialScalarPeak (initialScalarLive+1)` 以下とし、scalar/storage を合わせた peak も開始履歴との max で抑える。この scalar 一時領域はフィールド数や vector 要素数に比例して増えない。baseline と過去 peak は保持する。

これは直接のコピー代入評価器の仕事量であり、まだ接続していない生成 operator= の呼出し prepare/finish 等を含むと主張しない。モデル単位であり、実測 CPU 時間や bytes ではない。

## 検査と残り

`tests/test_cpp_class_assign.py` は readonly な元、独立する scalar セル、別名、余剰容量の vector を用い、内容・宣言順・戻り ObjectRef・自己代入・既存メモリ保持・仕事量・peak を検査する。scalar 部分は実 Command/runFuel とも比較する。縮小→再拡張をクラス代入として実行し、旧末尾参照は拒否され、新しい参照は読めることを確認する。過去 peak と非零 baseline、型/権限/profile 長の不一致も検査する。

固定 GCC の Packet クラスでは暗黙 operator= の内容・先頭参照・readonly な元・自己代入と、戻り値が代入先への参照であることを ASan/UBSan で照合する。無効な C++ ポインタは使用しない。この有限照合は AST の監査・生成・意味対応の一般証明を置き換えない。

同じ TU の暗黙 operator= の実体化・宣言 ID 監査・profile 生成は [class_assignment_audit.md](class_assignment_audit.md) へ進んだ。次は実 caller の field slot/layout と代入式・戻り参照への接続が必要となる。move、公開版の差異解消、他の旧ライブラリの検証も引き続き未完了である。

UnionFind の実評価結果と数学的不変条件の対応、代入元・別オブジェクトの保持は [union_find_assignment.md](union_find_assignment.md) を参照する。
