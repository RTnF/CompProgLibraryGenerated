# 同じクラスソースからの構成子・メソッド生成

`verifier/context_class_ir.py` の `emit_context_class` は、同じ C++ ファイルと
qualified class 名から、次の既存生成経路を一つの Lean 出力へまとめる。

- `Construction`: `class_copy_layout` の全対象構成子、宣言順の field 初期化、
  field の型・権限・export slot、mutable/const copy profile。
- `Calls`: `context_method_ir` の全対象非 static メソッド、const overload、
  FieldDecl からの receiver 引数写像、Context 上の `callFuel`。

両経路が出力する source SHA-256 と開始・終了時のソースを照合する。
生成途中で異なるソースを読んだ場合は拒否する。各経路の import を出力の先頭へ
まとめ、同じ namespace の下で各モデルを型検査できるようにする。関数名や
ソースハッシュから既成の意味モデルを選ばず、既存の AST 監査と変換規則を使う。

対象は既存の両経路がともに受理する部分言語に限る。先頭に一つの flat vector、
続いて scalar fields を持つ構成可能なクラスを扱い、対象メソッドで vector の
再割当を伴う操作は拒否する。例えば `push_back` を行う追加メソッドを黙って
生成対象から除外しない。公開 bundle では class 内の宣言種別も検査し、
static method、member template、本体のない method/constructor、static data、
conversion、friend、nested class、type alias など、生成対象へ接続していない
宣言を拒否する。field・アクセス指定・本体のある通常構成子/メソッドと、
監査で扱う既知の暗黙宣言以外を黙って省略しない。
元の `context_method_ir` の部分メソッド選択は引き続き独立の経路であり、
公開 bundle の宣言検査と併用できない。
構成子の field 順序・型・権限と標準 vector 操作の
契約は既存生成器の監査に従う。C++ から評価器への意味対応は引き続き
[信頼方針](trust_policy.md)の対象であり、生成自体を意味保存の Lean 証明とはしない。

`tests/test_context_class_ir.py` は公開切替用 Union-Find fixture から生成し、
通常 5 メソッド、const 3 メソッド、両構成子と copy profile が、それぞれ
既存の証明対象と全状態で `rfl` 一致することを Lean で確認する。
構成子の export 関数の対応と、const query の実 receiver 引数写像も検査する。
構成子の初期値やメソッドの返却 field を変えると、SHA の差だけでなく
生成モデルの本体も変わることを確認する。途中のソース差替えと resize
メソッド追加、および未生成になる class 宣言の追加は拒否例で検査する。
明示した部分選択経路が維持されることと、公開 profile で部分選択を
許さないことも検査する。

構成子 export は `NState`、メソッド呼出しは `Context` の既存評価器を使う。
これらを同じ出力に収めたことだけでは、両状態の接続、任意 caller の AST、
copy/move assignment、move construction、scope 終了や任意の寿命混在列の
正しさを保証しない。公開 registry は `translation = "context_class_ir"`、
`qualified_class = "cp::UnionFind"`、`bridge = "verifier/nested_bridge.py"` で
この経路を選べる。公開宣言は指定した `cp::` 直下のクラス一つだけとし、
別クラス名・追加の公開関数・異なる bridge は拒否する。bridge は通常どおり
ソースハッシュと公開宣言を監査し、生成 Lean 全文を登録モデルと比較する。
ソースハッシュだけの更新では古いモデルを受理しないことも検査する。
実際の公開部品はまだこの経路へ切り替えていない。公開 Union-Find 切替、
元実装との差の解消、既存公開定理を保持した登録モデルの更新は未完了である。

## 複数vectorメンバーの構築と呼出し

`emit_context_class(..., member_exports=True)` は、複数のflat整数vectorとscalarが宣言順に入り交じるクラスを、共通NState上の構築・メソッド呼出しとして生成する。既定のContext/copy profile経路は維持する。新経路は同じTUの各FieldDeclと暗黙copy初期化子の型・ID・権限を監査し、copyの実命令列も生成する。一般クラス状態からのcopy後置条件・caller AST・寿命・総資源まで検証済みとは扱わない。

構築段階のthisメソッドは既存inlinerで実field局所変数へ展開し、宣言順の型付き配置からCppConstructorMultiFinishのexportを生成する。メソッドはvectorを元のvector間の順、scalarを元のscalar間の順で正規化し、返されたObjectRefのvectorSlots/scalarSlotsから実引数を組み立てる。scalar参照・値渡し・const/mutableの監査と、外部参照がfield自身を指す場合の保守的な参照渡しを共用する。void結果やpush_back等は、既存NProgramが受理する構文・標準操作の範囲で扱う。引数数と各種field数を検査し、明示的receiverConstがtrueなら非constメソッドを拒否する。この値を元caller ASTのオブジェクト型・評価順へ接続する証明はまだない。

深いsequenceは32命令ごとにprivateなCommand定義へ切り出す。同じ右結合の命令木を定義参照で共有し、命令の順序・scope・課金を変更しない。`share_commands=True` は既存の深度上限設定を出力せず、標準上限で型検査する。分割前後のNProgram全体のrfl一致を、分岐の各側に70代入がある生成ソースで検査する。

`test_multi_member_constructor_void_calls_growth_and_field_alias` は2vector/2scalarの同じ実状態から、構築時helperと参照引数更新、void更新、const読取り、field自身への参照alias、vector伸長を続け、LeanとC++/UBSanで照合する。従来経路の登録モデルとの全文一致・定理との対応は維持する。新経路の任意caller AST、const view生成、class copy/move/assignment/destructionと総資源、公開registryへの採用は未完了である。

`tests/test_beats_wide_candidate.py` のmember bundle回帰は、実候補から生成した構成子がBeatsConstructCall.program、内部helperを含む全14メソッドが既存BeatsInstance、生成descriptorがBeatsConstructorFieldsとrfl一致することを確認する。生成出力には資源上限設定を含めない。構成子・メソッド本体の一致と、元caller AST・全寿命・総資源の検証範囲を分けて記録する。

複数メンバー経路の各メソッドは `arguments_of_fields` も生成する。任意のvector/scalar slot列と正しい外部引数数から、実adapterが返す引数列を証明する。参照渡しのfieldはscalarReference、値渡しは元型のvariable式を保つ。slotが連続することやfield値が構築時と同じであることは仮定しない。

Beats回帰は、任意のvector slot写像とscalar base、receiver状態、fuel、引数式について、6つの生成呼出しと既存CallのOutcome全体の一致を示す。成功だけでなくfault/exhaustedや更新状態・課金も同じである。`tests/lean/beats_member_receiver.lean` はこの対応と既存BeatsReceiverRestoreを使い、生成chmin後の実receiverを生成calc_maxへ渡し、数学的な結果・更新後Scalars/BVecsを導く。各操作のSafe等の前提は維持し、任意長操作列や総資源の証明とは扱わない。

同fixtureの `generated_construct_update_query` は、元callerの実root入力grantから生成構成子、返された実ObjectRefでの生成chmin、更新後の生成calc_maxまでを接続する。構築成功やfield条件は途中結果から導出し、呼出し側の追加前提にしない。元の4*n<2^31・入力値域・各操作のSafe条件を保ち、結果の数学的意味と最終Scalars/BVecsまで示す。borrowed child header入力と全寿命・償却・総資源は引き続き残件である。

## 複数メンバーを持つconstオブジェクトの構築

member_exports経路の `*_exportViewFuel(..., targetConst)` は、構築本体を通常の宣言権限で実行し、終了時に `declaredWritable && (!targetConst || mutable)` を各fieldへ適用する。constオブジェクトの構成子内でも、通常fieldの初期化・書込みを妨げない。通常exportFuelは維持する。scalarは既存restrictValues、vectorは新restrictVectorsで制限し、元の権限を超える要求は拒否する。全rootの移譲後にscopeを一度破棄し、元callerの参照別名と構築中の書込みを保持する。

生成するMemberViewの一般定理は、vectorのowner/element/header不変・要求flags・件数・権限非昇格、scalarの値不変、終了成功と選択/無関係rootのModels・実caller prefix・binding/scopeの保持を示す。構築終了は通常終端とbare returnの両方を扱う。共通部8定義・定理の依存3037宣言を固定nanoda/標準stackで検査する回帰も含む。

実クラスの回帰は、int/long longの3vectorと3scalar、通常/const/mutable宣言、構成子中の書込みとreturn;、const methodによるmutable更新をLeanとC++/UBSanで照合する。別のクラスでは元scalarへの書込みとreadonly別名の保持、追加fieldだけのview制限を確認する。既存オブジェクトへのconst参照view、caller ASTからのconstness導出、class copy/move/assignment/destructionと総資源は引き続き残件である。

## 複数メンバーの暗黙copy命令

Construction.copyFieldsは、監査した元FieldDeclの宣言順にscalar宣言とvector copyの記述を作る。sourceのObjectRefはvector/scalarごとのslot列なので、宣言IDに対応した各列の位置を使って元の順序へ戻す。Construction.copyFuelは通常NStmt/Commandを使い、結果のObjectRefは宣言順で追加された実slotから各種fieldを選ぶ。constなsourceから通常のcopy先を作るときも、元のbinding権限をコピー先へ流用せず、宣言とcopy先のtargetConstに従って新しいcell/rootの権限を決める。

全sourceのkind/type/slotを最初の確保前に検査する。初期状態で不存在のslotが先行fieldのcopyによって有効になることを防ぐ。MemberCopy.invalid_sourceは検査失敗時に命令列を実行せずfaultになることを示す。copy_completeは実primitiveのSteps列を合成し、copy_ready_completeは各中間状態のtyped source読取り・vector型対応・frame配置からprimitive成功を導いて合成する。fields.length+1はこの命令列の評価fuelであり、payloadコピーの仕事量・追加領域の上界ではない。

3vector/3scalarの回帰は、const sourceからの通常copy/const copy、copy先だけの変更、元の内容保持、宣言順の実slot、後から有効になり得る不正sourceの拒否をLeanとC++/UBSanで確認する。Beatsの回帰も15vector/2scalarのcopy後に更新・queryを実行し、結果[6,5,6]で元の木との独立性を確認する。

MemberCopy.Sourcesは、初期状態のtyped scalarCell読取りと、対応整数型の所有vector rootのslot/resolve/型対応だけを要求する。sourceのwritableは要求しない。GoodはframeのwellFormedとrootWritable表の長さ一致を表す。source_copy_completeはこの初期条件から全Readyを構成し、copy成功、Goodの保持、元の全scalar読取りと所有root vector読取りの同一性Keepsを導く。中間状態の読取りやprimitive成功を前提として追加しない。copy_of_fieldsは同じ証明を各生成クラスのcopyFuelと実ObjectRefへ渡す。view/copy共通部のこの一般証明までの依存3290宣言は固定独立kernelでも確認した。

`CppFrameResolveExtension.resolve_kept` は、同じ既存prefixを持つ有効なframe拡張の下で、任意のElementについて成功済みのresolveを保持する。rootと借用したchild headerの両方を扱い、必要なowner/slotの範囲は元の成功から導く。元は失敗していた不正な参照が拡張後にも失敗するとは主張しない。

`MemberCopy.PreservesContainers` は、コピー対象以外も含む元callerの全vector slotについて、成功済みの型付きresolveとbinding/bufferの一致を表す。`ready_preserves_containers` は実Ready列からこれを導き、`source_copy_preserves_containers` と各生成クラスの `copy_containers_of_fields` は初期Good/Sourcesからコピー成功とともに保証する。コピー対象のfieldは従来どおりflat整数vectorだが、保持するcallerの参照は入れ子型・借用childも含む。二段の借用header、readonly binding、捕捉済み整数参照を持つ具体例を既存の独立kernel回帰へ加えた。任意callerのAST、構築へのchild入力、assignment/move/destructionと混在寿命列の接続は別途必要である。

`tests/lean/beats_member_copy_proof.lean` は、readonlyを含むBeatsの15所有vectorのVOKGと2scalarの読取りから、targetConstの両場合の17field copy成功と元の読取り保持を導く。全copy先fieldの一般的な値・配置の後置条件、仕事量/peak、任意caller AST・assignment/move/destructionの証明は残る。
