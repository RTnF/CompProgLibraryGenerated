# 旧ライブラリのGroup／Mapping／Monoidの有限具体化

原本は `experiments/library3/cpp/AlgebraicStructure/{Group,Mapping,Monoid}.hpp` と
`experiments/library/cpp/algebraic_structure/monoid.hpp`。
公開field、hidden friend、委譲構築、`template<class U> U apply(U)` の値渡しを
変更せず、`template_class_ir.lower_template_class` で具体化したモデルを生成する。
元のソースからの変更はない。公開版との重複をAPIの同一性とは扱わず、原本を保持する。

| 原本の具体化 | 生成モデル | 確認する内容 |
| --- | --- | --- |
| `GroupSum<long long>` | 5 | 値構築・既定構築・単位元・opの全プログラムと既存モデルの一致。逆元は原本の`e().x-x`のまま、任意の型付きcallerで結果`-x`、停止、元メモリ保持、`ScalarPost2 0 80` |
| `GroupAffine<long long>` | 10 | 構築2種・単位元・op・invのa/b各モデルが既存モデルと一致。任意fuel/caller/argumentsでcallFuelも一致 |
| `Affine<long long>` | 12 | 構築2種・ide・compose・invのa/b各モデルが既存モデルと一致。`apply<long long>`と`apply<int>`は値渡しを保った一般callerの結果、停止、元メモリ保持、`ScalarPost2 0 80` |
| `MonoidMul<long long>`（原本2系列） | 各4 | 値構築・単位元・opの全プログラム/callFuelが既存モデルと一致。原本の委譲された既定構築は任意の型付きcallerで結果1、停止、元メモリ保持、`ScalarPost2 0 70` |
| `MonoidMax<long long>` / `MonoidMin<long long>` | 各4 | 原本のstd::max/minを変更せず生成。値構築・単位元は既存モデルと一致。任意の型付きcallerでopの結果・停止・元メモリ保持と`ScalarPost2 0 100`、既定構築は各整数端点を返して`ScalarPost2 0 70` |

整数演算の前提は型の値域と中間演算の未定義動作がないことである。Sumの逆元では
入力と`-x`がlong long範囲、Mappingの適用では`a*x`と`a*x+b`がlong long範囲である。
`apply<int>`は入力をint範囲とし、結果をint範囲へ制限しない。
GCC 13.3 LP64の既存符号付き変換契約に従い` signedDecode 32 (a*x+b)`を返すことを示す。
Affineのinvは原本の整数除算式をモデル化するものであり、任意の整数係数に対する
数学的な逆写像の存在を主張しない。既存モデルの前提・定理は`Proofs/GroupCall.lean`を参照する。

`tests/test_original_template_classes.py`は原本から毎回モデルを生成し、
`tests/lean/original_{sum,mapping,mapping_int,monoid_mul,monoid_select}.lean`と全プログラム一致定理をLeanで確認する。
指定した全定理の依存閉包を固定nanodaでも検査し、許可する公理は既存の標準3種だけである。
`tests/imports/original_*.cpp`は具体化とC++/UBSan回帰の共通入力であり、外部サイトと通信しない。
`apply<double>`のC++結果も比較するが、その浮動小数のLean証明は含まない。

生成入口は具体化前後のソースとwitnessのhashを照合する。同じTUのalias/primary/record IDと
元forced sourceへの帰属を確認し、全要求メソッドの本体不足や未指定のmember templateを拒否する。
型検査probeが必要な式は、同じ具体化文脈でprobeを実行する機能を実装するまで拒否する。
返却するcoverageは具体的な型引数・member instance・モデル一覧を含み、任意T/Uと完全な
C++ object/lifetimeを検証済みとするフラグはfalseのままにする。

未完了なのは任意T/U、浮動小数、公開fieldの一般的な直接読書きを含むcaller AST、
完全なobject/lifetime、copy/move/assignmentと混在操作の意味・総資源である。
各fieldモデルの独立した証明を、複数fieldを一度に評価する原オブジェクト全体の証明へ
拡大しない。C++の元APIを狭めず、台帳は部分検証のままとする。

## 入れ子型の有限具体化

`TemplateInstance(('long long',), witness, nested_members=('RangeMax',))` を
`lower_template_class` の `RangeAddRangeMaxMin` に渡すと、原本
`experiments/library/cpp/algebraic_structure/monoid_lazy.hpp` の
`RangeAddRangeMaxMin<long long>::RangeMax` を選択する。
`nested_members` はkeyword-onlyの識別子tupleで、既定の空tupleでは従来の外側型を選ぶ。
型や整数の引数は外側templateへ渡し、非templateの入れ子recordを順に辿る。

同一Clang TUでcontrolled aliasの参照ID、入れ子recordと親recordのID、
外側specializationとprimaryのIDを結ぶ。各段のTemplateInstantiationPatternが
対応するgeneric定義のIDを指すことと、全定義が元forced sourceに帰属することを要求する。
型の消去では選択した完全修飾名とinjected class名を区別し、別namespaceや
グローバルの同名型を部分一致で消去しない。coverageに実際のnested pathと選択型を記録する。

`tests/test_nested_templates.py` が生成し直す4モデルについて、
`tests/lean/original_nested_max.lean` は既存MonoidMaxモデルとの全プログラム一致、
任意fuel/caller/argumentsのcallFuel一致、元と同じ前提・結果・停止・メモリ保持・
資源上界を検査する。原本CPPのAPIと型は変更しない。
この有限具体化はmonoid_lazy全体の検証完了ではない。複数fieldを持つrecord型のmember template引数、
条件付きrecord返却、任意Tやコピー効果を含む完全なobject/lifetimeは残件である。

原本 `RangeAddRangeSum<long long>::RangeSum` の8fieldモデルは
`tests/lean/original_nested_sum.lean` で検査する。`x` はlong long、`size`はintのまま、
両方の値引数を評価・束縛してから構築結果を返すこと、単位元と委譲defaultの両fieldが0、
opの2プログラムと任意fuelのcallFuelが既存モデルに一致することを示す。
任意の型付きcallerに対して停止・元メモリ保持・構築の`ScalarPost2 ... 70`を確認し、
opは既存と同じ中間加算が各型範囲内という前提と上界72を保持する。
各fieldを別々に検査することを、原object全体の同時構築・寿命の検証とは扱わない。

## record型のmember template引数

`lower_template_class` の `companion_instances` へ、同じwitnessを持つ
`(qualified_class, TemplateInstance)` のtupleを渡す。receiverを0、companionを1以降とする
`RecordArgument(index)`を `member_instances={'apply': [(RecordArgument(1),), ...]}` に指定する。
各型のcontrolled aliasを同じClang TUで生成し、source/primary/nestedの帰属と宣言IDを検査する。
実体化memberの本体も、元sourceのgeneric method pattern IDへの対応と定義位置を検査する。
actual TemplateArgumentのRecordType.decl.idが選択recordのIDに一致することを必須にし、
生のC++型文字列、異なるTU/source、未選択record、重複した選択を拒否する。
companion経路は単一scalar fieldと複数scalar fieldのrecordの混在を扱う。
モデル名や短い型名が衝突する場合は、scopeを区別できる経路まで拒否する。

原本 `RangeAddRangeMaxMin<long long>` のRangeAdd/RangeMax/RangeMinから13モデルを生成する。
`tests/lean/original_record_apply.lean` は非const receiverを保ったapply2種について、
書込み可能なreceiver bindingと型の値域条件の下で、任意のscalar値引数の結果`x+v`、
停止、元メモリ保持、`ScalarPost2 caller Sinit res (1+e.nodes) 100 ...`を確認する。
同じプログラム/callFuelの一致も確認するが、元C++の別々の型をaliasで同一化しない。
copy/move/destructorの非自明な効果はtrivial-record監査が拒否し、
任意Tと完全なobject/lifetimeの検証済みフラグはfalseを維持する。

回帰には別namespaceのflat `Box`/`OtherBox` の5モデル生成とnative/UBSan、
witness側の明示的member specializationで結果を10から106に変えた例の拒否も含む。
特殊化本体が選択record内に実体化されていない場合は未具体化として拒否し、
本体がある場合もgeneric pattern IDと定義位置の一致を要求する。

## companion内の複数fieldとコピー返却

`RangeAddRangeSum<long long>` のRangeAdd/RangeSumを同じcompanion bundleに選ぶと、
元のクラスを分割せず13モデルを生成する。複数fieldを返す構築では、すべてのprimitive値引数を
一度だけ局所変数へ評価し、全fieldを宣言順で初期化してから結果を投影する。
先に初期化したfieldへの参照はその局所変数へ対応付け、初期化前fieldの参照を拒否する。
副作用を伴う構築式や独自copy/move/destructorなど、値消去で扱えない効果は拒否する。

`tests/lean/original_mixed_add_sum.lean` は13モデルの一般caller定理を登録する。
両投影で積と和の型範囲を要求し、値渡しcompose・非const receiver・負のint sizeを保持する。
prepareからcallの返却までの結果、停止、元callerメモリ保持、work/space上界を確認する。

`RangeSetRangeSum<long long>` は18モデルを生成する。返す値が同じrecordのtrivial copy/moveで
ある場合は、元recordの暗黙構成子の署名とparameterの全field IDを確認し、全fieldを読んで投影する。
条件付きcopyは条件を一度評価し、選択したbranchだけを実行する。`return x` より前の
値引数fieldへの書込みも保つ。`tests/lean/original_mixed_set_sum_samples.lean` は全18モデルを覆う
38の有限事例を持ち、noop両分岐、負/零size、危険な積をnoop時に評価しないこと、更新時の
overflowを両投影が拒否することを確認する。RangeSumの8モデルは全NProgramの一致を示してAdd版の一般caller定理を共有し、RangeSetの既定構築/idの4モデルも任意の有効callerについて結果・停止・元メモリ保持・資源上界を示す。値構築・compose・applyの6モデルも、`original_mixed_set_sum_value_ctor.lean`・`original_mixed_set_sum_compose.lean`・`original_mixed_set_sum_apply.lean` に一般caller定理を登録した。composeは条件を一度評価して選択したrecordの全fieldを読み、値渡しを維持する。applyは書込み可能なreceiver参照2個と値引数2個を維持し、更新対象を新しい値引数領域に限定する。積の範囲はnoopがfalseのときだけ要求し、負のint sizeも保つ。全18モデルについて結果・停止・callerメモリ保持・IRのwork/space上界を検査する。これは任意Tや原object全体の寿命・総費用の検証完了ではない。

これらの再生成・Lean/固定nanoda・C++/UBSan・独自copy/move/destructor等の拒否検査は
`tests/test_nested_templates.py` に登録する。原本のAPIとソースは変更しない。
companionを使わない既存の複数field経路は、既存証明のプログラムを維持しており、
他fieldの評価を含む新経路への移行と証明が残る。各投影の成功を原object全体の同時評価、
完全な寿命、総費用の証明とは扱わない。任意T/完全object lifetimeのフラグはfalseを維持する。

## record自身と複合型の区別

scalarの値消去・複数field分割が受け付けるのは、選択したrecord自身とトップレベルの
const・参照修飾である。`Probe *`、`vector<Probe>`、`Probe (&)[2]`、関数ポインタなどを
record自身として扱わない。desugared typeの全体を照合し、recordを含む未対応の複合型は
引数・返却型・値消去する局所宣言の境界で拒否する。単一fieldのmethodの返却型は、
署名を書き換える前にも検査する。複合型への対応を追加するときは、元のABIと対応する
評価器・証明が必要であり、unused引数でもscalar fieldへ読み替えてはいけない。

`test_record_value_type_boundaries` は単一/複数fieldとpointer/vector/array/function pointerの
引数、pointer/vectorの返却型とpointer/vector/arrayの局所宣言を組み合わせた18の有効なC++ fixtureをnative/UBSanで確認し、
変換器が意図した複合型境界で拒否することを検査する。const・参照の通常recordも認識する。

共有証明は `tests/lean/scalar_record_copy_fields.lean` と `original_mixed_set_sum_callers.lean` に置く。両fieldのtyped評価とコピー後のscope終了による元メモリ/束縛の復元も一般化して確認する。この共有はfieldモデルのNProgram同一性であり、元の別々のC++ record型を同一化する変更ではない。

## 条件式内の構築呼出しとSet/MaxMin

既知の呼出しを含む整数prvalueの条件式は、結果を受ける局所変数とIfStmtへ変換する。
条件の処理を一度行い、各operandの引数評価・呼出し・結果代入を選択されたbranch内だけで行う。
branch内の一時変数はそのscopeで破棄する。参照やobjectを返す条件式、short-circuit右辺の呼出し、
loop headerの呼出しはこの拡張の対象外であり、従来の拒否境界を維持する。
`tests/lean/inline_scalar_conditionals.lean` の9事例は、入れ子の条件とbranchの実行回数、
未選択のゼロ除算の非評価、選択したゼロ除算がfaultになることを確認する。C++/UBSanとも比較する。

原本 `RangeSetRangeMaxMin<long long>` のRangeSet/RangeMax/RangeMinから18モデルを生成する。
`tests/lean/original_mixed_set_extrema.lean` は、max/minの構築2種・e・opの8モデルについて
既存MonoidInstanceと全NProgram/callFuelの一致を示す。RangeSetの構築2種・id・composeの8モデルは
前述のSet/Sumと全NProgram/callFuelが一致し、登録済みの一般caller定理を共有する。
applyのmax/min両モデルについては、非const receiverの書込み可能な参照2個と値引数1個を維持し、
任意の型付きcallerでnoopなら値引数、そうでなければvを返すこと、停止、元メモリ保持、
`ScalarPost2 ... 110`を示す。選ばれないrecordの構築は評価しない。

さらに `tests/lean/original_record_apply.lean` の `RecordComposeAudit.compose_correct` で
Add/MaxMinのcomposeの値渡しを保った一般caller定理を登録した。両引数と和が符号付き64bit範囲内なら
和を返し、停止、元callerメモリ保持、`ScalarPost2 ... 70`を示す。
ここで扱うTはlong long、member templateのMは選択した元のRangeMax/RangeMinである。
任意T・任意M、単一object全体の寿命・総費用、公開API復元、原本1ファイル全体の移植は未完了である。

## field投影を使わないRangeSetの構築とcopy

`class_copy_layout` のstructured template_instance経路から、原本Set/SumのRangeSetを
既存のconstructor member export / MemberCopy評価器へ接続した。
long longとboolの両fieldを1つのObjectRefとして構築・copyし、コピー先の独立したcell/権限とscope終了を検査する。
元source・field宣言・暗黙copy構成子のIDを同じTUで監査し、witnessの途中変更も拒否する。
原本と公開headerは変更しない。詳細と残る任意型・class返却/lifetimeの境界は `class_copy_audit.md` を参照する。

登録検査は新4＋既存layout4の計8testsで終了0（106.356秒）。9事例とcopyの一般layout/observer/value/position/work/space定理は固定nanoda3329宣言で成功し、全検査入力hashは不変だった。
LLでのこの構築/copy接続を、任意Tやclass全API・完全object lifetimeの完了とは扱わない。

## RangeSumの委譲構築をobject stageへ接続

原本Set/Sumの `RangeSum():RangeSum(e()) {}` を、factory返却objectの全fieldを一度構築し、
trivialなmove/copyでtargetへ移すscalar stageとして生成する。引数・factory側の構成子body・外側bodyの順を保つ。
`tests/lean/original_delegating_object_layout.lean` は返却値用の4cellとtargetの2cellを含む
全NProgramの形、および構築後にtargetのlong long/intだけをexportすることを確認する。
負のsize、const先、copyの独立性、非export呼出しでの一時領域の回収も確認した。

`scalar_delegation_bodies.lean` は改名した別classでconstructor parameterのbody更新、
factory内のfield更新、外側body、さらに委譲chainのbodyが順序どおり働くことを5事例で確認する。
`scalar_delegation_failure.lean` は他方のfieldの除算が失敗すると、default/非export/directのいずれもfaultとなる4事例を持つ。
C++/UBSanも比較し、nontrivialな特殊メンバー等の未対応境界は実CPPから拒否する。
新旧関連16tests、独立kernel、manifest対象入力のhash不変を確認した。
これらは有限のtyped instanceの評価器の検査である。LLの既定構築の任意callerは下節で扱う。
任意T/M、値構築など残る一般object caller、C++の厳密なobject寿命・総費用、class全APIの返却/caller接続と公開復元は未完了である。

## 既定構築の一般callerとexport

`original_delegating_constructor_general.lean` の10 rootsは、well-formed frame・scope/base等の
通常の前提を満たす任意callerについて、元の既定構築stageの実行、typedな2fieldのexport、
旧memory/binding/slotと既存scalar読取の保持、新fieldの読取を証明する。
StageState/ExportStateは全buffer内容・forest・root権限も保持し、既存vectorの参照解決と要素読取の保存を示す。
本体work14/need P.length+15、prepare/body/export込みscalar work増分18以下、scalar/storage/outer peak上界を持つ。
構築結果のtargetConstは任意で、readonly/mutableをそのまま扱う。値構築等の一般object callerや
任意T/M、C++厳密lifetime/総費用とは区別する。登録検査は固定nanoda4198宣言とC++/UBSanで成功した。

## 値構築の一般callerとexport

`original_value_constructor_general.lean` の11 rootsで、元のRangeSum(T,int)のLL/int具体化について、
異なる型の2引数式の準備、全field構築、const/mutable先へのexportを接続した。
負のsizeを含む型の全範囲を保ち、既存scalar/vectorの内容と読取、新fieldの値・権限を示す。
本体work4、need callerP.length+11、引数評価を含むscalar work増分e1.nodes+e2.nodes+10以下。
固定nanoda4261宣言と境界値16組のC++/UBSanで登録検査成功。
任意T/M、厳密なC++ object寿命と総費用、返却object/caller接続、公開API復元と原本全体の移植は残る。

## Static factoryの全field export

`factory_exports=True` をmember exportへ追加し、元RangeSum::e()の全fieldを1回materializeして直接exportする。
`original_factory_export_general.lean` の10 rootsは、任意callerについて値・型・権限、旧scalar/vectorの保持、
本体work10/need callerP.length+11、prepare/body/export込みscalar work増分14以下とpeak上界を示す。
新factoryの10事例と元構築/委譲の回帰を含む6testsが固定nanoda2868/4315/2834/2648/2815宣言とC++/UBSanで成功した。
元factoryのclass返却はexportViewFuel経路を対象とし、unit stageのcallFuelをその返却契約として扱わない。
一般T/M、object引数やfriend/free function/memberのclass返却、厳密C++ lifetime/identity/総費用と公開API復元は残る。

## Friend返却の全field経路

`friend_exports=True` で元RangeSum::op(const RangeSum&,const RangeSum&)を全object exportへ接続した。
ObjectRefの全fieldをcaller上で型・値・権限・個数まで検査し、既存のstatic factory exportは既定のまま維持する。
11事例で結果/入力保持/alias/負size/const/各fieldのoverflow/不正・失効済み入力を確認。
別の3 rootsで任意P/参照先/入力値について元本体の全field結果・入力prefix保持・cost13/need P.length+15を証明した。
最終4testsは固定nanoda3276/4315宣言とC++/UBSanで成功した。
任意callerのfriend prepare/run/exportは後続節で接続した。厳密なclass identity、値渡しobject、任意T/MやC++厳密lifetime/総費用は残る。

## Add/Sum・Set/Sum friendの任意caller接続

`original_friend_object_call.lean` の12 rootsで、両familyの元RangeSum::opをtypedな2object参照から
prepare/run/exportへ接続した。負sizeやaliasを許し、結果2field、const権限、旧scalar/vectorの観測、
scope/live/storage workとpeak上界を保持し、抽象総work増分25以下を示す。
別々の原本宣言・witnessからfresh生成し、固定nanoda4086/4086宣言とC++/UBSanの2testsが成功。
元CPP型/APIは変更していない。任意T/M、値渡しobjectや他familyの一般object経路、厳密identity/lifetime/総費用は未完了。

## 2026-11-08: Add/SetのMax/Minを全object本体で検査

`test_extrema_friends_return_complete_objects_for_both_families` は4つの原本nested型ごとにfreshモデルを作る。`original_extrema_object_general.lean` の一般本体証明とmin/max一致、および `original_extrema_object_values.lean` の全field結果・alias・const・不正参照の検査を固定kernelへ渡す。型やfriendをCPPで合併せず、証明だけを再利用する。本体の任意prefixに対する結果・入力保持・bindingを含む全PS一致・work/need上界までを扱い、Max/Minの任意callerでのprepare/run/export一般定理は残る。

元の浮動小数単位元の不具合はCPP側の4箇所で修正した。float/double/long doubleの負値・極値・±infinityで単位元をnative/UBSan検査し、非浮動小数のe()要件を保つ。std引数の宣言監査とcompiler-resolved constexpr選択の共通化は `class_copy_audit.md` を参照する。LLモデルの証明やnativeの成功で任意T・浮動小数の形式意味論・厳密lifetimeの完成を主張しない。最新の実行結果はhandoffに記録する。

## 2026-11-08: Max/Min friendを任意callerのprepare/run/exportへ接続

`original_extrema_object_call.lean` を4原本モデルの登録検査に追加した。typedな2入力参照から任意callerをprepareし、元本体のPS一致をQSへ接続し、完成した1field objectをconst/mutable先へ返す。aliasも許す。旧scalar/vector観測保持、scope回収、IR work増分47以下とpeak上界を扱う。登録検査の終了結果はhandoffを参照する。原本全体・任意T/M・値渡しobject・厳密なidentity/lifetimeの検証は残る。

## 2026-11-08: 元RangeAdd composeのrecord値引数

Add/MaxMin・Add/Sum両原本のRangeAddについて、composeの2つのrecord値引数をscalar値コピーとして全object stageへ渡す。id/composeの結果field、値snapshot、alias/const、未来slot/不足field拒否、加算overflowを `original_value_add_objects.lean` の8 rootsとnative/UBSanで確認する。mixed value/referenceの2field回帰は `scalar_factory_value_arguments.lean`。既存のcopy監査でnontrivial copyは拒否し、rvalue参照等も拒否を維持する。登録検査の最新結果はhandoff参照。値引数の一般callerや条件付きrecord返却・途中更新・任意Tは引き続き未完了。

## 2026-11-08: RangeAddの値引数一般caller

`original_value_add_call.lean` の13 rootsは、Add/MaxMin・Add/Sumの元composeを値引数のprepare/run/全field exportへ接続する。readonly/aliasを許し、入力2値と和がlong longに収まることだけを算術の前提にする。任意scalar式のノード数Eに対しIR work増分E+12以下、ObjectRef snapshotからは14以下で、旧scalar/vector観測・scope・storage workとpeakを保つ。2値prepare補題は `Proofs/CppScalarValuePrepare.lean` に共有し、元RangeSumの定理名と命題を維持したwrapperでも回帰した。固定nanoda4072宣言ずつ/RangeSum4316/mixed2820宣言・native/UBSan・入力hash不変が成功。Setの条件付き返却と値引数更新、任意T/M・厳密identity/lifetime・全ファイルの移植は未完了。

## 2026-11-08: 元Set composeのconditional copy

Set両系統の元composeは、lvalue conditionalで選んだrecordをimplicit defaulted copy constructorへ渡す。selected recordのexact signatureとtrivial特殊メンバーを確認してparameter全fieldのviewを作り、条件を一度const boolへ保存してから元順序で全fieldをコピーする。値構成子を呼び直さないのでnoop=trueの非ゼロvも保持する。`original_set_object_values.lean` の10 roots、直接copy/moveの `scalar_record_copy_returns.lean` の4 rootsは固定nanoda2828宣言ずつ/2821宣言とnative/UBSan・入力不変で成功。副作用付き条件と入れ子record conditionalは未対応として拒否する。既存一般callerの変更後回帰はhandoff参照。Setの任意入力/任意caller一般定理、途中更新、任意T/Mと厳密identity/lifetime、原本全体の検証は未完了。

## 2026-11-08: Set composeの一般本体と任意caller

`original_set_object_general.lean` の4 rootsは、元bodyのreadonly条件flagを保ったまま任意Pと型付きx/f/y/gに対する結果・停止・work20/need P.length+21・全PS一致を示す。`original_set_object_call.lean` の11 rootsは共有prepare_literals4から元bodyと2field exportへ接続し、任意callerの旧scalar/vector観測保持、const結果、work増分32以下とpeakを示す。readonly入力とaliasを許し、writable・相異・非負性の前提は加えない。両原本freshモデルの固定nanoda4102宣言ずつとnative/UBSan、既存Add両系統4072宣言ずつ/元RangeSum4316宣言の回帰が入力不変で成功。途中更新/異なるreceiver・result recordのapply、任意T/M・厳密identity/lifetimeと原本全体は未完了。


2026-11-08: 元Set/Sum・Add/Sumのrecord返却applyを、同一TUの異なるreceiver/result recordとして共通class-copy経路へ接続した。receiverは元fieldへの参照、RangeSum引数は全field値snapshotとし、前置更新後に全x/sizeを返す。const/noexceptを保持し、member pointer型のcompiler照合で別familyの同名record取り違えを拒否する。元ソースを変更せず、負size・noop時の未選択乗算・overflow・alias・const/readonly・不正slotと引数不変を有限LLのLean roots/native/UBSanで確認する。登録回帰と実行結果は[引き継ぎ](agent/handoff.md)を参照。applyの任意入力/任意caller一般定理、任意T/M・厳密object identity/lifetime、公開API復元、原本全体/全137は未完了。


元Set/Add applyの任意入力本体は `original_set_member_general.lean` / `original_add_member_general.lean` で証明する。任意prefixとreceiver参照先、型付き値コピーx/sizeに対して、prefix全保持と全結果PS一致を結論に含める。Setはnoop時に積の表現可能性を要求せず、active時のみ要求する（work13/7、need≤P.length+13）。Addは積と加算の両方を要求する（work14、need=P.length+16）。sizeのi32→s64拡大は入力型から導く。負sizeを除外しない。任意callerからのmixed参照/値prepareと全field exportの接続、任意T/M、厳密identity/lifetime・公開API復元は別の未完了項目であり、本体定理だけで移植完了とはしない。


Set/Sum・Add/Sum applyの任意caller接続:

`original_member_prepare.lean` の2 rootsは任意型の1参照/2参照と2値snapshotを元callerから準備し、初期memory/bindings/slots/frame/scopeとIR work7/9、peak保持を示す。receiverには元のnonconst member呼出しに必要な書き込み権限を要求し、record値引数の元fieldには要求しない。

`original_add_member_call.lean` と `original_set_member_call.lean` の各11 rootsは、元apply本体から全field exportまでを任意NStateへ接続する。Addは積と和の表現可能性、Setはnoop=falseの場合に限り積の表現可能性を前提にする。負size、元のreadonly引数、型の合うscalar slotのaliasを排除しない。結果x/sizeを返し、const destinationは新fieldの権限だけを制限する。旧scalarの値/参照、vectorの内容/resolve/read、scope、storage workを保持し、IR総work増分はAdd≤24/Set≤25、scalar/storage/outer peakも上界を与える。class objectの厳密identity/lifetimeと任意T/M、member template apply、公開APIの復元・原本全体の完了とは区別する。登録テストは元ソースを変えずfreshモデルを生成し、独立kernelとC++/UBSanを確認する。最新実行結果はhandoff参照。


明示member templateとrecord conditional返却:

`receiver_methods` の3要素形 `(record_index, method_name, (RecordArgument(selected_index),))` は、既存 `instantiate_members` が監査した元source patternと同一TUのrecord宣言IDに一致する具体化だけを使う。型名文字列で別の同名recordを指定しない。元C++の `apply<選択型>` へのmember pointerをcompilerで照合し、receiver/result/引数の完全修飾型とconst/noexceptを検査する。source名・型引数・decl IDはmetadataへ残す。

元Set/MaxMinの `return noop ? x : v` は、bool条件に応じたimplicit copyと値構築である。新member経路は純粋boolの1段conditionalに限り、branch外にscalar結果slotを置き、選ばれたbranch内だけで元constructorまたは監査済みcopyをmaterializeして全fieldを渡す。コピー時に値構成子を呼び直さず、未選択branchの演算やconstructor bodyを実行しない。追加slotはIR上のscalar作業領域であり、C++のクラス既定構築を挿入するものではない。static/friendの従来制限と、入れ子conditional・副作用条件など未対応形の拒否は維持する。

`original_template_member_result.lean` は元Add/Set×Max/Minの全field返却、負値・noop/id・const結果・readonly/未来slot・overflowを有限LLで確認する。`member_constructor_choice.lean` は値構成子がxに100・sizeに1を加える2field recordを使い、copyでは元の両fieldを保ち、選ばれた構築だけを実行すること、未選択overflowを避けることを確認する。登録結果はhandoff参照。新具体化に対する任意入力/任意caller一般定理や任意T/M、厳密identity/lifetime・公開API全体の復元は未完了。
