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
現在のcompanion経路は各recordが単一scalar fieldである場合を扱う。
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
