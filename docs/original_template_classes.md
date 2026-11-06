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
