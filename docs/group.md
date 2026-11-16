# group

`cp::GroupSum<T = std::int64_t>`、`GroupMul<T = std::int64_t>`、`GroupAffine<T = std::int64_t>` を1ヘッダで提供する。原本は `experiments/library/cpp/algebraic_structure/group.hpp`。生成モデルは `Proofs/Cpp/Gen/Group.lean`、純粋モデルは `Proofs/Cpp/Lib/GroupMath.lean`、対応証明は `Proofs/Cpp/Group.lean`。作業ツリーでは新方式へ切替済みで、公開全体監査と全56部品の全件gateが成功した。push/release更新は未実施である。

## APIと動作

- GroupSum: 値/既定構築、`x()`、`e()`、hidden friend `op`、`inv()`。演算は和、単位元は0、逆演算は単項負号。
- GroupMul: 同じ形で積・単位元1・`1 / x`。値構築は非ゼロをassertする。整数では非ゼロ値でも逆演算が0になれば構築assertが失敗する。
- GroupAffine: 値/既定構築、`a()`、`b()`、`e()`、hidden friend `op`、`inv()`、`apply(const T&)`。`op(p,q)` の係数は `(p.a*q.a, p.b*q.a+q.b)`。可換な係数ならpを先に適用する合成である。
- 既存公開APIのqualified `cp::op` 3形も保持する。hidden friendと異なる宣言であり、両方を生成・証明・差分検査する。

原本20入口とqualified演算3入口、計23入口を対象とする。返すフィールドと正常停止時の仕事量は、値構築/読み出し/applyが1 tick、e/逆演算/opが2 tick、既定構築が3 tick。時間はスカラーの算術演算を単位とするO(1)。Tの演算自体の計算量はTの契約に属する。

## 前提と数学的性質

入力と途中値が演算・格納先の型に収まることを前提とする。整数の除算は0方向への切捨てで、除数は非ゼロ。GroupMulでは値/演算結果が非ゼロでconstructor assertを通ることが正常終了の条件となる。

純粋モデルで、加法/乗法の結合律・単位元・逆元、アフィン写像の合成・結合律・単位元・逆元を証明する。必要な代数構造を各定理に明示し、整数や浮動小数を体と仮定しない。アフィン合成の適用との一致はCommSemiring、一般の逆元はFieldかつ非ゼロ傾きが条件。整数では別の `affineIntInv` をInt.tdivで定義し、傾き±1の逆元法則と、任意の有効な入力について生成関数が返す切捨て値を区別する。

例えば整数の `GroupAffine(2,3).inv()` は係数 `(0,-1)` を返し、真の逆写像とはしない。GroupMulの整数逆演算が正常終了する値は±1。浮動小数の丸め誤差は未証明で、doubleのC++回帰成功をFieldの法則の証明として扱わない。

## 論理領域

純粋モデルのFrameは、構築/読み出し/e/既定構築のコピー、単項演算、二項演算、アフィン構築、適用、逆演算、合成の保持値を列挙する。最大10スカラーセルである。既定構築にはfactoryと値構築の最大2呼出しがあり、それぞれの入力・結果に4セルを同時に見積もる8セルを加えても、全操作のピークは18セル以下、O(1)となる。コピーや合成では返却値を重複保持する保守的な上界である。

`model_all_operations_space` を公開仕様のrootに登録する。構築/読み出し/e/defaultはcopyまたはaffineCopy、Sum/Mulのinvはunary、opはbinary、Affineのapply/inv/opはそれぞれapply/inverse/composeへ対応する。各run定理が返す値をこれらのFrameへ代入する。Tの内部表現、C++のヒープ/オブジェクト寿命、Lean評価スタックの実メモリ量は数えていない。

## 元のソースからの変更

namespace/std名を修飾し、原本のllと同型のstd::int64_tを既定に用いる。元のT、全3クラス、コンストラクタ、暗黙変換、hidden friend、委譲構築、波括弧/暗黙return、const参照applyを保持する。既存公開版のnamespace opも残す。旧変換器だけのために置いたint/long longのwitnessと明示具体化は不要になった。

旧GroupCall/Generated.Groupの部品専用検証は撤去する。残る旧方式部品が必要とする共通補題だけを `LegacyScalarCallCore.lean` に残し、宣言の互換namespaceを保つ。元C++の正本や、新方式Groupの対応証明としては使用しない。

## 検査

`tests/group.cpp` はテンプレート先行include・ASan/UBSan、整数境界、署名、コピーを数えるT、暗黙変換、qualified/hidden演算、doubleを含む元APIを検査する。`tests/diff/group.py` の共通非overflow領域で10整数型のC++/Lean差分を行う。static eはnativeと既定構築の差分、個別の対応定理で検査する。signed非単位元のAffine逆演算はconstruction回帰でも検査する。

`tests/test_lean_model_construction.py` は公開ヘッダのfresh翻訳と公開証明・純粋モデルを直接組み合わせる。`test_group_apply_reference.py` は任意の入力値・初期tickについての適用定理と、等しい入力・順序を変えた入力の観測を確認する。const参照のC++型と引数コピーの検査はnative suiteに含む。

## library3旧版との未解消差

ここで復元したAPIは `experiments/library/cpp/algebraic_structure/group.hpp` のもの。`library3` のGroupはpublic field `x/a/b` を持ち、MappingのAffineはpublic field `a/b`、`ide/compose`、値渡しの `template<class U> U apply(U)` を持つ。現行のgetterと `const T& apply` だけで同じAPIとはしない。異型引数0.5での適用結果とGroupSum<double>の逆元の0の符号にも差がある。詳細と実比較は `docs/experiments_findings.md` を参照する。旧版を含む全体の統合・検証は継続中。
