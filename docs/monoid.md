# monoid

`cp::MonoidMul<T>`、`cp::MonoidMax<T>`、`cp::MonoidMin<T>`は、値`x`と二項演算・単位元をまとめるクラス。セグメント木などに渡す。原本は`experiments/library/cpp/algebraic_structure/monoid.hpp`。

## APIと前提

3クラスとも公開フィールド`T x`、値からの暗黙構築、既定構築、静的`e()`、hidden friendの`op(a,b)`を持つ。公開版にはqualified `cp::op(a,b)`もある。型パラメータT、コピー代入できない型、ADLによる選択を維持している。既定型は原本の`ll`と同じ`std::int64_t`。

入力と途中の整数値がC++型に収まることを一度だけ前提とする。特にMulの積が範囲を越えないことが必要。Tの演算とコピーの意味・費用は、その型の契約による。任意のTについて結合則や単位元の法則が自動的に成立するとは仮定しない。

## 純粋モデルと機械翻訳

`Proofs/Cpp/Lib/MonoidMath.lean`で`mulOp`・`maxOp`・`minOp`と、元の数値traits分岐を保つ`maxIdentity`・`minIdentity`を定義する。C++正本から`Proofs/Cpp/Gen/Monoid.lean`を生成し、`Proofs/Cpp/Monoid.lean`が全15入口（3クラス×値構築・既定構築・e、hidden/qualified op各3）について返り値と正常停止を示す。

`std::is_floating_point_v<T>`と`numeric_limits<T>`は、型引数ごとの`Cpp.NumericTraits "T" T`として渡す。整数型を同じLean Intで表しても、そのC++型の境界値を使う。非浮動小数型の単位元はmin/max、浮動小数型は無限大対応なら負/正の無限大、それ以外はlowest/maxとなる。破棄される浮動小数分岐のために、ユーザー型へ単項minusを追加要求しない。標準契約・型の対応条件は[翻訳規則](translation.md)と[信頼境界](trust_policy.md)を参照。

純粋モデルの法則は次の条件下で証明する。

- Mulの結合則は`Semigroup T`、両側単位元は`MulOneClass T`。
- Max/Minの結合則と値の選択・上下界は`LinearOrder T`。同じ範囲内の2値からの結果もその範囲に残る。
- Maxの両側単位元は`maxIdentity ≤ x`、Minは`x ≤ minIdentity`。無特殊化のユーザー型のnumeric_limits値が最小・最大であるとは決めつけない。

これらの代数的条件はモデルの演算と実際のTの演算が対応する場合に適用する。独自ADLのmin/maxや丸めのある乗算を、一律に線形順序・半群とみなすものではない。

## 計算量と境界条件

モデルの仕事量は値構築1、eとopが2、既定構築が3 tickで、すべてO(1)。各操作の入力・結果・コピーを保つ固定frameは最大4スカラーセル、入れ子呼出しのframeを4セル保つ上界を加えても8セルなので追加領域はO(1)。Tの表現サイズや演算費用は別契約である。C++のヒープ、オブジェクト寿命、Leanの実行スタックのバイト数を数えるモデルではない。

整数の最小・最大、0・1、同じオブジェクトを両引数へ渡す場合も扱う。NaNを含むMax/Minの結合則・単位元則は主張しない。浮動小数の一般の演算誤差・Mulの丸め誤差は未証明として台帳に残す。浮動小数型をC++ APIから除いてはいない。

## 検査

`tests/monoid.cpp`で整数極値・乱数・暗黙変換・copy-only型・ADLとqualified op、原本と同じ既定型を検査する。`tests/monoid_floating_identity.cpp`ではfloat/double/long doubleの負値・極値・両無限大、default/eと両側のopを検査する。C++テストはASan/UBSanとテンプレート先行includeで行う。

登録差分ケース`tests/diff/monoid.py`は公開fieldを直接読み、hidden/qualified両opと単位元をC++/Leanで比較する。登録は整数10型（int、long long、long、short、signed char、char、unsigned char、unsigned short、unsigned、unsigned long long）。共有の構築回帰では型ごとの境界、同じLean carrierへの異なる型の束縛、単項minusを持たず既定値7のユーザー型、doubleの両無限大も確認する。

2026-11-16: 新方式切替後の全56部品・313検査のローカル全件gateが成功した。固定仕様照合、変更126モジュールのLeanカーネル再生、独立カーネル44,069宣言の検査も成功。必要な旧共通補題と旧変換器用のテスト参照だけを分離した。実push後のCI・配布リリース更新は未確認で、浮動小数の一般演算誤差の残件も保持する。

## 元のソースからの変更

namespaceをcpへ移し、既定のllを同一型のstd::int64_tで明記する。標準min/maxを見つけるlocal usingを置き、元のADLを保つ。既存公開版のqualified opも残す。3クラスを1ヘッダ・1TOML・1文書にまとめ、型だけの検証用witnessと有限型の明示具体化は不要になったため撤去した。元の機能・入力型の制限は追加していない。

library3の別原本の未検証APIや浮動小数の誤差については、[移植台帳](experiments_status.md)と[調査事項](experiments_findings.md)に残る項目を含めて追跡する。
