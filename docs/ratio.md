# ratio

作業ツリーの公開側を原本APIへ復元した。全56登録部品の全件gateと、固定仕様・公理依存・両kernelによる公開全体監査は成功した。1引数構築の値・領域の接続定理を追加した後も、全件gateと公開全体監査が成功した。原本単位のpush/release更新は未完了である。

## API

`cp::Ratio<T = std::int64_t>` は有理数を非公開の2フィールド `n,d` で保持する。構築は2引数（正規化）と1引数（分母1）。前置/後置の増減、単項正号/負号、四則の複合代入、Ratio同士および左右スカラーとの12形の二項演算、`<=>`・等値、stream抽出/挿入を備える。公開ライブラリの共通規格は C++23。

`Proofs/Cpp/Gen/Ratio.lean` は公開ヘッダから生成し、`Proofs/Cpp/Ratio.lean` が純粋有理数モデル・停止・仕事量・論理payloadの仕様へ接続する。`tests/ratio.cpp` は10整数型で全API、参照を返す操作の同一性、自己除算、非正規化のstreamをASan/UBSan付きで検査する。`tests/diff/ratio.py` は各登録型に共通の非overflow領域で全APIをC++/Lean比較する。

## 元のソースからの変更

旧公開版の固定型・3フィールド・構築/normalizeのみという縮小を作業ツリーで解消した。元のtemplate、既定型、構築、増減、単項演算、四則・左右スカラー演算、比較・等値、入出力を1クラスに保持する。namespace/標準名の修飾と同じ型を指す `std::int64_t` 表記を用いる。GCD/LCMは時間上界が規定されない標準関数から、非公開static関数の明示Euclidへ置き換えた。
移行用の公開ヘッダコピーと、旧RatioCall/Generated.Ratio検証は削除した。標準GCD/LCM版との本文比較とfrontend検査には、`tests/fixtures/ratio_reference.hpp` / `ratio_numeric.hpp` を用いる。公開実装と対応証明の正本はlibrary/とProofs/Cpp/Ratio.leanである。
原本に実在した左辺スカラー4演算のコンパイル失敗と、除算の符号・自己参照の不具合は原本でも修正した（`docs/agent/fixes.md`）。

## 仕様と前提

算術は数学整数を基準とし、入力と途中値が式・格納先のC++型に収まること（実装で絶対値を計算するときはその値も含む）を部品の前提とする。有理数としての演算では分母が非ゼロ、除算では除数の分子も非ゼロである。大小比較と正規表現の不変条件には正の分母を用いる。whileモデルの燃料は `2^64` であり、呼出しごとの前提をLean定理に明示する。
`operator>>` は原本どおり正規化しない。等値は分子・分母のフィールド等値で、正規化済みの場合に有理数値の等値と一致する。生の `2/4` と `1/2` は等値判定で偽、大小比較では等しい。

`RatioMath.lean` は正規化・四則の値、正規分子/分母、GCDで既約かつ正分母という不変条件を証明する。公開側の対応証明は `Proofs/Cpp/Ratio.lean` に統合した。fresh検査も公開対応証明を直接読み、別の証明コピーを正本にしない。標準関数・free helperのfrontend fixtureには、対応するテスト用契約を保持する。入出力は標準操作と状態を明示的なパラメータとする。

入出力は、stream操作が正常終了し、その結果・仕事量・領域の契約を満たすという前提で合成する。抽出の仕事量は `1 + readN + readD` 以下、出力は分母が1を超えなければ `1 + writeN`、超えれば `1 + writeN + writeSlash + writeD` 以下である。streamの最終状態、返すstreamの一致、抽出した生のフィールドも同時に示す。Int層の保持値の領域は `8*(bits+1)` に各stream操作の最大ピークを加えた値以下。空白の読飛ばし・数値の書式化・bufferなどstream内部の仕事量と領域は呼出し先の契約に属し、I/O全体を定数時間とはしない。

入力の絶対値が `2^bits` 以下なら、正規化・構築・単項負号・比較・四則の仕事量は `O(bits+1)`。全12形の二項/スカラー演算は、加減 `18*(bits+1)`、乗算 `13*(bits+1)`、除算 `25*(bits+1)` 以下を、値の正しさと停止と同じ仕様で示す。標準GCD/LCMの時間仮定は用いない。

論理データ領域は固定個数の保持値と反復の現在値を数える。`RatioSpace.lean` と `RatioArithmeticSpace.lean` では、後段で計算する名前付きの値も同時に保持すると見積もる保守的なモデルを用いる。Euclidは3payload、LCMと正規化のピークはそれぞれ `10*(bits+1)`、`11*(bits+1)` ビット以下。四則のcontextとcalleeを合成すると `81*(bits+1)`、ラッパーの元の4フィールドを加えると `89*(bits+1)` 以下である。2引数構築・単項負号は `19*(bits+1)`、増減は `24*(bits+1)`、比較は `39*(bits+1)`、1引数構築・コピー・等値の整数payloadは `8*(bits+1)` 以下である。新方式の数学整数モデル上の上界であり、C++ヒープ・オブジェクト寿命やLean評価スタックの実メモリ量を証明した指標ではない。stream内部の領域は前述の呼出し先契約と合成する。

## 公開APIと証明の対応

以下は28個の公開呼出し入口を全て含む。対応定理は `Proofs/Cpp/Ratio.lean`、領域の共通補題は `Proofs/Cpp/Lib/RatioArithmeticSpace.lean` にある。領域は純粋モデルの保持値を数えるもので、C++の各文を実行した履歴ではない。

| API（入口数） | 結果・停止・仕事量の対応定理 | 論理領域の対応 |
| --- | --- | --- |
| 2引数構築（1） | `ratio_euclid_init`、`ratio_euclid_init_input_bits`、`RatioMath.normalize_value` | `ratio_euclid_init_payload` |
| 1引数構築（1） | `ratio_euclid_init_scalar_value_payload`（有理数値・1 tick・返却フィールド） | 同定理のコピー保持値上界 |
| `<=>`・`==`（2） | `ratio_euclid_compare_input_bits`、`ratio_euclid_equal_run`、`ratio_euclid_equal_normalized_value` | `ratio_euclid_compare_payload`、`ratio_euclid_equal_payload` |
| 前置・後置の増減（4） | `ratio_euclid_{prefix,postfix}_{increment,decrement}_value` | `ratio_euclid_shift_payload`（更新前後と後置のコピーを含む） |
| 四則の複合代入（4） | `ratio_euclid_{add,sub,divide}_input_bits`、`ratio_euclid_multiply_bits` と `RatioMath` の値の法則 | `ratio_euclid_{add,sub,mul,div}_source` と同名の `_payload` |
| 単項正号・負号（2） | `ratio_euclid_unary_plus_value`、`ratio_euclid_negate_input_value_bits` | `ratio_euclid_copy_payload`、`ratio_euclid_negate_source` と `_payload` |
| 二項四則のRatio同士・左右スカラー（12） | `ratio_euclid_{add,sub,mul,div}_{Ratio_Ratio,Ratio_T,T_Ratio}_run` と `_input_value_bits` | 上記coreの領域と `additive_wrapper_bits` / `product_wrapper_bits` を合成。スカラーは分母1の構築へ帰着 |
| stream抽出・挿入（2） | `ratio_extract_run` / `_work`、`ratio_insert_{integer,fraction}_run` / `_work` | `ratio_extract_payload`、`ratio_insert_payload` と各stream操作の契約 |

型範囲の前提のもとで非折返し演算を数学整数として扱う点は、`docs/redesign_2026-11.md` の決定事項2に従う。C++のtemplateや入力領域を特定の整数型へ狭めることはしていない。符号なし型の具体演算についての追加の法則と差分検査は次節に示す。

## 整数型との対応

符号なし型の法則は `UnsignedMagnitude.lean` にまとめ、UInt8/16/32/64の具体的な演算から証明する。自然数への解釈、ゼロ、剰余、範囲、単位元、除算、表現可能な積・和、非負の差、順序を扱う。これらの法則から `Proofs/Cpp/Ratio.lean` で生成モデルに対応させる。

| 操作 | 対応の条件と結果 |
| --- | --- |
| GCD・正規化・構築 | 生成フィールド・停止・仕事量。分母非ゼロならRatの正規表現と一致。正規化は入力bit数に対し `6*(bits+1)` 以下 |
| LCM | LCMが型の表現容量に収まれば自然数/IntのLCMに一致。仕事量 `5*(bits+1)` 以下 |
| 乗除算 | 交差約分後の積が表現可能なら生成フィールドと有理数の積・商に一致。除算は非零除数を要求 |
| 加減算 | LCM・スケール後の積・和が表現可能、差が非負なら生成フィールドと有理数の和・差に一致 |
| 比較 | 分母GCDで除した後の積が表現可能なら自然数のOrderingと一致。分母非ゼロなら有理数の順序に一致。仕事量 `6*(bits+1)` 以下 |
| 前置・後置の増減 | 和が表現可能、差が非負なら値が±1変わる。前置は新値、後置は旧値を返す。仕事量は前置1・後置2 tick |
| 単項正号・負号 | 正号は値を保ち1 tick。Intの負号は正規化を経て有理数の符号を反転する。符号なし型の表現可能な負号（ゼロ）は正規形0/1を返し3 tick |

C++の小幅整数の昇格を伴う具体化と、UInt8/16の法則の証明は別である。unsigned char/shortのテンプレート検査はIntへbindし、intに昇格した途中値を格納型の幅で折り返さない。入力・格納値の型範囲は部品の前提に含む。明示的な小幅unsigned宣言/キャストの一般翻訳は引き続き未対応である。有限幅の型で範囲外に出た演算について、数学的な有理数としての正しさを主張しない。

## 検査範囲と残件

原本の直接テスト、公開ヘッダの全API・単独include・既定型・自己除算、Fraction算術期待値、C++/Lean差分をASan/UBSan付きで検査する。算術は10整数型、既定数値streamはshort/unsigned short/int/long long/unsigned/unsigned long long、文字streamはchar/signed char/unsigned charを検査している。文字型ではraw byte経路で0〜255の各byte、6種類の空白、NUL、負の分母、EOF/failを検査し、差分driverの8bitと文字型のsignednessという前提も静的に確認する。前置・後置の増減は8整数型で返値と更新状態を検査し、符号付き型では負数・ゼロからの減算も含める。unsigned32/64では最大値付近の正規化、約分前だけ積が大きくなる四則・比較、ゼロになる差、自己参照の複合演算も検査する。単項正号も8整数型、負号は符号付き5型と符号なしのゼロで値とreceiver不変を検査する（charの非零負号は処理系の符号に依存するため対象外）。有限な差分検査を全型の証明の代用にはしない。

開発用のRatio単体監査は `python3 tools/audit_ratio.py` で再現できる。公開ヘッダをfresh翻訳して登録モデルと照合し、公開対応証明を読み直して公理依存・leanchecker・nanodaを検査する。入力hash付きの証跡は `.cache/wip/ratio_audit/result.json` に保存する。公開用カタログとの照合・全件gate・全体監査は別に行う。

公開ソースを対象とした単体監査では、leanchecker --freshとnanodaの6,165宣言検査が成功した。公開全体監査では固定仕様・公理依存の照合と、変更moduleの再生判定、全rootの輸出coverage、nanodaの43,867宣言検査が成功した。全件gateはCI分配変更後も全312検査を通過した。これらはローカルの検証結果であり、push後CIの実測ではない。

全APIの型・領域の対応は上表に整理した。残件は原本単位のpushと配布物の更新、push後CI20分の確認である。公開model/proof/catalog登録と旧検証・移行候補の重複整理は完了した。明示的なunsigned char/short宣言・キャストの一般翻訳は未対応だが、Tを使う本ヘッダには現れない構文である。
