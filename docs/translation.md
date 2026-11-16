# C++ から Lean への翻訳（新方式）

`docs/redesign_2026-11.md` の対応層である。公開ヘッダの C++ を、意味論を一度だけ定めた制限構文として読み、`verifier/lean_translate.py` が Lean の関数へ機械的に翻訳する。翻訳結果（`Proofs/Cpp/Gen/*.lean`）について、部品ごとの証明（`Proofs/Cpp/*.lean`）が正しさと計算量のオーダーを示す。C++ を文ごとに記号実行する証明は作らない。

## 意味論（`Proofs/Cpp/Prelude.lean`）

- 関数は `Proofs.Cpp.M := StateT Nat Option` の値になる。状態は tick 数、`none` は「正常に戻らない」（`assert` の失敗、`while` ループや再帰が `Cpp.fuel = 2^64` 回を超えること）を表す。正しさの定理は結果が `some` であることを含むので、停止も示す。
- 整数型（`int`、`long long` など符号付き）は `Int`。部品ごとに「入力と途中の値が型の範囲に収まる」を前提として一度述べ、各演算の範囲は証明しない。`/` と `%` は 0 方向への丸め（`Int.tdiv`/`Int.tmod`）、`&`・`|`・`^` は 2 の補数（Mathlib の `Int.land` などと同じ定義）、`<<` は `2^b` 倍、`>>` は算術シフト。
- 符号なし 32/64 bit 型（`unsigned`、`unsigned long long`、`std::uint64_t`、`size_t` など）は `UInt32`/`UInt64` で、折り返しを含めて C++ と同じ意味になる。符号付き・符号なしが混ざる演算は、翻訳器が C++ の通常の算術変換（幅と符号から共通の型を決める）を自分の型付けで再現し、明示的な変換を挟む（符号付き → 符号なしは `UInt64.ofInt` で 2^64 を法とする値、符号なし → 符号付きは、変換先が広ければ値のまま、同じ幅以下なら 2^w を法とした 2 の補数での値 `Cpp.toSigned w`（C++20 の規定、GCC は C++17 でも同じ）。`unsigned __int128` は 2^127 未満で使う前提で整数として扱う。`v.size()` は `Int`（非負）で、Clang が挿入する暗黙の `size_t` への変換は使わない。
- `bool` は `Bool`、`std::vector<X>` は `Array X`、`std::pair<A, B>` は `A × B`。
- テンプレート引数 `T` は Lean の型変数になり、使った演算だけを型クラス引数として要求する（`+` → `[Add T]`、`<` → `[LT T] [DecidableLT T]`、`T s = 0` → `[Zero T]`、整数から `T` への変換 → `[IntCast T]`、要素の読み出しと値初期化 → `[Inhabited T]`。2 つの型引数 `S`、`T` の間の `a < b` → `[Cpp.HLt S T]`、`T` から `S` への暗黙の変換 → `[Cpp.Conv T S]`（`T` から整数型への変換も `[Cpp.Conv T Int]` など）。同じ型では `LT` と恒等写像が既定のインスタンス）。静的メンバーだけを使う型引数 `P`（ポリシー）の呼び出し `P::f(args)` は、関数に明示的な引数 `P : cp.<関数>.Policy_P ...`（使われた静的メンバーをフィールドに持つ構造体。引数と結果の型は使われ方から決める）を加え、そのフィールドの呼び出しに翻訳する。差分テストのハーネスは具体化 `P = "cp::DpHeight<long long>"` を `{ e := cp.DpHeight.e, ... }` として渡す。呼び出し先の要求も呼び出し元へ伝わる。証明は Mathlib の代数構造（`AddCommMonoid T` など）を仮定して述べる。値初期化（`std::vector<T>(n)`）は `default` で、`T` が数値のときに `default = 0` を仮定する定理がある。
- 範囲外の添字は C++ では未定義動作で、各部品の前提（添字が範囲内）で除く。モデルの `Cpp.get`/`Cpp.set` は全域関数にするために範囲外でも値を返すが（`default` を読む、書き込まない）、これは C++ の挙動の主張ではなく、定理と文書はこの値に依存しない。前提を満たす入力で範囲外アクセスが起きないことは、証明の中の添字の範囲と、サニタイザ付きテスト・差分テストで確かめる。
- C++ オブジェクトの寿命（コピー・ムーブ・破棄）とヒープ上の領域は扱わない。

## 翻訳の対象

| C++ | Lean |
| --- | --- |
| 自由関数・関数テンプレート | `def cp.f {T} [要求] (引数) : Cpp.M 出力` |
| クラス・クラステンプレート | `structure cp.C (T : Type)`（フィールド）と、メンバー関数ごとの関数 |
| const メンバー関数 | `cp.C.m (self : cp.C T) ... : Cpp.M R` |
| 非 const メンバー関数 | 出力に更新後の `self` を加える |
| コンストラクタ | `cp.C.init_<引数の型>`（重複がなければ `init`）。メンバー初期化子・既定のメンバー初期化子・値初期化の順 |
| 非 const 参照引数 | 出力に呼び出し後の値を加え、呼び出し側で書き戻す |
| 出力が複数 | 戻り値、参照引数（宣言順）、`self` の組 |
| 多重定義 | 名前に引数の型を付ける（`sum_int`、`sum_int_int`） |
| private メンバー関数 | 翻訳する。差分テストからは呼ばない |

文と式:

- `for (int i = a; i < b; i++)`（`<=`、`i--` と `>=`/`>` も）で、本体が `i` と上限の式の変数を変えず、上限が `size()` 以外の呼び出しを含まないもの → `for i in Cpp.range a b`（`Cpp.rangeDown`）。
- それ以外の `for`、`while` → `for _ in Cpp.forever do`（反復ごとに条件を調べて `break`）。`continue` の前に増分を実行する。
- 範囲 for（値または const 参照で、本体が範囲を変えないもの）→ `for x in v`。
- `if`/`else`、`return`、`break`、`continue`、局所変数の宣言（`let mut`）、代入、複合代入、`++`/`--`（文としてのみ）、`assert`（`Cpp.check`、失敗で `none`）、三項演算子（分岐に呼び出しを含まないもの）。
- 呼び出しは評価順に `let t ← f ...` として前に出す。`&&`/`||` の右辺と三項演算子の分岐の中の呼び出しは拒否する。
- 再帰は拒否する（定義の順序は呼び出し先が先）。

STL:

| C++ | Lean |
| --- | --- |
| `v.size()`、`v.empty()`、`v[i]`、`v.back()`、`v.front()` | `Cpp.size v`、`v.size = 0`、`Cpp.get v i`、`Cpp.back v`、`Cpp.get v 0` |
| `v[i] = x`、`v[i][j] = x`、`p.first = x` | `Cpp.set` の入れ子、組の更新 |
| `v.push_back(x)`、`v.emplace_back(x)`、`emplace_back(a, b)`（pair） | `v.push x` |
| `v.pop_back()`、`v.clear()`、`v.resize(n[, x])`、`v.assign(n, x)`、`v.assign(w.begin(), w.end())`、`v.reserve(n)`、`v.erase(std::unique(v.begin(), v.end()), v.end())` | `v.pop`、`[].toArray`、`Cpp.resize`、`Cpp.replicate`、`w` のコピー（tick は `w.size()`）、（何もしない）、`Cpp.unique`（tick は `v.size()`） |
| `std::numeric_limits<T>::min()`/`max()`（`T` は `int`、`long long`、`int64_t`） | 整数リテラル |
| `std::is_floating_point_v<T>`、`std::numeric_limits<T>::has_infinity`（型パラメータT） | テンプレート引数ごとの `Cpp.NumericTraits "T" T` のBoolフィールド |
| `std::numeric_limits<T>::min()`/`max()`/`lowest()`/`infinity()`（型パラメータT） | 同じtraits引数の `minimum`/`maximum`/`lowest`/`infinity` |
| `if constexpr (std::is_floating_point_v<T>)` のthen内の `-std::numeric_limits<T>::infinity()` | 同じtraits引数の `negativeInfinity`。他の場所の単項minusは通常の `Neg T` 演算 |
| `std::vector<T> v(n[, x])`、`{a, b}`、コピー | `Cpp.replicate`、`[a, b].toArray`、同じ値 |
| `std::min`、`std::max`、`std::swap`、`std::abs` | `min`、`max`、入れ替え、`Int.natAbs` |
| `std::sort(v.begin(), v.end())` | `Cpp.sort v`（安定な mergeSort。tick は `n (log2 n + 1)`）。C++ では同値な要素の順序は不定なので、定理は全順序（整列結果が一意）で述べる |

STL はドキュメント通りの契約・動作・計算量オーダーを持つものと認め（`docs/trust_policy.md`）、上の対応はその動作をそのまま定義したものである。STL の前提条件（添字の範囲など）は部品の前提として述べる。

`min/max` は明示した `std::min/max`、または関数内の `using std::min/max` から解決される2引数呼出しを扱う。局所usingはブロックのスコープに従い、依存した名前探索ではusingのshadow宣言のみを候補とする場合に受理する。同名のユーザー関数は通常の関数として翻訳する。他のusing宣言と標準min/maxの明示的テンプレート引数は未対応として拒否する。[using宣言の規則](https://eel.is/c++draft/namespace.udecl)と[標準min/maxの契約](https://eel.is/c++draft/alg.min.max)に基づく。比較演算とLeanのMin/Maxがこの契約に一致することは型の対応条件であり、ADLで別の動作へ変更する型の対応を証明したものではない。

数値traitsは[型カテゴリ](https://eel.is/c++draft/meta.unary.cat)と[numeric_limitsの契約](https://eel.is/c++draft/numeric.limits.members)に従うデータ引数で、公理や全型共通の境界値は置かない。`NumericTraits`の文字列タグはC++型パラメータ名に対応する。TとUが同じLeanのIntに具体化されても、別の引数としてintとlong longの境界を渡せる。型の対応条件としてtraitsの値がそのC++具体型・特殊化の値であることを要求する。無特殊化のユーザー型の境界値を数値ゼロと決めつけない。

constexprの両分岐をBool分岐として残し、未選択分岐のtraitフィールドは評価しない。浮動小数のthen内に限って負の無限大をtrait値として扱い、破棄される分岐のために非浮動小数型へNegを追加しない。この分岐の認識は上表の直接の条件式・直接の負の無限大式に限る。整数の差分driverはLP64の10型（signed/unsigned char、short、int、long、long long）について具体的なtraitsを渡す。doubleの両無限大と単項minusを持たないユーザー型も専用のnative/Lean検査を行う。この検査だけで浮動小数の一般演算の誤差を証明したとはしない。

差分driverの`field Class.field k`は、公開されたスカラー・vector・pairのフィールドを読む。private/protectedフィールドとrecordを含むフィールドにはこのコマンドを生成しない。CPPのgetter追加や、非公開表現へのアクセスをせずに、公開フィールドをモデルの投影と比較するための観測である。

ここにない構文・型・関数は `Unsupported` として拒否する。拒否された実装は `experiments/` に置く。

## 計算量（tick）

翻訳結果は次の点で tick を加える: 関数の入口で 1、ループの反復ごとに 1、`push_back`/`emplace_back` で 1（ドキュメントの償却 O(1)）、長さ `n` の vector を作る・コピーする・`resize`/`assign` するときに `n`（ドキュメントの O(n)）。STL 操作の tick はドキュメントの計算量のオーダーに合わせる。各反復・各関数の本体のそれ以外の部分は定数個の操作なので、tick 数のオーダーが C++ の実行時間のオーダーになる。部品の定理は tick 数の明示的な上界（例: `x.size() + 1`）を示し、そこからオーダーが従う。

## 差分テスト（信頼境界）

翻訳器そのものの正しさは証明しない。代わりに `verifier/diff_harness.py` が、翻訳した関数のシグネチャから同じコマンド言語のインタプリタを C++（公開ヘッダを呼ぶ、ASan/UBSan 付き）と Lean（翻訳結果を `lean --run` で実行）の両方に生成し、部品の生成スクリプト（`tests/diff/<部品>.py`）が出すコマンドで出力が一致することを確かめる。TOML の `diff.instances` に並べたテンプレート引数の具体化（例 `T = "long long"`）ごとに行う。

`verifier/model_bridge.py`（`check_public.py` の bridge 検査）は、ヘッダのハッシュと公開宣言、翻訳のやり直しと登録済みモデルの全文一致、証明がモデルを import すること、差分テストを確かめる。

## クラス内のfriend関数定義

クラス内に本体を持つfriend関数は、receiverを持たない自由関数として翻訳する。クラスの型引数はLeanの型引数として引き継ぎ、非公開フィールドの読取りも通常の構造体の射影になる。friendの型宣言やfriendクラステンプレートは未対応として拒否する。差分テストのC++側では非修飾呼出しでADLを使う。クラステンプレートの型引数はfriend関数自身のテンプレート引数ではないので、C++の呼出しには付けない。

`tests/test_lean_model_friend.py` は、型引数を持つクラスの非公開フィールドをfriend関数から読み、通常の名前空間関数も呼んで、サニタイザ付きC++と翻訳したLeanの出力を比較する。

`*this` の値の読取りは、その時点の全フィールドの組になる。前置・後置 `operator++` / `operator--` の定義と、`++*this` / `--*this` による前置メンバー呼出しを扱う。非constメンバーの出力には返却値と更新後のreceiverを別々に含める。後置実装の `C r = *this; ++*this; return r;` は変更前の値を返し、receiverだけを更新する。返却参照を別名として保存し後から変更する構文は対象に含めない。差分テストでは返却オブジェクトの追加とreceiver更新の両方を保持し、`tests/test_lean_model_friend.py` で前置・後置の増減それぞれの返却値とreceiverを比較する。

## C++規格と比較

登録の `standard` は `c++17` または、新方式（`lean_model`）では `c++20` を指定できる。AST抽出・公開宣言の照合・差分テスト・C++テスト・サニタイザ付きテスト・入出力テスト・テンプレート先行includeは同じ規格で実行する。全ヘッダの一括includeと配布物のinclude検査は、含まれる部品が要求する規格の最大値を使う。C++17の部品からC++20の部品への依存は登録エラーになる。翻訳器と差分ハーネスのCLIでは `--standard c++20` を指定する（既定はC++17）。規格を変えても未対応構文は引き続き拒否する。

整数と型引数の `<=>` は `Ordering`（`lt` / `eq` / `gt`）へ翻訳し、2方向の `<` で比較する。型引数には `[LT T] [DecidableLT T]` を要求し、C++の比較と同じ順序を使う。浮動小数の部分順序は対象に含めない。C++の `std::strong_ordering` とLeanの `Ordering` の差分テスト出力はそれぞれ `-1` / `0` / `1` に揃える。

`bool operator==(const C&) const = default` はスカラーの全フィールドの等値の連言になる（型引数には `[DecidableEq T]`）。これは分数としての同値ではなく、フィールドごとの等値である。継承、非スカラーフィールドのデフォルト比較、その他の明示的なデフォルトメンバーは対応するまで拒否する。比較とデフォルト等値の回帰テストは `tests/test_lean_model_friend.py` にある。

## 整数GCD・LCMの契約と費用

明示的な `std::gcd(a, b)` / `std::lcm(a, b)` は `Cpp.numericGcd` / `Cpp.numericLcm` へ翻訳する。[規格のGCD契約](https://eel.is/c++draft/numeric.ops.gcd)・[LCM契約](https://eel.is/c++draft/numeric.ops.lcm)、[cppreferenceのGCD](https://en.cppreference.com/w/cpp/numeric/gcd.html)・[LCM](https://en.cppreference.com/w/cpp/numeric/lcm.html)に従い、それぞれの引数の絶対値を先に取り、結果を共通の型へ変換する。例えば符号付き `-42` と符号なし `56` のGCDは14であり、先に負数を符号なしへ変換してはならない。両引数はbool以外の整数型、両絶対値と（LCMの場合）最小公倍数が共通の型の範囲内であることが前提になる。

`Cpp.NumericGcd` は絶対値と非負整数からの変換を明示する型クラスで、Int/UInt32/UInt64のインスタンスは純粋な定義を持つ。規格は両関数の時間上界を規定していないので、対数時間のSTL契約は仮定しない。呼出しには `[Cpp.NumericCost]` を要求し、与えられた `gcd` / `lcm` 費用関数の値をtickへ加える。この費用クラスに正本の既定インスタンスは置かない。部品の時間計算量を証明するときは費用の条件を明示するか、費用を証明できる明示的なアルゴリズムで置き換える。差分ハーネスだけは結果値の比較のため費用を1とする実行用インスタンスを置くが、時間計算量の根拠には使わない。

同名のユーザー関数を標準関数に置き換えない。標準数値関数の明示的なテンプレート引数は未対応として拒否する。`tests/test_lean_model_friend.py` で、ゼロ・負数・符号の混在・64bit境界と同名ユーザー関数の結果をC++/Leanで比較する。

スカラーだけのレコードの暗黙コピーと、一時レコードへの非constメンバー呼出しも扱う（例: `(C(a) += b)`）。同じ型のコピーをスカラー変換コンストラクタへ誤って渡さず、一時receiverの更新を元の値へ書き戻さない。暗黙のスカラー→レコード変換は、一意な非explicitの1引数コンストラクタに一致する場合に限る。ユーザー定義コピーコンストラクタや非スカラーフィールドの暗黙コピーは、この経路では未対応として拒否する。

構築子の本体では、初期化済みフィールドをreceiverとして非constメンバーを呼び出せる（例: `Ratio` の構築子から `normalize()`）。呼出し先の型クラス要求は、修飾されたクラス名（`Cpp.NumericGcd` / `Cpp.NumericCost` など）も保って呼出し元へ伝える。

差分ハーネスでオブジェクト番号を引数に渡す場合、C++では表の要素を参照で束縛し、実際の関数の値/参照引数宣言に従って呼ぶ。ハーネス独自のコピーでreceiverと引数の別名関係を消さない。`tests/test_lean_model_friend.py` の原本Ratio算術テストは自己除算も含む。ただしこの移行中のテストは入出力演算子を除いた算術部分を翻訳しており、原本クラス全体の翻訳・証明・公開の完了を示すものではない。

## ストリーム引数の状態変換

原本Ratioの入出力に必要な `std::istream&` / `std::ostream&` を、それぞれ `Cpp.IStream` / `Cpp.OStream` の状態へ翻訳する。`[Cpp.Streams]` は状態型を、`[Cpp.StreamRead T]` / `[Cpp.StreamWrite T]` は標準操作の実現を明示する。各操作は `Cpp.M` の純粋な状態変換であり、書式・ロケール・エラーフラグ・例外マスクなどを状態に持ち、その操作のコストと不帰還も表現できる。正本に書式を固定する既定の実現や費用インスタンスは置かない。

読取りは元の対象値も受け取る。これにより、失敗で値を保持する場合と変化させる場合を区別できる。各読取り後に対象フィールドとストリームの両方を更新し、連鎖した次の読取りへ渡す。出力は更新後のストリームへ次の挿入を行い、文字リテラル `'/'` を整数47の挿入と区別する。標準操作の契約は[算術型の抽出](https://eel.is/c++draft/istream.formatted.arithmetic)、[算術型の挿入](https://eel.is/c++draft/ostream.inserters.arithmetic)、[文字の挿入](https://eel.is/c++draft/ostream.inserters.character)に従う。利用する標準操作の実現がこれらの契約に対応することが信頼境界であり、標準I/Oの実装自体を証明したとは扱わない。

現在扱うストリーム式は、型引数Tの値/フィールドに対する読取り・書込みとnarrow文字リテラルの書込みである。具体的な `int` / `long` / `char` などのI/Oは、整数モデルが同じIntでも選ぶオーバーロードが異なるため、対応する型別の契約を用意するまで拒否する。多文字リテラルを文字1個の挿入へ置き換えない。ストリームをアルゴリズムのレコード内に格納する構文も未対応として拒否する。

`tests/test_ratio_stream_model.py` は入出力を除去せず、原本全体をnamespace/include/標準関数の明示修飾だけ変更して翻訳する。`tests/lean/ratio_stream_contract.lean` は任意の標準操作・状態・Tについて、抽出が2回の読取りとフィールド更新、挿入が分子の書込みと条件付きの区切り/分母の書込みに一致することを示す（入口の1tickと操作自身の費用・不帰還も保持）。原本の抽出は正規化しないので、その挙動を保存する。既定書式に対する具体的な実現をテスト側だけに用意し、通常入力、未完の入力、空入力、不正入力、EOF、戻り値と引数の状態をASan/UBSan付きC++と比較する。

汎用差分ハーネスはストリーム引数と参照戻り値にも対応する。入力ストリームはトークン数と、正規形の10進整数または不正入力を示す `x` で指定する。出力ストリームは引数トークンを消費せず、既定書式の空ストリームとして作る。入力の出力はEOF/failの2ビット、出力の出力は文字数と文字コード列になる。クラスの非const参照引数は `objref` と表示し、Lean側のオブジェクト表にも更新後の値を書き戻す。次の呼出しでその変更を検査できる。C++側はストリームの戻り値を参照で捕捉し、コピーを要求しない。

このテスト用の具体的な実現は、同じ幅の符号付き16/32/64bit整数（short/int/long/long longと対応する別名）に限る。shortの抽出は16bit境界で切り詰める。char/signed charの文字抽出をIntの数値抽出と取り違えたり、異なる幅を同じ抽出規則へ落としたりしない。未対応の具体化は明示的に拒否する。これは差分テストの実現の制限であり、C++候補のテンプレートや抽象ストリームモデルを特定型へ変更するものではない。EOF・不正入力・範囲超過による切詰めをC++と比較する。ストリームの標準操作自体に定数時間や無条件の停止は仮定しない。

差分検査の既定10進streamは、符号付き16/32/64 bitと符号なし32/64 bitを型ごとに実現する。符号なし入力は、絶対値がその幅の最大値以下なら符号を幅付きの値へ変換し、超えれば最大値へ飽和してfailbitを立てる。先行するfailbit・EOFと対象値の保持も扱う。これはcanonical decimal tokenまたは不正token `x` に限定した検査用の実現で、全書式・ロケールのparserを定義するものではない。同一driverでは幅と符号が揃った数値モデル、またはchar/signed charの文字モデルを許可する。異なる数値モデルや数値/文字モデルの混在は、別々の契約を具体化できないため拒否する。符号なし32/64 bitの境界・負号・overflowと、生の分数フィールドを `tests/test_ratio_stream_model.py` でC++/Lean照合する。

文字モデルは同じプロトコルのtoken表記を空白で結んで1文字ずつ読み、`bytes <個数> <0..255のbyteコード>...` でも入力できる。byteコードはcanonicalな10進表記を要求し、この経路は文字モデルだけで有効にする。検査用のC++ driverは8 bit byteと対象文字型のsignednessをstatic_assertで確認し、符号付き文字型では128以上のbyteを負の値へ解釈する。数値としての `24` と文字としての `'2'` / `'4'` を区別する。文字の抽出に成功して最後の文字を読んでも即座にEOFにはせず、次の抽出で入力切れを検出したときEOF/failを立てる。挿入は整数表記ではなく下位8 bitの文字を出力し、NUL・127・signed charの-1（255）のbyte値も検査する。0〜255の各byte、Cロケールの6種類の空白、NUL、負の分母、残余文字をC++/Leanで検査する。全てのbyte列や書式・ロケールを網羅したparserの証明ではない。

自由演算子のLean名には、同じヘッダ内に多重定義がなくても引数型のタグを付ける。例えばRatioの入出力は `cp.op_shr_istream_Ratio` / `cp.op_shl_ostream_Ratio` となる。別ヘッダの入出力演算子が同じ定数を定義することを避け、複数モデルを同時にimportできるようにする。

標準関数版のfrontend参照fixtureは `tests/fixtures/ratio_reference.hpp` に置き、公開実装は `library/number/ratio.hpp` とする。namespaceと標準名の修飾、既定型の等価なstd::int64_tへの表記変更以外は、修正済み原本と本体が一致することをテストする。単独include、既定型、汎用ハーネス経由の入出力を確認する。公開側は非公開Euclid helperを使い、対応証明は `Proofs/Cpp/Ratio.lean` に統合している。

## Ratioの数学層と生成関数の対応（移行途中）

`Proofs/Cpp/Lib/RatioMath.lean` は符号付き整数の正規化を純粋関数で定義し、分母が0でないときRatの正規分子・分母と一致すること、分母の正値性、互いに素性、値の保存を証明する。GCDでの除算が割り切れるので、C++の0方向への除算と整数除算が一致することも示す。増減と符号反転についても有理数の値を確認する。

`tests/lean/ratio_arithmetic_contract.lean` は候補から毎回生成したモデルへこれらの結果を接続する。正規化と2引数構築のIntモデル、単項マイナスのIntモデルについて結果と操作数を示す。1引数構築、前置/後置増減、単項プラスのデータ更新と操作数は型変数Tのまま証明する。GCDの費用は引き続き明示的パラメータであり、未規定の対数時間を仮定しない。LCMで共通分母を作る加減算についても、純粋モデルの値と生成された複合代入の結果・停止・費用を証明する。交差約分の乗除算・正分母の大小比較・正規化済み入力の等値・二項/左右スカラーラッパーも整数モデルへ接続した。正分母かつGCDが1という不変条件を構築・増減・四則演算が保つ条件も証明している。GCDとLCMによる整除ではtdiv/edivの一致を証明した。全型への数学的な対応、計算量オーダーと最終監査は未完了である。

小幅の符号なしテンプレート引数 `unsigned char` / `unsigned short`（`unsigned short int`を含む）の差分bindingは、数学整数Intを用いる。C++では演算時にintへ昇格するため、演算子ごとにUInt8/UInt16の折返しを適用しない。例えばunsigned charの128/1と1/2の比較では、途中の積256はintの値であり、0へ折り返してはいけない。入力と格納先を含む途中値の型範囲という部品の前提は維持する。この追加はテンプレートの具体bindingだけで、明示的なunsigned char/short宣言・幅を狭めるキャストの翻訳は、必要な変換意味論を備えるまで拒否する。

unsigned charのstreamは文字操作、unsigned shortのstreamは16bit符号なし数値操作に対応させる。文字のsignednessをdriverで保持し、unsigned charの128〜255は非負の値として抽出する。signed/unsigned文字モデルの混在も拒否し、C++側のstatic_assertで対象型のsignednessを照合する。

差分ハーネスの `calls` 引数で、検査対象の呼出し名を明示的に選べる。未指定なら従来どおり全呼出しを検査し、未知名や非公開関数の指定は拒否する。
この選択はC++ソースと全クラスの翻訳を変更せず、driverが具体化する入口を限定する。文字・符号なし型の算術検査では入出力を選ばず、その型のストリーム契約を数値の契約へ置換しない。
`tests/test_ratio_integral_models.py` はEuclid版Ratioの12二項/スカラー演算、複合代入の返値とreceiver、等値・比較をsigned char/char/short/int/long/long long/unsigned/unsigned long longについて照合する。
値が型の範囲に収まる正の小入力を用い、Fractionの期待値とASan/UBSan付きC++・Leanを比較する。文字型・符号なし型のストリームや全入力の型一般証明を示す検査ではない。

### レコードの返却と既定構築（Group移行用）

- 依存式の結果型がClangの汎用ASTでは未確定でも、翻訳器で求めた型が一意な非explicit・非可変参照の1引数構築に一致すれば、式を一度評価してから構築する。整数literalから型変数の構築引数への変換も、既存のZero/One/IntCastの規則に従う。レコードの波括弧返却は、引数個数で一意に選べる非explicitコンストラクタを呼び、単にフィールドを並べない。
- 新しく扱う委譲構築は、空body・引数なしの既定コンストラクタが、同じクラスの引数なしstatic factoryの結果を暗黙コピーする形に限定する（例: `GroupSum() : GroupSum(e()) {}`）。factoryの実行と失敗・仕事量を保ち、返されたスカラーフィールドを構築状態へ移す。任意の委譲、引数付きfactory、ユーザー定義copy/dtor、基底クラス、非スカラーの暗黙コピーは追加対応していない。
- 同じ引数型・参照形式・戻り型を持つhidden friendとnamespace関数templateが併存する場合は、生成名を `_hidden` / `_qualified` で区別し、両方の本体を翻訳する。C++差分driverは前者をADL、後者をnamespace修飾で呼ぶ。型tagだけが同じで実際の署名が異なるものや、他の同tagの曖昧なoverloadは拒否する。
- 回帰検査は `tests/test_lean_model_construction.py`。hidden/qualifiedで異なる本体、constructorが引数を変更する波括弧返却、factoryと変換引数の実行回数、明示構築・未対応委譲・copy/dtor/継承の拒否を確認する。公開Group本体の移行・群の法則の証明は別途行う。

差分driverでテンプレートの数値型をIntへ具体化するときは、Div/ModをそれぞれInt.tdiv/Int.tmodへ束縛する。Lean標準のEuclid除算では、例えば `-7 / 2` と `-7 % 2` がC++の `-3` と `-1` に一致しない。具体型を直接書いた非テンプレートの演算は従来どおりCpp.tdiv/tmodへ翻訳し、UInt32/64の束縛は変更しない。数学整数の証明で標準除算を用いる部品は、C++の切捨て除算と一致する条件（Ratioでは約数による正確な除算など）を保つ。Groupの整数逆演算では、体の逆元の法則と整数切捨ての仕様を区別する。
