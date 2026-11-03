# 参照引数の内部呼び出し基盤

`Proofs/CppReferenceInvoke.lean` は、値引数と lvalue 参照引数を混在させた内部呼び出しの準備・終了・実行を定義する。既存の CppState / CppLoop の関数本体を使う。値引数の既存 invoke、公開モデル、共通変換器の既存経路は変更しない。

`state_ir.py` は同じ AST にある通常関数の参照 CallExpr を呼び出し元から自動変換する。CppReferenceCommands が既存のスカラー文を再利用し、参照呼び出しを文・分岐・スコープ・ループ本体へ合成する。参照呼び出しを含まない関数は従来の StateProgram / LoopProgram を生成し、既存の公開モデルは変更しない。部品ごとの全入力の結果・停止・計算量の証明と公開は別に必要である。

## 引数と参照の検査

CallArgument.value は副作用を持たない既存の Expr、CallArgument.reference は呼び出し元の binding のスロットを指定する。参照は既存の binding から実アドレスへ解決する。任意のアドレスを引数として直接作らない。

参照先は**準備前の呼び出し元メモリ**に存在し、パラメータと同じ Ty を持ち、その型の有効な値でなければならない。新しい私有セルを追加してから参照を検査すると、不正な参照先が予約セルを指せるため、この順序を固定する。reference_address_bound は成功した参照のアドレスが元メモリの長さ未満となることを証明する。

可変参照は呼び出し元の writable binding だけから作れる。読み取り専用の参照は writable / readonly のどちらの binding からも作れる。値を参照へ、参照指定を値引数へ取り違えること、引数の過不足、存在しない binding、型不一致、無効値を拒否する。const 参照への一時オブジェクトの束縛や rvalue 参照は扱わない。

実際の C++ では、参照が初期化済みで寿命内のオブジェクトを指し、パラメータの C++ 型で合法にアクセスできることが必要である。幅が同じ long / long long をモデルの Ty が同じであるだけで不正な参照キャストへ利用しない。自動変換には Clang の束縛と型・修飾の照合も必要である。

## 準備と終了

引数は呼び出し元の状態で解決する。参照は同じセルへ束縛し、値引数は私有セルへコピーする。呼び出し元の binding 分の予約セルを追加して、呼び出し中も存続するフレームを追加領域に計上する。呼び出し先は自身の binding だけを持つ。同一セルに複数の参照を渡してよい。

終了時は呼び出し先メモリの元の caller 範囲を保持し、値コピー・局所セル・予約セルを破棄する。元の caller bindings と権限を復元し、返却値を1個の私有 readonly セルとして追加する。参照更新を元のメモリで上書きしない。返却値の欠落、未処理の break、無効な返却値、元の caller 範囲より短いメモリは拒否する。

run は既存の直線的な Stmt.run、runFuel は既存の CppLoop.runFuel で本体を実行する。後者の fuel は呼び出し先本体の観測枠であり、準備の検査を先に行う。fault と exhausted を区別する。任意の本体の停止を一律に仮定しない。

## 証明と費用

16補題で、読み取り専用・欠落・一時参照の拒否、参照の束縛、元メモリ内の参照先、引数の個数・仕事量、準備のメモリ範囲・binding 数・baseMemory・費用、終了時の caller bindings・更新済み範囲・長さ・baseMemory・費用、実行の合成、成功時の fuel 増加による結果の保持を証明する。

準備の仕事量は caller.work + 1 + 引数の nodes の合計 + パラメータ数。参照のアドレス取得は1、値の評価は既存 Expr.nodes、各 binding / コピーは1、開始と終了はそれぞれ1とする。終了時の仕事量は callee.work + 1。peak は既存 State.observe と同じ抽象セル・binding・式一時領域の単位であり、実測の CPU 時間やスタックバイト数ではない。

## 検査と残作業

`tests/test_reference_invoke.py` は6種類の C++ 呼び出し先から生成した本体を使い、符号付き / 符号なし64 bit、逆順の参照先、同一セル、値引数のコピー、局所セルの破棄、更新後の返却値を180呼び出しで Lean / 独立した期待値 / UBSan 付き C++ と照合する。readonly binding、dangling reference が予約セルを指すケース、型と値の不一致、引数の過不足、返却失敗、signed 演算の範囲超過を拒否する。参照を持つループと読み取り専用の呼び出しも C++ と照合し、fuel の不足・fault・成功・成功結果の保持を区別する。代入演算と返却値の2改変は元の結果の検査で拒否する。

```sh
python3 tests/test_reference_invoke.py
python3 tools/check_proof_security.py
```

複合式や引数内に入れ子になった参照呼び出し、一時参照、未具体化のテンプレートやユーザー定義型の呼び出し、各部品の全入力の結果・停止・費用・領域の証明は残作業である。ループ条件の式全体を占める呼び出しは [反復ごとの条件変換](loop_converter.md#呼び出しを含むループ条件) で追加した。Clang が具体化した型テンプレートの内部呼び出しは [具体化済みの経路](template_converter.md#具体化したテンプレートの内部呼び出し) で扱う。未対応の呼び出しを、これらの基盤のテストだけで検証済みとして登録しない。

## 呼び出し元 AST と制御の合成

CppReferenceCommands.Command は legacy Stmt、invoke、sequence、scope、branch、whileLoop を持つ。既存の式・代入・宣言・返却・値呼び出しの意味を再利用する。legacy の評価と fuel は従来と一致する。参照呼び出しの正常終了は return / break を呼び出し元へ伝播せず、返却値の readonly セルを残して次の文へ進む。scope は局所セルと binding を破棄し、外側の参照先の更新を保持する。while は break を自身で処理し、return は関数の外側へ伝播する。

7補題で legacy の一致、呼び出しの合成、成功時の fuel 増加による結果保持・成功結果の一意性、Program.callFuel の結果保持を証明する。新しい Program の call は直線的な評価用で、ループを含む場合は callFuel を使う。有限の fuel のテストを部品の全入力の停止証明にはしない。

変換器は実際の FunctionDecl の ID で呼び出し先を解決し、その parameters / resultType / body を生成する。参照引数は直接の DeclRefExpr に限り、括弧と const を付加する implicit NoOp を取り除く。writable と型を照合し、参照指定を生成する。変換・一時オブジェクト・明示的な参照キャストを直接の lvalue として扱わない。参照呼び出しを含む関数だけ新しい Program を生成する。値引数だけの関数が内部で自身の私有コピーを参照呼び出しへ渡す場合も、この経路で扱う。

現在、参照呼び出しは文の式全体（返却・初期化・代入の右辺・if 条件・捨てる呼び出し）に限る。外側の整数 cast は扱う。参照呼び出しを含む複合式や他の呼び出しの引数への入れ子は、C++17 の評価順序を一つに決めて生成せず拒否する。引数間の初期化は indeterminately sequenced であり、固定順序を一般に仮定できない（[C++17 N4659, expr.call](https://timsong-cpp.github.io/cppwp/n4659/expr.call)）。この拒否には合法だが未対応の式も含まれる。値引数だけの従来の純粋な呼び出しは従来どおり扱う。複合代入 x += f(x) は右辺が先に評価される規則に従い、参照呼び出し後の x を読み出す（[C++17 N4659, expr.ass](https://timsong-cpp.github.io/cppwp/n4659/expr.ass)）。

`tests/test_reference_call_ir.py` は呼び出し元を含む AST 全体からモデルを生成する。参照を持つ関数からの別の参照呼び出し、値コピーの中での更新、同一セルの参照、局所セル、分岐、ループ本体、break、複合代入を117呼び出しで Lean / 独立した期待値 / UBSan 付き C++ と照合する。実行枠不足、signed 範囲超過、成功時の fuel 増加、改名の不変性、ソース演算の改変と未対応の効果・一時参照の拒否を確認する。

```sh
python3 tests/test_reference_call_ir.py
```
