# C++ 検証基盤

`scalar_ir.py` は新しい共通変換器の初期部分言語を実装します。名前・ハッシュによる専用モデルの選択を行わず、型付きのスカラー AST から IR と Lean 定義を生成します。[対応範囲、費用、信頼境界と未完了事項](../docs/scalar_converter.md) を参照してください。状態と基本ループの拡張は下記のとおりです。配列・一般の STL、2種類の floor_sum 以外のループを持つ部品の全入力証明と既存2部品の移行は未完了です。

`state_ir.py` は同じ式変換に分岐、参照のエイリアス、代入、早期 return、スコープを追加します。Clang の関数テンプレートの具体化も扱いますが、主テンプレートの一般の型条件の証明は未完了です。[状態変換器の記録](../docs/state_converter.md) を参照してください。

`while` と基本的な `for` の生成関数は `CppLoop` の明示的な実行枠を持つ評価器を使います。正常終了、検査失敗、枠不足を分け、枠の不足を停止証明には使いません。[停止条件と未対応構文](../docs/loop_converter.md) を参照してください。

`state_bridge.py --component NAME` は共通生成器を使う公開部品の登録ゲートです。ソースハッシュと公開宣言を照合し、`cp::` の全対象宣言を共通規則で変換して、登録モデルと生成 Lean の全文を比較します。登録項目 `translation = "state_ir"` と `lean_namespace` は評価器と出力先の設定であり、関数名やソースハッシュで手書きの意味モデルを選びません。公開対象は `safe_mod`、`floor_sum_unsigned`、`floor_sum` です。signed 版はメタデータの `signed_conversion` で対象コンパイラ契約を明示します。具体化だけのテンプレートは公開を拒否します。ソース変更後にハッシュだけ更新しても、生成対象の変更が登録モデルとの不一致として止まることを検査しています。

`scalar_assert.py` は標準 assert の宣言とマクロ展開を照合し、真・偽を実行するチェックへ変換します。独自マクロと同名の失敗関数は拒否します。[状態変換器](../docs/state_converter.md)を参照してください。

`scalar_stl.py` はスカラーの `std::swap` に対する標準操作の契約を確認します。呼び出し先のポインタの一致、固定ヘッダの具体化パターンと標準環境の本体 AST を確認し、同名関数や利用者の特殊化を拒否します。[契約と未完了事項](../docs/scalar_stl_contracts.md) を参照してください。

`clang_ast.py` は固定した Clang 22.1.4 と GCC 13.3.0 のヘッダで `cp::` の公開宣言を列挙し、TOML の宣言一覧とヘッダ全体の SHA-256 を照合します。

宣言一覧の対応種別は `FunctionDecl`、`TypeAliasDecl`、`CXXRecordDecl`、`EnumDecl`、`VarDecl` に限ります。`cp::` に別の宣言が現れた場合や同名の多重定義が現れた場合は公開判定を止め、bridge と意味対応のレビューを要します。


`floor_sum_unsigned` の元ソースと公開ヘッダから生成したモデルは同じ `Proofs/Generated/FloorSumUnsigned.lean` に一致します。公開登録にモデルと `Proofs/FloorSumCall.lean` を記録し、元ソースの全文照合も共有検査で続けます。[仕様と全入力証明](../docs/floor_sum_experiment.md)では結果、停止、状態評価の安全性、呼び出し側メモリ、時間と領域を扱います。signed 版も同じ共通経路で元ヘッダと公開ヘッダの3関数を全文照合し、数学的な総和・停止・安全性・費用と caller の保持を証明します。

`CppState` と `CppLoop` に値引数の内部呼び出しモデルを追加し、`CppInvokeProofs` と `tests/test_invoke_model.py` で状態保持・返却・費用・失敗・実行枠を検査します。同じ AST に定義がある値引数・スカラー返却値の直接呼び出しを生成し、`tests/test_scalar_call_ir.py` で C++ と比較します。関数ポインタ、再帰等は拒否します。参照引数の呼び出しは下記の拡張経路で扱います。while/for の条件内の直接呼び出しは反復ごとに評価し、最後の偽の判定での更新も保持します。[対応範囲](../docs/state_converter.md#値引数の関数呼び出しモデル) と [条件の変換](../docs/loop_converter.md#呼び出しを含むループ条件) を参照してください。

`state_ir.py --direct-file` は全翻訳単位を一度取得し、入力ファイルの関数を同じ AST の宣言 ID で取り出します。元 signed floor_sum の3関数から生成する実験モデルも全文照合します。signed 範囲外の変換は明示的な対象コンパイラの契約で追加し、`FloorSumSignedSpecification` で関数全体の全入力証明を公開登録しています。[入力ファイル選択](../docs/state_converter.md#同じ-ast-からの入力ファイル選択) を参照してください。

scalar_ir.py と state_ir.py の `--signed-conversion gcc13.3-lp64-twos-complement` は検査した対象での32/64 bit signed 変換を選択します。既定は checked のままです。`CppTargetCast` に復号の範囲・値保持の証明、`tests/test_target_cast_ir.py` に C++ 比較と算術の検査保持を登録します。

`template_ir.py` は未具体化の主テンプレートの構文・型パラメータ・未解決演算を保持する実験経路です。組み込み整数7種類の具体化は既存 state_ir の IR と照合し、生成した IntegralExtrema の具体化規則も Lean で照合します。IntegralExtremaExecution は7整数型の全組の比較・更新・呼び出し成功・メモリ保持・仕事量12以下・領域7以下を証明します。GCC 契約は全範囲、checked は選択した signed 変換の成功が条件です。[対応範囲と残作業](../docs/template_converter.md)を参照してください。主テンプレートの全入力証明・ユーザー定義型の演算契約と公開は未完了です。

`state_ir.py` の具体化済みの経路では、FunctionTemplateDecl の実際の FunctionDecl を通常関数と同じ宣言 ID で呼び出し解決へ登録します。テンプレート間・通常関数との値/参照呼び出し、ループを持つ具体化済み本体を生成します。`tests/test_template_call_ir.py` で元の chmin/chmax を含めて比較します。coverage は concrete_instances_only のままで、未具体化・明示的特殊化・非型引数・再帰等は拒否します。[具体化した内部呼び出し](../docs/template_converter.md#具体化したテンプレートの内部呼び出し)を参照してください。

`CppReferenceInvoke` は値・lvalue 参照を混在させた呼び出しのモデル基盤です。元メモリ内の参照先と権限を準備前に検査し、更新済み caller 範囲を保持して私有セルを破棄します。生成した呼び出し先の本体と C++ の比較、フレーム・費用・fuel の補題を追加しました。CppReferenceCommands と state_ir.py は、呼び出し元の参照 CallExpr を文・分岐・スコープ・ループ本体へ生成します。複合式・引数内の参照呼び出し、一時参照等は拒否します。[基盤と残作業](../docs/reference_invoke.md)を参照してください。


vector の読み書き・reserve・容量内追加の [共通モデル基盤](../docs/vector_contracts.md) を Proofs/CppVector.lean に追加した。現時点では C++ AST の自動変換へ未接続で、共通変換器は vector を引き続き拒否する。構築・寿命・iterator range・入れ子 vector・標準メソッドの実際の宣言の検査と、既存状態・制御への接続を追加する必要がある。

vector_bindings.py は標準宣言を検査した実際の AST の引数から型・const / writable の Parameter スキーマを生成する。型同一性のコンパイラプローブを通し、coverage は parameter_bindings_only。CppVectorBindings はこの型・所有者・権限を持つストア操作の基盤であり、C++ の文・式・ループの本体生成はまだ未接続。[対応範囲](../docs/vector_contracts.md)を参照する。


`vector_ir.lower_source` / `vector_ir.emit_lean` は、同一 AST の標準宣言・具体化検査と型同一性を確認した引数スキーマから、直線的な vector / scalar の関数本体を生成する。coverage は straight_line_scalar_return。size・添字読み取り・reserve・要素代入・容量内追加・scalar 局所変数 / 代入 / 返却を CppVectorProgram と混在引数へ接続する。スカラー式・cast・Lean 出力は既存 scalar_ir の拡張入口を共有する。初期範囲ではループ・分岐・局所 vector・入れ子・返却・保存済み要素参照・別関数呼び出しを拒否する。doubling の全体生成・証明は未完了。対象、費用、拒否、969照合・240 C++17 / UBSan 操作列と3ソース改変の検査範囲は [vector 契約](../docs/vector_contracts.md) を参照する。


vector_ir は局所の `std::vector<T>(n,value)` と const の同形の fill 構築、および lexical CompoundStmt の scope・破棄にも対応する。コンストラクタは同一 AST の標準クラスの型 / 一意な署名 / 具体化と、局所変数の型同一性プローブを確認する。default allocator だけを許し、使用する private helper・constructor・destructor の特殊化も拒否する。scope 内の return を伝播し、私有 vector は墓標として保持する。新規2検査の310照合 / 71 C++17 UBSan 呼び出しと7負例を含む詳細は vector 契約を参照する。default / count-only / range / copy / move / initializer_list 構築と入れ子・vector 返却・ループは未完了。


vector_ir の if / for / while / break と文としての scalar ++ / -- は CppVectorLoop へ生成する。制御を含む TU は coverage=control_flow_scalar_return で fuel 付き LoopProgram を出力し、primitive は既存の vector / scalar の文を共有する。反復 scope の破棄、break 時の for 更新の省略、early return を扱う。fuel 不足と fault を成功と区別し、停止には実際の成功の witness が必要。共通の成功単調性 / 一意性と8定理、852照合 / 242 C++17 UBSan 呼び出しの範囲は vector 契約を参照する。短絡論理、assert、continue / do、if / for 条件宣言、一般の関数呼び出し、入れ子 / vector 返却は未完了。


vector_ir の純粋な && / || は右辺の短絡を保持する logical 式へ生成する。標準 assert は scalar_assert の検査済み AST だけを check に変換し、偽の条件は fault として拒否する。無効化・偽マクロ・失敗 callee の影 / 再定義と効果を含む条件は拒否する。追加6定理と新規3検査の1,331照合 / 444 C++17 UBSan 呼び出し / 2 SIGABRT、モデル3改変とソース / マクロ等の負例を含む詳細は vector 契約を参照する。

vector 本体の範囲 assign は、検査済み begin/end の純粋な端点を同じ更新前の frame で捕捉し、型・所有者・世代・境界・宛先の権限 / limit を検査してから既存の範囲コピー契約へ接続する。標準 iterator の主定義と使用メンバーも同じ AST で照合する。`tests/test_vector_assign_ir.py` は全 / 空範囲、const / mutable のコピー元、端点の alias、局所 vector と破棄、C++ 実ソースの改変、不正範囲 / 権限 / 所有者、モデルの検査除去を扱う。iterator 算術・保存・逆 iterator、入れ子と全入力証明は未対応である。

`nested_ir.lower_source(..., construction_stages=True)` はクラス構成子のfield初期化子と本体を別のNProgramとして生成する。fieldは宣言順に局所として構築し、生成したfield名/slot一覧からrunFuel終了状態を参照する。unitのcallFuelによるscope破棄の前の処理であり、永続オブジェクトの構築・返却はまだモデル化していない。通常入口の既存モデルを変更しない。詳細はdocs/union_find_experiment.mdを参照する。


`context_class_ir.emit_context_class` は同じsource/classから既存class_copy_layoutの構成子/export/copy profileとcontext_method_irの全メソッド/receiver写像を一括出力し、両生成のsource digestを照合する。[対応構文・検査・未完了事項](../docs/context_class_converter.md)を参照する。公開registryはtranslation=context_class_irとqualified_classを指定して同じnested_bridgeで全文照合できる。実際の公開部品の切替は未完了である。
