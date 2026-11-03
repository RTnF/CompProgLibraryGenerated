# 固定幅要素の vector 操作の共通基盤

`Proofs/CppVector.lean` は配列・vector の読み書き、reserve、容量内の emplace_back のための共通操作モデルである。この基盤から型付き binding、混在引数、式・文のモデルへ接続している。`verifier/vector_ir.py` は検査済み AST から直線的なスカラー返却の本体を生成する。既存 `state_ir.py` は引き続き vector を拒否する。局所 vector の fill 構築と scope は対応し、for / while / 分岐も対応し、その他の構築・入れ子・返却の生成は未完了であり、doubling 本体を証明済みとはしない。

Buffer は所有者ID、要素列、容量、上限、再割当世代を保持する。有効状態では長さ≤容量≤上限かつ全要素が受入述語を満たす。固定幅整数の場合は既存 Ty.valid を受入述語にする。抽象的な要素型は多相だが、以下の費用を任意のユーザー定義型・入れ子 vector の実際のコピーや破棄の費用へそのまま適用してはならない。その契約は未実装である。

ElementRef は所有者ID・世代・添字を保持する。読み書きは全てを検査する。負の添字、末尾以降、別の所有者、再割当後の参照、不正な値、readonly の書込みを拒否する。所有者IDを各オブジェクトの寿命ごとに一意に割り当て、破棄後も再利用しないことは、今後接続するオブジェクトストアの義務である。ElementRef は要素参照であり、end iterator やイテレータ一般を表現しない。

reserve は要求が容量以下なら内容・容量・世代を保持する。要求が容量を超える場合は内容と所有者を保持し、容量を要求値へ変更し、世代を1増やして古い参照を拒否する。上限超過と readonly を拒否する。固定した GCC 13.3.0 の libstdc++ の `bits/vector.tcc` の reserve は要求量を割り当てる実装であり、この容量の契約はその実装に対応する。C++ 標準一般の実装が常に同じ容量を選ぶとは主張しない。

容量内の appendReserved は末尾に受入値を1個追加し、容量・世代・所有者を保持する。既存要素への参照と値を保持する。容量不足は拒否し、自動拡張の emplace_back は未対応である。書込みは指定要素だけを置換し、他の要素と容量・世代・所有者を保持する。読み取りは状態を変更しない。

仕事量と領域は抽象単位で、検査の Lean 実装の計算量や実測時間ではない。有効性の全要素検査は証明モデルの前提確認で、C++ が毎回走査するという意味ではない。読み取り・書込みは仕事量1、容量内の追加は2。領域は vector オブジェクト・容量と1個の一時値として容量+2。reserve は容量不変なら仕事量1・領域容量+1、再割当なら仕事量長さ+1・領域旧容量+要求容量+2。後者は再割当の間に古い領域と新しい領域が同時に存在することを含める。caller 所有の領域を除外した関数全体の費用・最大領域への合成は別途必要である。

割当が成功すること、標準 allocator と固定幅要素の操作の意味は、このモデルの信頼前提である。bad_alloc / length_error の例外経路、入れ子型のコンストラクタ・破棄・移動、所有権ストア、参照の AST 解決、std::vector の明示的特殊化・独自 allocator・マクロ等の拒否ゲート、入れ子 vector、AST からの iterator range による assign の生成は未実装である。部品を公開する前にこれらの対応範囲と拒否を確定する。

`tests/test_cpp_vector.py` の2検査は510件の Lean 照合・60個の C++ 操作列と33件の拒否確認を含む。ライブラリのテンプレートを先に include し、固定した C++17 / libstdc++ と UBSan で、空入力、負値、int の両端、余剰容量、reserve の再割当・不変、容量内の自己要素の追加、読み書きと容量を照合する。不正な参照を C++ で逆参照して UB を起こすテストは行わず、モデルが拒否することを確認する。基盤の全入力証明は内容・有効性・既存参照の保持、再割当による参照拒否、単一要素の更新と他要素保持、仕事量・領域を扱う。

候補 doubling の実際の Clang AST では、vector の構築が CXXConstructExpr と allocator の CXXTemporaryObjectExpr、添字が CXXOperatorCallExpr、size / reserve / emplace_back / assign / begin / end が CXXMemberCallExpr と MemberExpr になる。自動変換の接続には、これらの宣言IDと標準ライブラリの実際の具体化・パターンを検査する必要がある。単なるメソッド名や型の文字列一致だけで標準契約を選ばない。再帰・iterator range・値コピー・返却を持つ部品（過去の merge_sort のような形）を扱うには、これらのモデルの追加が必要になる。

## 初期値付き構築と範囲 assign の基盤

`Proofs/CppVectorRange.lean` は固定幅要素の fill 構築と同じ要素型の別 vector からの半開範囲コピーを追加する。21定理で実行・有効性・範囲の長さと内容・所有者の保持・旧参照の拒否・費用を扱う。`IteratorRange` はコピー元の所有者ID・世代・開始と終了を保持し、end の位置を許す。負の端点、逆順、末尾超過、別所有者と古い世代、コピー先との alias、readonly とコピー先の上限超過は拒否する。std::vector の範囲 assign は自己コンテナの iterator を受け付けず、再割当の有無にかかわらずコピー先の全要素参照を無効化する。[標準草案の sequence requirements](https://eel.is/c++draft/sequence.reqmts#59) を確認した。C++17 の対象実装については固定 GCC 13.3.0 の `bits/vector.tcc` の forward iterator 用 `_M_assign_aux` を確認し、C++17 / UBSan の実行で照合した。

コピー元の reserve 再割当は保存済み IteratorRange の世代と一致しなくなり、assign で拒否されることも証明した。

コピー結果の容量は `max(旧容量,範囲長)`、世代は常に+1、内容は該当 slice になる。仕事量は範囲長+1。領域は再割当する場合、旧容量+範囲長+2、容量を再利用する場合、旧容量+2である。これは入力元を caller 所有として除外した固定幅要素の抽象費用で、関数全体では他の生存オブジェクトの領域と合成する必要がある。fill は n 個の同値要素、容量 n、世代0、仕事量 n+1、領域 n+2であり、要素値と n≤上限を検査する。空範囲・n=0も許す。[構築の標準草案](https://eel.is/c++draft/vector.cons#7) に記載された初期値の複製に対応する。所有者IDの新規性と割当成功は引き続きストア・allocator の接続に必要な条件である。

`tests/test_cpp_vector_ranges.py` の2検査で、415件の Lean 照合と169個の C++17 / UBSan 操作列、18件の拒否検査が成功した。全ての部分範囲、空の入力元・コピー先、縮小・拡大、余剰容量、int の両端、コピー元の内容と容量の保持を確認する。無効な参照と自己範囲コピーはモデルだけで拒否を検査し、C++ の未定義動作として実行しない。vector の AST 自動生成・オブジェクトストア・型と制御の合成、入れ子 vector や iterator 一般は未完了で、基盤だけで doubling 本体の証明済みとはしない。

fill の要素を Buffer にして同じ所有者を複製するだけでは、入れ子 vector の構築を表せない。doubling の外側 vector の各行には独立したオブジェクトの寿命と新規所有者IDが必要であり、単純な複製の契約とは別に生成・破棄を接続する。

固定 Clang の実際の std::vector<int> の dump で、ClassTemplateSpecializationDecl と size / reserve / operator[] 等の CXXMethodDecl に TemplateInstantiationPattern が付くことを確認した。後続の標準操作ゲートで、このパターンと元宣言を照合する。別の Clang 実行の宣言IDを直接比較してはならず、同一翻訳単位のID解決または検証済みの同一性プローブが必要である。std::vector<bool> は bits/stl_bvector.h の部分特殊化と proxy 参照を使うため、この固定幅要素の標準契約の対象外とする。

## 標準 vector 呼び出しの AST 同一性ゲート

`verifier/vector_stl.py` は1回の Clang 実行による完全な翻訳単位から、入力ファイルの関数と関連する std 宣言を取り出す。標準部分は root の JSON テキストを選別し、vector とそのヘッダ外定義の namespace だけを辞書化する。参照するメソッドのID、クラス具体化の TemplateInstantiationPattern、メソッドの TemplateInstantiationPattern を同じ実行の宣言へ照合する。別実行のID比較を行わない。標準クラスの主定義とヘッダ外の主メソッド定義は、独立した `<vector>` だけの pristine 環境の正規化 AST と比較する。使用済みフラグ・具体化済みの追加宣言を除き、本体の演算・定数・構造を保持して比較する。

size / reserve / operator[] / begin / end / assign / emplace_back / push_back の実際の std 宣言を対象とする。標準 allocator、組み込み整数の要素、またはその入れ子 vector のクラス同一性を検査する。std::vector<bool>・ユーザー定義要素・独自 allocator・標準クラス / メソッドの利用者特殊化・同名独自型・未対応メソッド・未検証マクロ呼び出しは拒否する。利用者が namespace std へ追加した宣言もこの初期ゲートでは拒否する。元の標準 assert を既存の assert ゲートで検証した場合に限り、引数へ直接記述された vector 操作の macro argument location を許す。

結果の coverage は `callee_identity_only` と明示し、検査済みの同じ AST の関数と呼び出しノードを返す。構築・引数評価・アクセス権・状態・費用の実行モデル生成は行わず、既存の state_ir の vector 拒否も維持する。これを doubling 本体の生成・証明済みとは扱わない。型の同一性を確認した入れ子 vector に固定幅要素の資源契約を直接適用してはならない。今後この AST を共通オブジェクトストア・型付き式と文の生成へ接続する。

`tests/test_vector_stl.py` は通常 / const と入れ子の呼び出し、改名、実際の doubling のメソッドと assert 条件の照合を確認する。同名独自型、標準クラス / メソッドの特殊化、proxy、独自 allocator、ユーザー定義要素、未対応メソッド、マクロ呼び出し、依存ヘッダからの特殊化、標準ヘッダの診断文字列をマクロで変えた主メソッド本体を拒否する。これは有限値の実行一致を主張する検査ではなく、C++ → IR の前段に必要な宣言・標準操作の同一性検査である。

## 所有者の寿命とオブジェクトストア

`Proofs/CppVectorStore.lean` は Buffer の構築、reserve、容量内追加、範囲 assign、要素の読み書き、破棄を共通 Store へ合成する。所有者IDはスロット添字で、構築は常に末尾へ追加する。破棄はスロットを none に変更し、長さを縮めない。古いスロットのIDを再利用せず、古い参照が別の寿命へ到達することを防ぐ。スロットと墓標は検証用の記録であり、C++ の実装がこれらを保持するという意味ではない。追加領域に墓標の数を計上しない。

31定理で、構築の新規ID・他オブジェクト保持・有効性、スロットの更新と他スロット保持、破棄と再構築後の参照拒否、存在しない所有者や所有者を変える更新の拒否を証明する。有効な Store の各生存 Buffer はスロットと同じ所有者IDを持ち、要素・容量の条件を満たす。更新は存在するスロットだけに行い、結果の所有者を変更できない。破棄したスロットへの更新も拒否する。

生存領域は各生存 vector の容量+1を合計し、仕事量を累積し、最大領域を更新する。初期 caller 所有領域は baseSpace として入口で実際の初期生存量から定める必要があり、恣意的に大きな値を設定してはならない。構築中の領域は既存生存量と構築の局所最大領域を加える。操作は既存生存量へ対象 vector の既存量を除いた局所最大領域を加え、基準量を除外する。更新の局所 peak は元と結果の容量+1以上であることを検査する。生存量の更新式と、更新後の生存量が記録した peak 以下になることも証明した。再割当の一時的な旧 / 新領域は既存の reserve / assign の局所契約から合成する。

readReference は状態を変更しない解決用の操作で、累積費用を扱う入口は Store.read。書込み権限は今後接続する C++ binding から writable 引数へ渡す必要があり、Store 自体は C++ binding を生成しない。現時点の Store は共通の要素型と受入述語を使う。異なるオブジェクト型、入れ子 vector の親子の所有権・破棄と返却、CppState のスカラーと評価順序、検査済み AST からの生成は未接続である。これだけで doubling 本体の証明済みとはしない。

`tests/test_cpp_vector_store.py` の2検査は676件の Lean 照合・72個の C++17 / UBSan 操作列と357件の寿命 / 拒否確認を含む。複数の構築・reserve・範囲 assign・破棄・再構築・読み書きの累積仕事量と peak を独立した集計と照合し、caller の初期生存領域を除く場合も確認する。C++17 / UBSan では同じ内容・容量・寿命の操作列を実行する。24回の構築 / 破棄を繰り返し、IDは増えても墓標のために生存領域と peak が増えないこと、全ての破棄済みIDへの参照が拒否されることを検査する。古い参照を C++ で逆参照することはしない。

## 型と権限を持つ vector binding

`Proofs/CppVectorBindings.lean` は Store の所有者ごとの要素型・最大書込み権限と、C++ の参照 binding の所有者・要素型・writable を分けて保持する。参照の解決時は実在する所有者、型一致、要素の型内の値、容量・長さ・max_size の条件、権限を検査する。同じ vector に const と mutable の参照を置ける。const binding から作った要素参照は readonly を保持し、後の書込みでは捕捉した権限と現在の binding 権限の両方を検査する。readonly オブジェクトに mutable binding を付けることも拒否する。17定理で解決と束縛・構築の実行、型や所有者の不一致・破棄済み所有者・権限昇格・readonly 書込み・タグ列の不整合の拒否、最大領域の観測を扱う。

型付きの構築・size・reserve・容量内追加・範囲 assign・読み書きをストアへ接続する。構築は型タグとストアのスロット数の一致を検査し、新しい所有者にタグと binding を追加する。assign はコピー元とコピー先の型と binding を解決し、range が解決したコピー元に属することを確認する。領域観測はストアの記録 peak に現在の binding 数と一時値を加え、以前の peak を保持する。これはスカラーの式評価・bindings とまだ合成しておらず、関数全体の C++ 時間・領域を証明したものではない。

対象の要素型は bool を除く32 / 64 bit組み込み整数。固定 libstdc++ / LP64 の max_size は PTRDIFF_MAX / sizeof(T) として32 bit要素では2305843009213693951、64 bit要素では1152921504606846975。Clang の実際の int / long / long long / size_t / ptrdiff_t の幅・サイズと CHAR_BIT を検査し、32 bit ABI を拒否する。6種類の整数 vector の C++17 / UBSan max_size と const / mutable alias の照合も行う。型タグはこの要素値の表現であり、C++ のクラスの同一性は前段の標準宣言ゲートと引数プローブで別途確認する。

`verifier/vector_bindings.py` は検査済みの同じ AST の ParmVarDecl から const の vector 参照とスカラーの値 / lvalue 参照の Parameter スキーマを生成する。vector 引数はコンパイラの `__is_same(decltype(引数), const ::std::vector<T>&)` 等で正規のグローバル std クラス・要素型・const 性と照合する。実際の翻訳単位に Clang VFS overlay で static_assert を挿入し、相対 include と呼出元の文脈を保持する。型同一性のキーワードや std / vector / 組み込み型をマクロへ置換した場合、マクロ由来の引数・本体、名前のない vector 引数、本体のない vector 引数を持つ関数宣言はこの初期プローブでは拒否する。単なる型の綴りで名前空間の別名にある独自型を標準 vector として登録しない。

coverage は parameter_bindings_only である。doubling 候補の実際のスキーマを `experiments/verification/array/doubling_bindings_ir.json` と `Proofs/Generated/DoublingBindings.lean` に保存し、再生成の全文一致と `Proofs/DoublingBindings.lean` の1定理で const vector<int> 参照・uint64 値引数の形を照合する。この定理は引数メタデータだけを対象とし、doubling の本体証明ではない。const の変更は生成スキーマへ反映され、元の形の照合が拒否される。

`tests/test_vector_bindings.py` の3検査は、実際の C++ 引数の生成・Lean での形の一致、改名不変性、const 改変の拒否、名前空間別名と型同一性キーワードのマクロ置換による偽装の拒否、37件の型・権限・所有者・古い参照・累積費用・構築 / 追加 / assign の実行確認を含む。vector の標準操作ゲートの既存3検査と、追加した非対応 ABI の1検査も通過した。

次に必要なのはスカラーと vector の binding の組合せ、引数の実際の束縛、評価順序、文・式・ループと scope の生成、入れ子 vector の型・親子の所有権・破棄・返却の接続である。現 state_ir は vector の本体を引き続き拒否し、新しい引数スキーマを関数本体の変換・証明済みとして扱わない。


## スカラーと vector の混在呼び出し

`Proofs/CppMixedInvoke.lean` は、生成された Parameter 列に沿ってスカラーと vector の引数を束縛する。宣言順の slot map と各種 binding 列を分け、引数の参照先は全て元の caller で解決してから値コピーや予約セルを割り当てる。新しく作ったセルを不正な caller binding から参照すること、型の不一致、const から mutable への権限昇格、引数種別と個数の不一致を拒否する。スカラー値の式には仮引数と一致する明示的な結果型を要求し、必要な C++ の変換は前段が cast 式として生成する必要がある。

スカラー値を返す finishScalar は更新された caller のメモリと vector を保持し、caller の binding を復元して readonly な返却値 binding を追加する。私有スカラーのコピーと予約セルを除去し、私有 vector のスロットを墓標へ変える。型タグとストアの長さを保持し、後続の構築でも破棄済み所有者IDを再利用しない。callee が caller の型タグ・セル型・vector 所有者や生存状態を変更した場合も拒否する。返却値を通じた vector 所有権の移転、入れ子 vector の親子所有権・破棄、例外による復帰は未対応である。

累積仕事量はスカラーとストアの和、合成 peak は各基盤が記録した peak の和を上界とする。引数の評価中には caller の vector binding も生存するため、その数を一時領域へ含める。関数内の予約セルは caller の両 binding 列の生存領域を保守的に計上する。私有 vector の破棄は固定幅整数要素の契約で生存オブジェクトごとに仕事量1を加える。ghost な型タグ・slot map・墓標を C++ の追加領域としては数えない。

`tests/test_mixed_invoke.py` は実際の doubling 引数スキーマを使用した入口、型・権限・個数の拒否、スカラー / vector の alias、値コピーの独立性、caller 更新の保持、返却値の範囲、私有セルの除去、墓標・古い参照・所有者IDの非再利用、累積仕事量と領域の43照合を行う。caller に10個の vector binding が残る式評価の領域も確認する。独立した C++17 / UBSan の参照・値引数・vector・局所 scope の実行と照合する。3件目の検査では元のモデルを再コンパイルした上で、引数評価時の caller vector binding の領域、私有 vector の墓標、返却値の範囲検査、const 権限検査をそれぞれ取り除く4改変を行い、既存の補題が拒否することを確認する。このテストは呼び出し基盤の確認であり、C++ 関数本体の AST 自動生成や doubling の全入力証明を完了したとは扱わない。


## 検査済み AST からの式・文の生成

`verifier/vector_ir.py` は `vector_stl.audit_vector_operations` が宣言ID・標準クラス・メソッドの具体化を検査した同じ AST と、型同一性プローブ済みの引数スキーマを使う。引数スキーマの処理は `bindings_from_audit` として共有し、異なる Clang プロセスのIDを突き合わせない。スカラーの式と Lean 出力は `scalar_ir.expression` / `lean_expression` の拡張入口を再利用し、定数・演算・cast の構文規則を複製しない。部品名やソースハッシュで規則を選ばない。

coverage は `straight_line_scalar_return`。vector 参照とスカラーの値 / lvalue 参照を持つ通常関数の、初期化付きスカラー局所変数、スカラー代入、size、添字読み取り、reserve、要素書込み、容量内 push_back / emplace_back、スカラー返却を扱う。型、読み書き権限、整数の範囲、添字と容量の前提は型付き runtime が検査する。要素型は bool を除く32 / 64 bit組み込み整数。signed narrowing は既存の checked 変換規則を使い、範囲外を拒否する。append は追加前に空き容量がある成功経路だけを扱い、自動拡張を伴う追加は拒否する。割当成功と固定 libstdc++ の契約を前提とする。

`Proofs/CppVectorProgram.lean` は宣言順の slot を各 binding 列へ解決し、型付きのスカラー / vector 式を読み取る。11定理は型の異なる slot の拒否、literal / variable / size / read の合成、課金時の内容保持と仕事量、return 後の停止、返却のない呼び出しの拒否を扱う。式の葉は読み取りだけなので、C++ の評価順が未規定な算術オペランドによる状態更新は扱わない。C++17 の要素代入では右辺を先に評価する。式ノード数で一時領域を保守的に観測し、vector の費用をストアへ、スカラー評価と対象参照の費用をスカラー状態へ加えて合成する。callee の返却後は混在引数の finishScalar で caller 更新を保持して私有セルを除去する。

分岐・ループ・break・assert、fill 以外の vector の局所構築やコピー・返却、要素への保存済み lvalue 参照、入れ子 vector、再帰・別の関数への呼び出し、効果を含む式、複合代入、一般のイテレータはこの初期生成器では拒否する。doubling 候補も全体生成を拒否する。これらは後続の拡張対象であり、対応済みの式・文だけから本体を手作業で組み立てて doubling の生成完了とは扱わない。

`tests/test_vector_ir.py` は実際の C++ 本体から生成したモデルを969件の Lean 照合・240個の C++17 / UBSan 操作列と比較する。小規模全列、符号付き整数境界、caller の参照更新、scalar / vector の混在順、size / read と演算の組合せ、返却と私有 scalar の除去、capacity・epoch、抽象仕事量・peak を独立した期待値で確認する。空入力、容量不足、上限超過、不正な値、範囲外添字、signed overflow の拒否も含む。改名不変性、3種類の実際の C++ 演算・添字・追加値の改変で元の期待結果が拒否されること、12個の未対応本体の拒否を確認した。これらは本体の自動生成と実行照合であり、生成した関数について全入力の結果・停止・時間 / 領域を証明し終えたとは扱わない。


## 局所 fill 構築と lexical scope

vector_ir は `std::vector<T> local(n,value)` と const の同形の局所宣言を追加した。CXXConstructExpr が直接のコンストラクタ宣言IDを出力しないため、同じ AST にある正規の標準クラスのコンストラクタ一覧で ctorType を一意に解決する。型・クラスの具体化パターンとコンストラクタのパターンを検査し、fill のシグネチャだけを受け付ける。使用された vector メンバーや private helper の特殊化も拒否する。基底クラスへの UsingShadowDecl の参照を vector の自身の宣言と取り違えない。

局所変数の宣言直後へ Clang VFS overlay の static_assert を挿入し、コンパイラの `__is_same(decltype(local), ::std::vector<T>)` 等で正規のクラス・要素型・const 性を確認する。型同一性のキーワード等がマクロ化された場合も拒否する。コンストラクタの allocator 引数は元の標準宣言から来た CXXDefaultArgExpr と正規の const std::allocator<T> に限定する。明示的な allocator、initializer_list、コピー・移動、count-only・default・range 構築は未対応である。const scalar 引数に束縛する組み込み整数の full-expression temporary は型を検査して純粋な値として評価する。

CppVectorProgram の construct は長さと値を評価し、sizeLimit、要素の型と割当成功の契約の下で新しい所有者・タグ・binding と宣言順 slot を追加する。固定幅要素の複製の仕事量 n+1と領域 n+2をストアへ加え、default allocator の生成・破棄と束縛を保守的に仕事量3へ含める。引数・allocator の一時領域も観測する。const オブジェクトは型タグの最大書込み権限と binding の両方を readonly にする。

CompoundStmt を scope として生成する。入口のメモリ・binding・slot・所有者の境界を保存し、leaveScope で caller に当たる外側の更新を保持し、局所 scalar と binding を除去し、局所 vector を墓標へ変更する。型タグと所有者スロットの長さは保持し、次の scope でも破棄済みIDを再利用しない。スカラー返却値は Step の値として保持するので、scope 内の return でも局所 vector を破棄してから外へ伝播する。破棄の費用は生存した固定幅 vector ごとに1、scope の復帰は1。追加3定理は不整合の拒否、外側 binding / slot の復元、所有者スロット数の保持を扱い、構築と scope の実行を合成する2定理も追加した。

新規2検査は310件の Lean 照合、71個の C++17 / UBSan 呼び出し、20個の連続した lexical scope で内容・返却・更新・墓標・タグ・仕事量・peak を確認する。空の構築、整数両端、const オブジェクト、scope 内の early return、length_error の対象となる上限超過、不正な値、空 vector の添字の拒否を含む。同じ大きさの局所 vector を20回構築・破棄しても、墓標の数で peak が増加しないことを確認した。コンストラクタ・private fill helper・デストラクタの特殊化、偽の標準型、__is_same のマクロ置換、initializer_list、明示的 allocator の7負例を拒否した。既存の本体969照合 / 240 C++ 呼び出し、型付き引数、標準メソッド、混在呼び出しの回帰も成功した。

この追加は局所 fill 構築と scope の生成・実行・共通補題であり、doubling の入れ子構築・返却、ループ、全入力の仕様・時間 / 領域証明を完了したとは扱わない。


## vector を扱う分岐・ループ・break

vector_ir は純粋な条件を持つ if、for、while、break と、文として使う scalar の ++ / -- を追加した。for の初期化の binding を外側 scope に置き、反復本体の scope を復帰してから更新を実行する。break や return があれば更新を飛ばし、break は最も内側の while が消費する。unbraced な分岐・反復でも宣言が外へ逃げないように scope を生成する。読み取る値にだけ依存する条件の評価を毎回行い、size や要素の読み取りも毎回課金する。

制御を含む翻訳単位の coverage は `control_flow_scalar_return` で、`Proofs/CppVectorLoop.lean` の LoopProgram を生成する。それ以外は従来の Program と straight_line_scalar_return を保持する。ループを含む新しい Command は、既存の vector / scalar の文を primitive として使い、sequence・scope・branch・while・break を合成する。scope は既存 leaveScope を使うため、各反復や break / early return でも局所 vector を破棄して墓標を残す。

runFuel と callFuel は CppLoop の Outcome を共有し、finished、fault、exhausted を区別する。fuel は観測上の上限であり、尽きた結果を証明の成功や非停止の証明として扱わない。Terminates は実際の成功を与える fuel と結果の存在を要求する。8定理で zero fuel / break、成功の fuel 単調性と一意性（runFuel / callFuel の両方）、while の return / break による終了を証明した。燃料の増加で結果・更新・仕事量・peak は変わらない。

新規2検査は全121列（長さ0〜4、値 -2 / 0 / 7）に対し、for の接頭部更新・break と while の探索・early return を独立した参照と比較する。852件の Lean 照合と242個の C++17 / UBSan 呼び出しで、caller 更新、反復ごとの墓標、内容保持、累積仕事量と peak、fuel 256 / 512 の一致、fuel 不足、signed overflow の fault、不正引数の拒否を確認する。意図的な停止しない形のモデルは exhausted を返すことだけを確認し、その C++ を実行したり非停止を証明したりはしない。実際の C++ の更新値・counter・break 条件の3改変は元の期待結果に拒否された。continue、do、for 条件宣言、if 初期化、短絡論理条件、goto の6未対応プロファイルも拒否した。

if constexpr、条件宣言・初期化、continue、do、一般の関数呼び出し、入れ子 vector と vector 返却はまだ未対応である。関数は末尾に明示的な scalar return を必要とする。具体例の fuel 実行と共通の制御補題を、生成した各関数の全入力の停止・結果・未定義動作不在・時間 / 領域証明の完了として扱わない。doubling 本体には入れ子・返却・assert・呼び出し等の後続接続が必要である。


## 短絡条件と検査済み assert

vector_ir は組み込み && / || を専用の logical 式へ生成する。左辺が && の偽、または || の真なら右辺を評価せず、そうでなければ右辺を評価して結果を0 / 1へ正規化する。要素の添字読み取り・除算を含む右辺でもこの順序を保持する。式は純粋な読み取りに限定し、代入・インクリメント・一般の呼び出しを条件に埋め込むことは引き続き拒否する。上界の領域観測には保守的に両辺のノード数を含めるが、評価しなかった右辺の仕事量や vector の読み取りを課金しない。

標準 assert は既存 scalar_assert のマクロ出所・成功枝・失敗 callee のシステム宣言の検査を共有し、同じ AST で verifiedScalarAssert となった条件だけを Stmt.check へ生成する。偽なら none / fault として成功した返却を与えず、真なら検査の仕事量1を加える。assert を前提条件の自己申告や証明上の仮定へ置き換えない。NDEBUG による無効化、独自の assert マクロ、__assert_fail の影や再定義、効果を含む条件は拒否する。vector 操作のマクロ由来の source location は、既存ゲートが確認した assert 引数内だけに許す。

追加6定理は && / || で右辺を飛ばす場合と実行する場合、偽の check の失敗と真の check の成功を扱う。新規3検査は1,331件の Lean 照合と444個の C++17 / UBSan 呼び出しで、長さ0〜4・値 -2 / 0 / 7 の全121列の短絡、while 条件、入れ子の assert、返却、読み取り回数・仕事量・peak を確認する。空 vector の添字や0除算を右辺に置いたガードも確認した。偽の assert の2経路は C++ が SIGABRT で停止し、UBSan のエラーを起こさないことを確認した。

ガードを弱めた実ソースが元の fault 期待値を満たさなくなること、偽のマクロ・失敗関数の影 / 再定義・無効化・副作用の6負例を拒否することを確認した。assert を弱めても後続の不正な添字が成功を阻むケースも確認し、各検査を独立して保持する。モデルで右辺を強制評価する2改変と check の偽を無視する1改変は既存の補題に拒否された。

assert と短絡の生成を追加しても、一般の関数呼び出し、入れ子 vector・返却、doubling 本体の全体生成・全入力の結果 / 停止 / 時間 / 領域証明は未完了である。

## 本体からの begin/end 範囲 assign

共通生成器は、固定幅整数 vector の `target.assign(first.begin(), last.end())` と begin/end の組合せを扱う。const / mutable のコピー元を許し、両端の要素型は宛先と同一である必要がある。別の引数 binding が同じコピー元を参照する場合も動的に所有者を解決する。整数式への iterator の置換や関数名ごとの dispatch は行わない。

同一 AST の標準 vector メソッドに加え、libstdc++ の `__normal_iterator` の主定義と使用されたメンバーの具体化を固定標準ヘッダーと照合する。実装名前空間へのユーザー宣言を拒否する。Clang が省略した根のファイル情報は直前の根のファイル情報を引き継ぎ、正規の iterator ヘッダーの根を解決する。

`Frame.iteratorRange` は更新前の同じ frame で両端を解決し、所有者・世代と半開区間の順序・境界を検査する。`Stmt.assignRange` は range を捕捉してから型付き `Frame.assign` / Store / Buffer へ接続する。コピー元を保持し、宛先の内容・容量・世代と work / peak を更新する。宛先は writable、コピー元と異なる所有者、範囲の長さは宛先の limit 以下である必要がある。自己 assign、不整合・破棄済み binding、異なる所有者の端点、非空の end→begin を拒否する。空の begin→begin / end→end と空 vector の end→begin は有効である。

3つの所有者式、2つの iterator 構築、1つの呼出しを固定仕事量6とし、宛先・端点・返却用の一時領域7をコピー前に観測する。コピー / 破棄 / 割当の仕事量と局所 peak は既存の範囲 assign 契約へ合成する。iterator のキャプチャと実行成功・範囲拒否の5補題を追加した。

現在は直接の begin/end の式に限る。保存された iterator、offset / 算術、逆 iterator、異なる要素型への変換、count / initializer_list assign、入れ子 vector は未対応であり拒否する。これは範囲 assign の本体生成と共通補題で、doubling の入れ子・返却・別関数呼出しや全入力証明の完了ではない。

最終確認では `tests/test_vector_assign_ir.py` の3検査が成功し、2,051件の Lean 照合、1,040 C++17 / UBSan 呼出し、2実ソース改変、4未対応 iterator / assign プロファイル、3特殊化、2モデル改変を扱った。費用はコピー元の長さ n に対してこの呼出し文脈では n+16、peak は宛先が拡張する場合 n+13、容量を保持する場合13を独立集計して照合した。別の caller / 入力文脈にこの定数をそのまま適用せず、共通 State / Frame / Store の契約から合成する。

## 入れ子の型と所有権の森林

`Proofs/CppVectorOwnership.lean` は既存ストアへ接続するための所有権メタデータを扱う。Element は固定幅整数または再帰的な vector 要素型。Tag は要素型、親、root の scope、子の ID 列を持つ。生存スロットと墓標を区別し、IDは論理的な allocation の所有者で、C++ のヘッダーの物理アドレスではない。

wellFormed は全生存タグについて、対応する整数型、子の重複禁止、双方向の親子の存在・型・scope、親 ID < 子 ID を検査する。整数 vector は子を持たず、子は独立した root scope を持たない。親子の番号の順序は、今後の構築で親のスロットを先に割り当てる不変条件である。循環・二重所有・孤立・型の不一致・破棄済み子等を拒否する。

rootOwner は親の ID の厳密減少で停止し、有効な森林では全生存ノードに root と scope が存在することを証明した。root の transfer は親子関係と全ノードの root を保持し、その root に属する context を移転先へ変える。有効な root と正しい元 scope / 型なら常に成功することと、有効性の保持を証明した。子だけの移転、異なる元 scope / 型、不正な森林は拒否する。

retired は全ノードを元の森林の context で分類してから同時に墓標へ変える。同じ scope の子孫も退役し、他の scope のスロットを保持し、スロット総数は変えない。retireScope は更新前後の wellFormed を検査する。成功時の有効性・スロット数保持に加え、`retired_wellFormed` と `retireScope_valid_input` により全有効入力で後検査が必ず成功することも証明済みである。raw の lookup / rootOwner / context / transferred / retired は検査補助で、単独で入力の有効性を保証する公開 C++ 操作ではない。

現在は34補題とメタデータの2検査がある。固定幅の単一 / 二重 / 三重 vector を含む17サイズについて482 Lean guards、返却 elision を通常 / 無効にした34 C++17 / ASan / UBSan 列、12不正森林、子孫の退役 / 元 scope 検査を除く2改変を確認する。ASan / UBSan を有効にし、この実行環境で使えない LeakSanitizer は既存公開検査と同様に無効化した。

この森林はまだ Buffer / Store の内容・容量・epoch、binding の const / writable、scope の実際の破棄・vector 返却、AST の入れ子構築 / indexing へ接続していない。ヘッダー移動と要素参照の寿命、親容量と子ヘッダーの重複のない領域測定も別に接続する必要がある。native 列は標準 vector の返却 / move で要素の内容・アドレスが保持される確認であり、森林と C++ の全体の意味対応や doubling 本体の証明ではない。


## 入れ子の内容と所有権ストア

`Proofs/CppNestedVectorStore.lean` は所有権森林を既存の `Store Value` / `Buffer Value` へ接続する。Value は固定幅整数または子 vector の論理 owner ID。整数 buffer は型の値域を検査し、入れ子 buffer の内容はタグの子 ID 列と順序も含めて完全一致しなければならない。森林とストアの長さ・生存状態、buffer.owner、長さ ≤ 容量 ≤ limit も検査する。森林の既存検査と合わせ、二重所有・孤立・循環・存在しない子・不一致の型を受理しない。

scope 退役は元の森林の context を使ってタグとバッファを同時に墓標へ変える。21補題で、有効入力からの退役成功と有効性保持、同 scope のバッファ削除、別 scope の内容・容量・epoch と参照の保持、削除した参照の失効、次の raw Store 割当でも墓標の ID を再使用しないことを示す。正しい型・元 scope の root 移転は成功し、内容を変えず有効性を保つ。これは論理所有者の移転で、C++ の root binding の寿命や move の費用をまだ表さない。

入れ子の抽象生存量は各生存 buffer の容量と root のヘッダーを数える。子のヘッダーは親容量に含まれるので二重に数えない。退役の生存量は増えず、更新した peak は退役後の生存量から基準量を引いた値を覆う。破棄の抽象仕事量は各退役 buffer の解放1と、入れ子 buffer の構築済み子ヘッダー訪問数を合計する。墓標、森林、owner 探索は証明用の帳簿で C++ の格納領域・実行費用には数えない。単位は抽象セルでバイト数ではない。limit と初期基準量は今後の ABI / binding adapter から正しく供給する必要がある。汎用 `Store.liveSpace` / `commit` の各 buffer ヘッダーを足す平坦な費用式を、そのまま入れ子の費用へ流用しない。

`tests/test_nested_vector_store.py` の2検査は9種類の行数 × 4種類の行長で834 Lean guards、通常 / elision 無効の72 C++17 / ASan / UBSan 返却・move ケース、14種類の不正内容を扱う。C++ の返却後の内容と内側 data アドレスの保持を比較する。容量・epoch・抽象費用の式は Lean モデルの検査であり、C++ のバイト単位の領域や実行時間の比較ではない。子 ID の順序・件数・存在、整数と子 ID の混同、owner 不一致、signed 値域、容量・limit、生存対応・リスト長の不一致を拒否する。内容と子 ID の照合を除く改変、バッファを退役させない改変は既存補題に拒否される。

この State は内容と森林の接続層である。既存 `CppVectorBindings.Frame` / `CppMixedInvoke.State` の Store Int、const / writable binding、nested indexing、構築・reserve・copy / move の同期、物理的な子ヘッダーの参照寿命、vector 返却、検査済み AST、doubling 本体への接続は未完了。raw buffer 更新だけで森林との整合性を保証しない。有限 native ケースと共通補題を doubling 本体の全入力証明として扱わない。

## 容量不足時の追加（2026-10-13）

`Proofs/CppVectorGrowth.lean` は容量内追加と再確保する追加の両方を扱う。既存の `appendReserved` は変更していない。対象は通常の固定幅整数 vector で、割当成功を仮定する。`accept` による全要素検査はモデルの有効性確認であり、C++ の走査費用ではない。

容量不足なら、新容量は `min(limit, max(1, 2 * size))`。固定 GCC 13.3 の `bits/stl_vector.h` の `_M_check_len(1)` と `bits/vector.tcc` の `_M_realloc_insert` を確認した容量方針であり、C++ 標準一般の方針とはしない。自然数モデルの倍算はオーバーフローしない。対象の整数 vector の `max_size` は `PTRDIFF_MAX / sizeof(T)` なので、この倍算が対象 C++ の `size_t` の範囲に収まることは型付き接続時の前提となる。

`append_spec` は有効入力での成功、末尾への追加、所有者・上限・値域の保存、容量内での epoch 保存と再確保での epoch 増加、局所 peak の `3 * 旧容量 + 3` 以下の上界を証明する。容量内の仕事量は2、再確保時は旧サイズ+3、局所 peak は旧容量+新容量+2。旧参照の失効は `grow_invalidates`。readonly、最大サイズ到達、不正値は拒否する。

償却証明のポテンシャルは、容量が上限に達していなければ `max(0, 2 * size - capacity)`、達していれば0。後者により、最後の拡張が倍増より小さくても `work + 新ポテンシャル ≤ 旧ポテンシャル + 5` が成り立つ。`appends_exist` は受理される追加列が上限以内なら全列の成功・最終内容・有効性を証明し、`appends_work` は総仕事量の上界を証明する。`empty_appends_linear` は初期が空なら、初期容量によらず k 回の追加が仕事量 `5k` 以下で成功することを示す。

`Proofs/CppVectorStoreGrowth.lean` は既存の `Store.commit` を使って接続する。`append_spec` はストア全体の有効性、更新対象・別所有者の内容、スロット数、累積仕事量、生存領域の差分、基準領域を除いた生存領域が記録 peak 以下になることを証明する。入れ子では親容量に子ヘッダーを数えるため、この平坦な `Store.liveSpace` をそのまま使用しない。

`tests/test_cpp_vector_growth.py` は3検査。140回の追加を固定 C++17 / UBSan と照合し、自己要素を引数にした再確保、既存参照の保持・失効、上限での切り詰め、不正入力を確認する。2所有者を交互に更新する60回のモデル列で累積仕事量・生存領域・peak も照合する。容量上限付近のケースは小さな論理上限を用いる Lean の確認であり、巨大割当の実測ではない。

この段階の残りは型付き binding、入れ子の行追加、AST の append、動的な生存領域を許す `FWM` への接続だった。下記の追記で整数の行追加と入れ子 AST の実行器へ接続した。ここまでの共通補題を `graph_list` や `tree` 本体の証明済みとして数えない。


## 入れ子の整数行の自動容量拡張（2026-10-13）

`Proofs/CppNestedGrowth.lean` の `Frame.appendGrowing` は入れ子の型・権限を解決し、`CppVectorGrowth.append` の結果を既存の `Frame.commit` で反映する。`CppNestedOps` の実際の `Frame.append` もこの処理を使うため、共通 AST 変換器 `nested_ir` の `g[i].emplace_back(x)` は事前 reserve がなくても実行できる。容量内の場合は以前と同じ結果・費用となることを `append_reserved_success`・`append_reserved` が証明し、既存の容量内追加の証明を維持する。

`append_ok` は有効な整数行・書込み許可・型の値域・追加後のサイズ上限の前提下で、成功、有効性・内容・owner・limit の保存、epoch の保持または増加、償却仕事量と局所 peak の上界を示す。`updated_space` は更新後の入れ子生存領域+旧容量=更新前の入れ子生存領域+新容量を証明し、`updated_peak` は更新後の生存領域から基準領域を除いた量が記録 peak 以下になることを示す。親の容量に入っている子ヘッダーは再計上しない。

`tests/test_nested_growth.py` は64回の行追加を C++17/UBSan と照合する。空の行、余剰容量、反復再確保、自己要素からの追加、旧整数参照の保持・失効、兄弟行の保持、const・型・上限の拒否、累積仕事量と入れ子生存領域・peak を確認する。専用 C++ ソースから `nested_ir` で生成した関数の呼出しと、実際の `NStmt.append` でも空の行への追加を確認する。既存 `test_nested_construct.py` の満杯行への追加は成功する期待へ更新した。

残りは、外側へ新しい行を追加する構成・所有権森林の更新、構造体の要素、変化する生存領域と容量を扱う `FWM` / `pstmtM` の費用証明。平坦な `vector_ir` 側の `appendReserved` は変更していない。グラフ・木の元のクラス全体を検証完了として扱わない。


## 外側への空の行の追加（2026-10-13）

`CppForestAppend` は親の子ID列へ新しいIDを追加し、末尾に子タグを生成する。IDは森林の旧スロット数であり、墓標を再利用しない。既存タグの型・親・scopeと既存の子を保つ関係 `Extends` を定義し、既存オブジェクトの有効性、rootOwnerとcontextの保存を証明した。`append_wellFormed` は新しい親・子を含む森林全体の有効性を証明する。

`CppAppendRow` の `State.appendRow` は、整数vectorのvectorに空の行を追加する。親のバッファは容量内追加または自動再確保を行い、森林とストアに同じ新IDを追加する。既存の行や別オブジェクトのバッファは変えない。`added_wellFormed` / `appendRow_runs` / `appendRow_valid` は、有効な入力・型・サイズ上限の前提下での成功と、任意の成功結果の有効性を証明する。追加1回の仕事量は親バッファの追加費用+1で、ポテンシャル付きの上界は6。

新しい空の行の容量は0で、そのヘッダーは親の容量に含む。`added_space` は追加後の生存領域+親の旧容量=追加前の生存領域+親の新容量を証明する。`added_peak` は追加後の生存領域から基準領域を除いた値が記録peak以下になることを証明する。

`Frame.appendRow` は書込み権限と型を解決し、所有権の最大権限リストを新スロット分だけ伸ばす。`NStmt.appendRow` と共通変換器 `nested_ir` により、実際の `g.emplace_back()` のASTからこの処理を生成する。`AppendRowStmt` は文の実行と、成功結果の状態の有効性を証明する。引数付きの行構築・行コピー、行の所有権移転はまだ拒否する。

`tests/test_append_row.py` は64回の外側追加を固定C++17/ASan/UBSanと照合する。空の親、余剰容量、自動拡張、別オブジェクトと墓標を挟んだ新ID、既存行の内容・整数参照の保持、再確保による行ヘッダー参照の失効、const・型・上限の拒否、仕事量・生存領域・peak、移転後のscope破棄を確認する。追加した行に整数を書き込む権限の継承も確認する。専用C++ソースを共通AST変換器へ通し、生成モデルの関数呼出しでも新しい空の行を確認する。上限付近は小さい論理上限を使うモデル検査で、巨大な割当の実測ではない。

残りは行コピー・fill・resize、構造体要素、FWMの可変容量・可変生存領域・可変行数。新しい行IDは常に親ID+行番号+1とは限らないため、既存の `RootGraph` の連続IDの前提も一般化が必要。元のグラフ・木のクラス全体はまだ検証完了ではない。


## 行IDと親の世代番号の一般化（2026-10-14）

`CppRowsGraph.Rows` は親タグ・親バッファの子ID列と現在のepochを明示し、森林全体の有効性を要求する。行IDが連続すること、親epochが0であること、容量が一定であることは要求しない。`of_legacy` で既存の `RootGraph` を埋め込める。`row_read` / `child_row` / `resolve_row` は実際のID列を使い、constとmutableの両方で所有者・型・最大権限・現在の世代番号を解決する。`appendRow_rows` は空行追加後に新しいIDと親epochでこの関係が保たれることを証明する。`updated_rows` は別バッファの更新後の有効性が分かれば、親の関係が保たれることを証明する。

`CppRowsStmt.eval_row` はこの関係を実際の `Container.row.eval` へ接続し、成功結果のbindingと `GoodF` による仕事量・一時領域の上界を証明する。`tests/test_rows_graph.py` は別オブジェクトと墓標を挟む追加を行い、複数回の再確保後と容量内の両方で一般定理を適用する。世代違い・所有者違い・範囲外・constへの書込みを拒否することも確認する。数値事実の証明はLeanカーネルによる `decide +kernel` を使う。

この一般化は新しい証明層であり、既存の `MultiVecN` / `FWM` はまだ連続IDと固定の行数・生存領域を使う。公開グラフクラスへの接続にはそれらの更新が残っている。


`CppRowsContents.Data` は可変長の行内容リストと実際の所有者IDを結ぶ。行数の一致と各行の整数内容を保持し、`appendRow_data` は外側への空行追加で新しい空行を末尾に足し、既存の全行の内容を保存する。`updated_data` は1行のバッファ更新で対応する論理行だけを置換する。別の位置が同じ所有者を指さないことは、森林の `tagOK` に含まれる子IDのNodupから導く。更新後の状態の有効性と更新バッファの内容は、具体的な更新操作の成功定理から受け取る。容量・行長を固定しない。


## 可変資源量を持つ行フレームと文評価（2026-10-14）

`CppRowsFrame.FWR` は1つの整数vectorのvectorについて、`Data`、根binding、最大権限リストと型・scope・権限を保持する。別の根や墓標、一時bindingを併存させてよい。`Resources` は現在の生存領域、累積仕事量、storage peak、オブジェクトスロット数、割当基準領域を表し、`Measured` が実際の状態と結ぶ。行数・容量・生存領域・スロット数は固定しない。

`appendRoot` は実際の `Frame.appendRow` の成功と新しい空行の内容関係を証明する。`afterRoot` では生存領域を旧値+新容量−旧容量、仕事量を旧値+親追加費用+1、スロット数を旧値+1へ更新する。`afterRow` は内側のバッファ更新について生存領域・仕事量・peakを更新し、スロット数と基準領域を保つ。両者のpeakは、既存peakと、既存生存領域+一時追加領域−基準領域との最大値である。子のヘッダーを二重計上しない。`updateRow` は具体的な更新結果の有効性と内容を前提にフレームを保存する。`appendBound` / `appendChild` はこれを自動拡張する整数appendへ接続し、ポテンシャル付き仕事量の上界5と一時領域の上界3×旧容量+3も証明する。

`CppRowsSteps.appendRoot_stmt` / `appendChild_stmt` は、実際の `NStmt.run` の成功と、式の終了で一時bindingを解放した後の `FWR` を証明する。内側appendの添字と値はスカラー式である。根追加のスカラー仕事量は2、内側追加のスカラー仕事量は添字のノード数+値のノード数+3以下。保存された論理内容と資源量を、続く文の前提にそのまま使える。

`MultiVecDynamicRows.dynamic_rows` は既存の `MultiVecN.FWM` から任意の入れ子パラメータを取り出し、対応する `FWR` と初期の資源量を導く。この後はFWR側で可変の行数・資源量を扱える。ただし、既存の複数ベクトル全体の `pstmtM` / `pexecM` はまだ固定フレームを使う。全パラメータの別名関係を保つ動的実行器、構築・resize・行コピー、構造体要素への接続は残る。

`tests/test_rows_steps.py` は、空行追加と新しい行への整数appendの文評価証明を合成し、実際の成功結果に対するFWRを導く。別の根と墓標を含む初期状態を使い、一時bindingの解放とpeakの上界を確認する。C++ソースの外側append・新しい行へのappend・既存行へのappendを共通AST変換器へ通し、12回の関数呼出しを固定C++17/ASan/UBSanと照合する。行内容・親と既存行の容量、別の根の内容、墓標、スロット数、有効性、peakを確認する。


## 複数パラメータと別名参照を含む動的フレーム（2026-10-14）

`CppRootModel.View` は平坦な整数ベクトルまたは整数ベクトルのベクトルの論理内容を表す。`Models` が実際の状態と結び、`Heap` は根の所有者IDから論理内容への写像である。同じ根を指す複数の引数はこの1つの内容を共有する。`put` はその根だけを更新するため、可変参照とconst参照の別名にも同じ更新を反映する。パラメータ全件の根IDを異なると仮定しない。

`append_other` は外側への空行追加で他の根の内容を保存することを証明する。`updated_other` は1行のバッファ更新で別の根とその全行の内容を保存することを証明する。変更する子は親タグがsomeで、根のタグは親がnoneである。異なる根の子が同じIDなら両タグの親が一致して矛盾する。このタグの比較により必要な分離を導き、IDが連続するという前提を置かない。`append_frame_effect` は成功した実際の `Frame.appendRow` からこの保存則とbinding・権限リストの更新を導く。

`MultiVecDynamic.Family` は任意の個数の平坦・入れ子パラメータのbinding、要素型・scope・権限、所有者で共有するHeap、実際の資源量をまとめる。`row_frame` は任意の入れ子パラメータをFWRとして取り出す。`changed` / `appendRoot` / `updateChild` / `appendBound` は1根への変更後も全パラメータの内容関係を保存する。追跡対象外の根や墓標を併存させてもよい。行数・容量・生存領域・storage仕事量・peak・スロット数は動的な値である。

`MultiVecDynamicSteps.appendRoot_stmt` / `appendChild_stmt` は共通ASTモデルの実際の文評価へ接続する。式の一時参照を解放した後も、全パラメータのFamilyを保持する。内側appendの添字と値はスカラー式で、スカラー仕事量はノード数の合計+3以下、バッファ仕事量はポテンシャル付き上界5である。外側appendのスカラー仕事量は2である。

`tests/test_multivec_dynamic.py` は、2個の入れ子の根と1個の平坦な根について、各根を指すmutable/constの6パラメータを用意する。外側appendと新行へのappendの文証明を合成し、もう一方の根への更新にも全体の保存定理を適用する。非連続行ID、墓標、0でない親と行のepochを含む。別名constから新しい行を読める一方で書込みを拒否することを確認する。C++関数へ同じ根をmutable/constで渡し、別の根も変更する5回の呼出しを、固定C++17/ASan/UBSanと生成モデルで照合する。

ここまでの接続は個々のappend文とその合成である。既存 `pstmtM` / `pexecM` の置換、Familyを使う純粋な条件分岐・ループ・関数呼出しの実行器、行コピー・resize・構造体要素はまだ残る。公開グラフクラス全体の検証完了とはしない。


## 内容の投影と動的な制御構造の証明（2026-10-14）

`DynamicContents.Contents` / `erase` / `eraseHeap` は行ID・epoch・容量・資源カウンタを除き、型・scopeと論理内容を残す。純粋な `appendRoot` / `appendChild` は所有者で共有する内容だけを更新する。後者は添字・型・値の範囲を検査する。`erase_put` / `appendRoot_erased` / `appendChild_erased` は実行側のHeap更新がこの内容更新と一致することを証明する。内容の意味論だけではC++の最大サイズや割当成功を保証しない。実際の文との接続では、既存のFamily操作の有効性・サイズ上限内という前提も必要である。

`MultiVecDynamicHoare.Runs` は、共通の `Command.runFuel` が有限の燃料で成功し、終状態にFamilyと任意の後条件を満たすHeap・資源量が存在することを表す。既存の燃料単調性を使って、primitive・sequence・branch・whileの規則を証明した。`scalar_condition` はスカラー条件の評価と式終了による参照解放がFamilyを変えないこと、および条件のノード数+1以下のスカラー仕事量を証明する。

`whileGhost` は継続のたびに自然数のghost指標を減らす。行数・容量・オブジェクト数・資源量は不変条件の中で変えてよい。`whileGhostStop` はreturnとbreakも扱い、継続する場合だけ指標の減少を要求する。returnでは元の戻り値を伝え、breakではそのループのbreakingフラグを消す。`Runs`の後条件へ資源量の上界を含められるが、任意のプログラムの計算量を自動で導くものではない。

`MultiVecDynamicScope` は同じ森林・バッファを持つ状態間でModelsを保存し、スコープ終了によるpeakの観測を`observed`へ反映する。`scope_scalar`は戻り値がvectorでなく、そのスコープに属するオブジェクトがなく、外側のスカラー型・パラメータbindingを復元できる前提で、実際の `NState.leave` とFamily保存を証明する。ローカルvectorの破棄・戻り値vectorの移転はこの規則の対象外で、別の接続が必要である。

`tests/test_dynamic_control.py` は行追加・条件分岐・スカラー代入・scopeを持つループへghost不変条件と停止規則を適用する。3反復で4行を追加する例について、再確保後の全パラメータのFamily、有限燃料での成功と最終資源量の上界を確認する。別名constと平坦ベクトルも保持する。branch規則と、ghost指標0の時点でbreakまたはreturnする規則を別途適用する。型・添字・値の不適合を純粋内容意味論が拒否することも確認する。C++ソースを共通変換器へ通し、0/1/3/8反復の関数呼出しの結果・行数・既存binding・有効性を生成モデルと固定C++17/ASan/UBSanで照合する。3反復の資源量上界はその具体例の検査であり、一般のループの計算量証明ではない。

まだ `pstmtM` / `pexecM` 相当の全命令を含む純粋実行器や、一般のFamily初期化・関数呼出しの抽象化は揃っていない。行コピー・resize・構造体要素、ローカルvectorを所有するscopeも残る。元のグラフクラス全体の検証完了とはしない。


## 純粋な式評価と動的な読み出し（2026-10-14）

`DynamicExpr.Locals` はスカラーのmemory/bindingsと変数slotを保持する。`snapshot_env` はその純粋な環境が実際のNStateの環境と一致することを証明する。`select` / `denote` はFamilyのパラメータとContentsHeapだけを使い、スカラー式、型変換、単項/二項演算、除算・剰余、短絡論理演算、平坦/入れ子のsize/readを計算する。負の添字・範囲外・型不一致を拒否する。これらの関数の再帰はLeanで停止検査される。

`DynamicRealizes.Realizes` はLocalsとContentsHeapを実際の状態へ結ぶ。行ID・epoch・容量・資源量は存在するFamilyの中に置き、論理状態には持たない。スカラー式のdenote一致と、Evで証明した式の評価後に一時参照を解放してもRealizesが保たれることを証明する。式の仕事量上界wに対して式終了後の総仕事量は旧値+w+1以下で、scalar peakとstorage peakからの追加領域上界も引き継ぐ。

`DynamicRowsRead` は任意の行IDと親epoch・const/mutable権限で、行参照の評価、行size/read、外側sizeを実際のNExpr.evalへ接続する。既存NestedReadOnlyの連続ID前提を新しい補題では使わない。`DynamicSizeSound` / `DynamicReadSound` はContentsHeapのlookupから具体的なID・epoch・bufferを取り出し、純粋評価と実際の評価の一致、仕事量/一時領域の上界、評価後のRealizes保存を証明する。入れ子readの添字と位置はこの接続定理ではスカラー式である。結果の整数の型範囲は入力状態の有効性から導く。

sizeはC++のsize_tの範囲に入ることを前提とする。根sizeの仕事量/一時領域上界は3/3、行sizeは添字ノード数+3/+4、行readは添字と位置のノード数の和+3/+4。これらは式評価中の上界であり、終了時のchargeはRealizesの保存補題で加える。

`tests/test_dynamic_expr.py` は別の根と墓標を挟んで外側を3回追加し、非連続の新しい行に整数を追加する。親epoch2・行epoch2の状態でconstの別名を使い、根size・行size・行readの純粋/実行一致定理を適用する。型変換・算術・除算/剰余・短絡論理演算・size/readを組み合わせた16式について、純粋評価と実行モデルを照合する。型不一致、負/範囲外添字、ゼロ除算、符号付きオーバーフローの拒否も含む。C++から生成したinspect関数について3個の有効入力を固定C++17/ASan/UBSanと比較し、3個の不正添字は実行モデルの拒否だけを確認する。

全式構造についての帰納的な純粋評価の健全性定理、平坦な根のlookupからの同様の接続、スカラー文とappendを含む純粋実行器、一般Family初期化・関数呼出し、ローカルvectorのscope、行コピー・resize・構造体要素はまだ残る。実行可能な純粋評価器を用意したことと、その全構文の健全性証明を完了したことは区別する。


## 複合式の帰納的な証明と証明書の構築（2026-10-14）

`DynamicExprCompose` は、評価中に参照用のbindingが末尾へ追加されてもRealizesが保たれることを証明する。式終了前の状態を次の部分式の前提に使える。targetCast/unary/divremと、短絡する/右辺も評価するlogicalの実行補題も用意した。cast/binaryは既存のEv補題を使う。`DynamicExprLaws` は全スカラー演算子について純粋評価を部分式の評価へ分解する。両部分式がscalarOnlyの場合に元のscalar評価へ切り替える経路も同じ式になることを証明する。

`DynamicFlatSound` は平坦な根のsize/readを論理lookupから取り出し、純粋評価・実際の評価・Realizes保存を結ぶ。結果の整数の型範囲は入力状態から導く。sizeはsize_t範囲内、readの添字はスカラー式の前提を持つ。`DynamicExprAtoms` は平坦/入れ子のsize/readについて、論理lookupと添字・範囲の条件だけから原子的な評価証明を作る。

`DynamicExprCertified.Evaluation` はスカラー式、原子的な読み出し、cast/targetCast/unary/binary/divrem/logicalの証明を合成する帰納的な関係である。`sound` はその構造帰納法により、Realizesを満たすすべての実行状態について純粋評価と実行の一致、有限の評価成功、仕事量・一時領域の上界を証明する。評価中の上界はいずれも式ノード数の2倍。`released` は式終了後のRealizes保存、総仕事量が旧値+2×ノード数+1以下、scalar/storage peakからの上界を導く。短絡する場合は右辺の評価証明を必要としない。

`DynamicExprDerive.Ready` は原子的なlookupの証明がどこで使えるかを記録する。`derive` はReadyと純粋評価の成功からEvaluationを構築し、スカラー合成の中間値や型変換の証明を利用者が手で指定する必要をなくす。純粋評価が失敗する部分式も、短絡して評価しない経路に置ける。Readyの原子的な証明の前提を省略して、任意のNExprの健全性を主張するものではない。

`tests/test_dynamic_certified.py` は再確保後のconst別名を持つ共通fixtureで、5種類のsize/readの原子的な証明を作る。型変換、targetCast、単項/二項、除算/剰余、短絡論理演算のすべてを合成し、右辺に実行不能な参照を置いた短絡経路も検査する。中間値を指定せずReadyから合成式の証明を導く経路と、ゼロ除算に対するEvaluationが成立しないことも確認する。費用とRealizesの後条件は具体的なfixtureの状態だけでなく、同じ論理内容を実現する任意の状態について定理を適用する。C++との照合は共通fixtureを使うtest_dynamic_expr.pyのinspect関数を継続して使う。

残りは原子的な読み出しの一般添字・一般位置を構造帰納へ接続すること、全構文でReadyを導くこと、スカラー文/appendを含む純粋な文・制御構造の実行器、Family初期化・関数呼出し、所有vectorのscope、行コピー・resize・構造体要素である。公開グラフクラス全体の検証完了とはしない。


## 純粋な文評価と複合式を使うappend（2026-10-14）

`DynamicStmt.State` はLocalsとContentsHeapを持つ。`run` はskip、スカラーdeclare/assign/ret/check、外側への空行append、内側への整数appendを純粋に計算する。未対応の文ではnoneを返すが、それだけで実際のC++が失敗するとは主張しない。容量・epoch・割当上限はこの純粋状態に含めない。

`DynamicScalarSteps` は宣言・代入後のLocalsと実際のスカラー状態を結ぶ。`DynamicScalarSound.sound` は式のReadyと純粋な文評価の成功から、実際のNStmt.runの成功、戻り値の一致、更新後のRealizesを証明する。仕事量は式ノード数の2倍+1以下。一時スカラー領域は宣言では2×ノード数+2、それ以外では2×ノード数を上界とし、既存のscalar/storage peakと合成する。

`DynamicAppendSound.appendRoot` は論理lookupと変更対象の実バッファのroomから、外側appendの純粋/実行一致とRealizes保存を導く。事前reserveは要求しない。仕事量はバッファ追加の費用+3である。`DynamicAppendValue.appendChild` は行添字がscalarOnlyで、追加する値がReadyを持つ任意の複合式の場合を扱う。値の式は変更対象をconst別名で読むこともでき、その評価中に追加された一時bindingをappend後にすべて解放する。対象行のRoomAtだけを要求し、無関係なバッファのroomを要求しない。非連続の行IDと任意の親epochを許す。

内側appendの総仕事量と更新後ポテンシャルの和は、旧仕事量+添字ノード数+2×値ノード数+8+旧ポテンシャル以下。peakは旧peakと、旧scalar peak・liveS+添字ノード数+2×値ノード数+4・更新後storage peakから評価する。バッファの自動拡張の償却上界5をこの式へ組み込んでいる。低層のappendChild_stmtでは旧バッファのlookupと更新後Familyを明示する。高層appendChildの費用結果は旧バッファと更新結果を存在量化しているため、複数回のポテンシャルを合成するには低層定理の対応関係を使う必要がある。純粋内容の成功だけから割当成功を導く定理ではない。

`tests/test_dynamic_stmt.py` は再確保後の非連続行IDを持つ共通fixtureで、ベクトルを読む宣言・代入・check・returnを連結し、各状態へ一般の健全性定理を適用する。constへの代入・型不一致・偽のcheckの拒否も確認する。const別名のsize/readを複合した値による容量不足の行appendと、外側の空行追加についても一致定理を適用する。C++から生成した3関数を固定C++17/ASan/UBSanと照合し、戻り値、内容、容量、既存binding、別オブジェクトの保存を確認する。

残るのは純粋な制御構造の実行器への接続、全読出しでReadyを導く一般添字・位置の証明、Family初期化・関数呼出し、所有vectorのscope、行コピー・resize・構造体要素である。元のグラフ・木クラス全体の検証は引き続き未完了である。


## 純粋な制御構造と対応する実行の合成（2026-10-14）

`DynamicControl.runFuel` はDynamicStmtの純粋状態を使い、primitive/sequence/branch/whileLoop/scope/breakLoopを実行する。returnとbreakで後続を短絡し、ループ自身のbreakは消費する。スコープ終了では外側セルの更新とContentsHeapを保存し、新たなスカラー局所変数だけを取り除く。外側のメモリ長と型列も検査する。燃料切れはexhausted、未対応のinvokeScalarはfaultとなるが、未対応の結果をC++の失敗とみなさない。所有vectorを生成する局所文はDynamicStmtの未対応ケースのままである。

`success_mono` は成功後に燃料を増やしても同じ結果になることを証明し、`success_unique` は異なる燃料で得た成功結果の一意性を導く。`DynamicControlHoare.Runs` は有限燃料での成功と後条件を持ち、文・連結・分岐・スコープ・whileGhostStopの規則を用意する。whileGhostStopは継続する反復だけで自然数のghost指標の減少を要求する。return/breakで直ちに終了する経路は指標0でも許す。純粋なrunFuelの再帰自体の停止と、対象ループがexhaustedにならず成功することの証明を区別する。

`DynamicControlBridge.Runs` は純粋な成功と実際のCommandの成功を、最終Realizes・スカラー戻り値・breakの一致で結ぶ。任意の対の後条件を保持するため、実際のバッファlookupやポテンシャル、仕事量・peakの情報を次の文へ渡せる。primitive規則には既存のappend一致定理を渡せる。scalar規則はScalarReadyと純粋runから実際の実行と資源上界を自動で作る。sequence/branch/scope/whileGhostStopを合成でき、branchとwhileの条件はReadyを持つ複合式でよい。条件評価中の一時参照は解放し、その後のRealizesを継続へ渡す。scope規則では純粋leaveと実際のleaveの成功・復元後の一致を明示的に要求する。所有vectorの破棄を自動で証明する規則ではない。

`Runs.aligned` は両側の成功燃料を一つの共通燃料へ増やせることを証明する。ループ規則は両側の状態にまたがる不変条件を使い、継続経路でのみghostを減らし、return/breakを両側で同じように処理する。一般のループについて一律の時間上界を主張せず、資源量を含む不変条件・後条件から別途証明する。

`tests/test_dynamic_control_pure.py` は3回のカウンタ減少について純粋な停止規則と、同じ論理状態を実現する任意の実状態に対する対応規則を適用する。ghost0でのbreak/return、実行不能な後続checkの短絡、branchと成功燃料の整列も確認する。共通ASTが生成した3関数のループ（内側・外側append、局所スカラーのscope、別名const読出し）、break、早期returnを、純粋実行器・実際の実行モデル・固定C++17/ASan/UBSanで照合する。燃料0、非停止ループのexhausted、偽checkのfaultも検査する。具体的な3反復の照合から任意回数のグラフ構築の正しさや計算量を主張しない。

残るのは全読出しの一般添字・位置からのReady構築、appendの割当可能性とscopeの復元条件を論理不変条件から自動で取り出す接続、Family初期化/関数呼出し、局所所有vector、行コピー/resize/構造体要素である。公開グラフ・木クラス全体の検証は未完了である。


## ベクトル読出しを含む一般の添字（2026-10-14）

`DynamicIndexEval.eval_row` は添字の一般Evを受け取り、入れ子の行参照の評価へ接続する。添字評価が追加する一時binding列をextraとすると、選んだ行参照は元のbinding長+extra.lengthに追加される。元の長さの位置を行参照として使わない。const/mutableの権限、任意の親epoch、非連続の行IDを引き継ぎ、既存bindingと内容を保存する。`read_root`も一般Evを使う平坦な根の読出しで、添字が作った一時binding列を保持する。

`DynamicIndexRead.read_row` は行添字と行内の位置の両方を一般Evで評価する。位置の評価中にも行参照を保持し、追加されるbinding列は「行添字の一時列、選んだ行参照、位置の一時列」の順になる。`size_row`も一般添字から選んだ行のsizeを読む。ストアと所有権森林を変えない評価の性質から、既存の行参照と元のパラメータの権限を保つことを証明する。

`DynamicIndexAtoms`は論理lookup、添字のReadyと純粋評価値、範囲の条件からflat_read/row_size/row_readのAtomicを作る。scalarOnlyの前提を要求しない。行内の位置には別のReadyを渡す。index_evは先行する添字や行参照が追加した一時bindingを許す実状態へ、同じ論理内容の証明書を適用する。返されたAtomicは既存のEvaluation/Ready/deriveへそのまま合成でき、式評価の仕事量・一時領域の上界2×式ノード数と、releasedによるRealizes保存・終了時の資源上界を引き継ぐ。行sizeのsize_t範囲、実際の値の型範囲、lookupと添字の有効範囲は検査・証明する。

`tests/test_dynamic_index.py` は非連続ID・親epoch2の共通fixtureで、同じconst別名を読む複合式を行添字と位置の両方に使う。3つの一時bindingの順序、選んだ行のowner、const/mutable権限、解放後の元のbinding列を確認する。さらにその読出しを平坦な根の添字へ入れ、一般添字を使う行sizeと合成する。健全性と資源上界は同じ論理内容を実現する任意の実状態に適用する。負・範囲外の添字、型不一致、証明書を作れない失敗経路と短絡で評価しない経路も確認する。共通AST生成の2関数を固定C++17/ASan/UBSanと照合し、戻り値、内容、元のスカラーとbinding、有効性を確認する。

Readyの原子的なlookup前提を純粋評価の成功から自動抽出することはまだ残る。今回の一般添字をappend対象の行選択へ接続すること、scope復元条件と割当可能性の抽出、Family初期化/関数呼出し、局所所有vector、行コピー/resize/構造体要素も未完了である。元のグラフ・木クラスAPIの全体検証は未達である。


## 一般添字のappendと実バッファに結び付いた償却費用（2026-10-14）

`DynamicAppendIndex.appendChild_stmt` は行を選ぶ添字と追加値の両方にReadyを持つ複合式を使う。添字が作る一時bindingの後ろに変更対象の行参照を追加し、値の評価中も保持する。値の式も任意の既存根・同じ行・const別名を読める。append後は添字・対象・値の一時bindingを解放する。任意の親epochと非連続行IDを許し、全パラメータのFamilyとスカラーsnapshotを保存する。

低層の`append_bound`は実際の更新Frameと結果バッファの対応、limit保存、itemsへの1要素追加を返す。高層`appendChild`も、純粋実行と実際のNStmtの一致・Realizes保存に加えてRowUpdateを返す。RowUpdateは変更対象の親と子の実際のlookupを更新前後で結び、親バッファが保存され、結果のlimitが旧値と同じで、内容が旧内容に1要素を足した列であることを記録する。費用定理に出る旧・新バッファはこの実際のlookupへ結び付いている。

1回の総仕事量と新ポテンシャルの和は、旧仕事量+2×添字ノード数+2×値ノード数+8+旧ポテンシャル以下。peakは旧peak、旧scalar peak、liveS+2×添字ノード数+2×値ノード数+4、更新後storage peakから評価する。変更しないバッファのlookupも低層定理で保存する。

`RoomFor s root k count`は対象行にcount要素を追加できるmax-size上の余裕を表す。capacity内に収まることは要求しない。`one`で1回のRoomAtを取り出し、`RowUpdate.remaining`で追加後に残り回数を1減らして渡せる。`RowUpdate.link`は同じ行への連続更新における「2回目の旧バッファ=1回目の新バッファ」を証明し、`two_work`はそのポテンシャルを消去して2回の費用を合成する。無関係なバッファのroomを要求しない。

`tests/test_dynamic_append_index.py`は非連続ID・親epoch2の共通fixtureで、同じ行をconst別名で読む複合式を変更対象の添字と追加値の両方に使い、2回のappendを合成する。1回目に再確保し、2回目は容量内となる。RoomForとRowUpdateから2回目の余裕と総償却費用を導き、同じ論理状態を実現する任意の実状態へ適用する。内容、子epoch、容量、親・別の根・元のスカラー・bindingの保存を確認する。対象行のlimitを3、無関係な根のlimitを1とする境界ケースでは、1回目は成功し2回目を拒否する。const対象、負/範囲外の一般添字、追加値の符号付きoverflowをモデルで拒否する。共通AST生成関数を固定C++17/ASan/UBSanと照合する。test_dynamic_index.pyのindex_checksを共通化し、元の読出し検査とC++照合は維持する。

純粋評価成功からReadyを自動構築する補題、scope復元条件の抽出、Family初期化/関数呼出し、局所所有vector、行コピー/resize/構造体要素が残る。公開グラフ・木クラス全体の検証は未達である。


## 純粋評価成功からの証明前提の自動構築（2026-10-14）

`DynamicExprDecode`は純粋なselect/denoteの成功を分解する。rootで選ばれたパラメータのslot/find?/heap lookupと型・scope、rowで親の行列・行添字・選ばれた行、sizeの型とsize_t範囲、readの型・非負添字・値のlookupと型範囲を取り出す。rowは必ずflatを返すので、rowsを選択できるのはlocalだけであることも証明する。必要な前提を成功結果から導き、検査済みの入力型・範囲条件を省略しない。

`DynamicExprAuto.ready`は式のノード数に対する強い帰納法で、すべてのNExprについてReadyを構築する。size/readの葉は上記の分解から必要なlookupを取り出し、一般添字のAtomicへ接続する。スカラー演算子は部分式のReadyを組み合わせる。利用者が各葉のlookupや中間値の証明を手で渡す必要はない。`evaluation`は純粋評価の成功からEvaluationを作り、`sound`は実行一致・有限評価成功・仕事量と一時領域の上界2×式ノード数を持つAtomicを返す。既存のreleasedへ渡すと一時参照解放後のRealizesと資源上界も得られる。短絡して評価しない失敗部分式にもReadyを構築できる。

この定理は現在のLocals/ContentsHeapとNExprのモデルに対する成功の健全性である。対応する任意の実状態にはRealizesを要求する。pure selectが失敗する深い入れ子などを新しい対応構文にしたものではなく、純粋評価の失敗一般から実際のC++が失敗することも主張しない。

`DynamicStmtAuto`はskip/declare/assign/ret/checkをScalarFormとして明示し、式のReadyを自動で供給する。scalar_soundは純粋文評価の成功とRealizesから実際のNStmt成功・Matches・資源上界を導き、scalar_runsは制御構造の対応規則へ接続する。vector文は割当とscopeの前提を別途必要とするため、このScalarFormに含めない。一般appendの式にはDynamicExprAuto.readyを直接渡せるが、対象のlookupやRoomAtは依然必要である。

`tests/test_dynamic_auto.py`は任意の式と純粋成功値に対するsoundの定理を適用し、18種類の成功例で葉の前提を指定せずにAtomicを得る。一般添字・行size・複合演算・短絡評価、深い入れ子/空行/型不一致/ゼロ除算/overflowなどの失敗を確認する。ベクトルを読む複合式をスカラー宣言し、その結果と再度の読出しをreturnする文を自動の入口へ接続する。任意のRealizes状態に対するreleasedと、一般appendへの自動Readyの適用も確認する。共通AST生成の2関数を固定C++17/ASan/UBSanと照合し、戻り値、元の内容・スカラー・binding、有効性を確認する。

次は文の純粋成功からappendのlookup/添字/値の前提を取り出すこと、scope復元条件の抽出、Family初期化と関数呼出しである。局所所有vector、行コピー/resize/構造体要素、元のグラフ・木クラスAPI全体の検証も未完了である。


## 純粋なappend成功からの前提抽出と共通の文規則（2026-10-14）

`DynamicAppendDecode`はappendRoot/appendChildの純粋内容更新と、対応するDynamicStmt.runの成功を分解する。外側appendではmutableRoot・行列lookup・更新結果を取り出す。内側appendではさらに対象の要素型、非負の行添字、追加値、行lookup、値の型範囲、更新結果を取り出す。論理内容更新の成功に含まれる条件を別途指定する必要はない。

`DynamicAppendAuto.Available`は、純粋状態が選ぶ実対象に追加できることだけを要求する。外側ではその根の実lookupとlength<limitを持つRootRoom、内側では選ばれた行のRoomAtである。capacity内であることや無関係な根の余裕は要求しない。純粋評価からは実際の割当上限を取り出せないため、この前提は残す。

`root_sound`と`child_sound`はRealizes・純粋文成功・Availableから実際のappend成功とMatchesを導く。Readyは全式に自動で供給する。child_soundは選択先/添字/値の純粋評価と実バッファのRowUpdate、償却費用、peak上界も返す。root_soundは旧実バッファlookupと仕事量=旧値+バッファ費用+3を返す。既存の低層資源定理は維持する。

`DynamicAppendAuto.sound`は現在の純粋DynamicStmt.runが成功する全NStmtを扱い、スカラー文も含めて実際の成功とMatchesを導く。`runs`はその結果を制御構造の対応規則へ接続する。共通入口は成功・結果の対応を返すもので、資源評価にはscalar_soundやroot_sound/child_soundの後条件を使う。未対応構文は純粋成功を作れず、実際のC++の失敗を証明したとは扱わない。

`tests/test_dynamic_append_auto.py`は一般添字と自己読出しの値を使う内側append、外側append、ベクトル読出しを含むreturn、skipを、lookupやReadyを入力せずに成功から接続する。任意の純粋成功文に対する共通soundの適用と、任意のRealizes状態へのchild_soundも確認する。再確保・内容・binding・別の根を検査する。外側バッファがlimitに達した状態では純粋成功は維持されるが実行は拒否し、Availableも成立しないことを証明する。const対象、要素型不一致、負の一般添字と未対応構文の扱いも確認する。共通AST生成の2関数を固定C++17/ASan/UBSanで照合する。

scope復元条件の抽出、Family初期化/関数呼出し、局所所有vector、行コピー/resize/構造体要素、元のグラフ・木クラスAPI全体の検証は未完了である。


## 純粋なscope復元と実際の状態の接続（2026-10-14）

`DynamicScopeAuto.leave_fields`は純粋なleave成功から、外側のメモリ長が内側以下であること、外側セルの型列が保存されること、復元後のLocals/ContentsHeapを取り出す。enterはscope番号だけを増やした実状態のRealizesを導く。

`leave_sound`は外側と内側のRealizes、純粋leaveの成功、終了対象scopeに所有オブジェクトがないことから、実際のNState.leaveの成功と復元後のRealizesを証明する。内側のContentsHeapを引き継ぐので、既存の根へのappendを含む内容変更を保存できる。内側で宣言したスカラー局所変数を除き、外側セルの更新、元のbindings/slots/scopeを復元する。引数パラメータのbinding範囲は外側のFamilyから、型/長さは純粋leaveから導く。戻り値はOption IntからスカラーRetへ写すので、vectorを返さない条件を別途指定する必要はない。

終了時の仕事量は内側状態の仕事量+1。peakは外側/内側の記録peak、外側/内側のscalar peakと外側liveS、内側storage peakと現在のliveSpace-baseSpaceの観測からなる正確な式を返す。生存領域の観測を既存のpeakに含まれると仮定して省略しない。

`fresh_of_tags`は、有限の森林タグのscopeが外側scope以下である検査から、より深いscopeに所有オブジェクトがないことを導く。scopeを持たない子タグも、そのrootOwnerのタグを使って扱う。この有限検査は十分条件であり、leave_sound自体は終了対象scopeだけの不在を要求する。`leave_matches`は戻り値とbreakの一致も保存し、scopeは対応済みのbody、純粋leave成功、所有オブジェクトの不在から、実際のleave成功や復元後Matchesを手で指定せずにscopeの対応へ接続する。

`tests/test_dynamic_scope_auto.py`は任意のRealizes状態に対して、宣言→外側変数への代入→returnのbodyを構成し、scope規則で局所変数の除去・外側更新・戻り値・bindings/slots/scopeの復元を確認する。外側appendと局所宣言後のleaveにも定理を適用し、変更したContentsHeap、別の根、仕事量を確認する。メモリ短縮と型変更は純粋leaveが拒否する。局所所有vectorがある状態では純粋なスカラー復元は成功し得るが、所有オブジェクトの不在は成立せず、実際の破棄結果はnoopのleftと異なることも確認する。共通AST生成の3関数で、scope内return、appendと外側代入、scope内breakを純粋実行/実行モデル/固定C++17・ASan・UBSanで照合する。

局所所有vectorの破棄やvector戻り値の移転をこの規則で扱うものではない。Family初期化/関数呼出し、局所所有vector、行コピー/resize/構造体要素、元のグラフ・木クラスAPI全体の検証は未完了である。


## 引数束縛によるFamily初期化とprepareへの接続（2026-10-14）

`DynamicFamilyInit.Compatible`は解決済みvector/nestedRoot引数のowner・要素型・scopeが論理Heapのviewに対応することを表す。scalar/scalarAddressの実際の値・型・アドレスは成功したbindOneが検査する。grant/describeは解決済み引数列からFamilyのパラメータを作り、vector参照だけでbinding番号を進める。スカラー引数が途中にあっても、その後のvector番号はずれない。同じ根のconst/mutable別名は別のbindingとして登録し、所有者に属する最大権限は保存する。

bind_rootは実際のFrame.bindRoot成功を分解し、rootWritableの実際の値、追加されるbinding位置、更新FrameとFamilyを結ぶ。bind_one/bind_allは成功したCppNestedCallの束縛をたどり、root vector引数を登録したFamilyを構築し、ストア/森林・rootWritable・scopeの保存を証明する。最大権限のfallback値を成功したbindRootで使ったとは仮定せず、実際のlookupから一致を導く。引数のconst権限を強められるかは元のresolveで、ownerの最大権限はbindRootで検査される。

`DynamicPrepare.initial`はprepareが実際に作るフレームであり、引数評価の一時参照の解放、callerの生存局所変数を数える予約セル、空のscalar/vector bindingsとslots、scope+1を含む。prepare_eqで元のprepareとbindAll initialの一致を証明する。initial_familyは解放後の物理状態を持つ空のFamilyを作り、prepared_familyは引数解決後のFamily・Compatible・prepare成功から、describeが作るcallee Familyとsnapshot/eraseHeapのRealizesを返す。ストア/森林とrootWritableの保存、callee.scope=caller.scope+1も導く。

この入口ではresolveAllの成功と、解決後のFamily・論理view対応を前提として受け取る。callerからの一般の引数解決全体とfinishまでを自動で接続した定理ではない。calleeのsnapshotを既存の自動式/文評価へ渡せる段階である。

`tests/test_dynamic_prepare.py`は、mutable nested参照・scalar値・同じ根のconst nested参照・scalar参照・別のflat参照を混在させる。非連続行IDと再確保後epochを持つ共通fixtureから、成功したprepareに新定理を適用してFamily/Realizesを構築する。引数式が作る一時bindingの解放、予約セル数、参照番号、元のセルを指すscalar参照、最大/const権限を確認する。calleeで一般読出しと参照先への代入を自動証明へ接続する。const別名を先に束縛する逆順、権限強化・型・アドレス・引数個数・scalar値範囲・scope不一致の拒否も確認する。共通AST生成関数のcallFuel全体を固定C++17/ASan/UBSanと照合し、戻り値、caller参照先への更新、再確保と内容、callerのbindings/slots/scope、別の根を確認する。有限のcallFuel照合を全入力の関数呼出し証明とはしない。

次はcallerのRealizesからresolveAllのFamily/view対応を導くことと、finishでcallerのFamilyとスカラーprefixを復元することである。局所所有vector、vector戻り値の移転、行コピー/resize/構造体要素、元のグラフ・木クラス全体の検証は未完了である。


## callerからの純粋な引数解決とFamilyの保存（2026-10-14）

`DynamicArguments.resolve/resolveAll`は現在の純粋状態で引数を解決する。値引数は式のresultTypeとパラメータ型を照合してdenoteを評価する。vector/nested参照はcallerに登録されたrootパラメータの型・scope・権限を使い、const grantをmutableへ強めない。scalar参照は型と範囲を満たす既存セルのaddressを返す。全引数を同じcallerのLocals/ContentsHeapで読むため、先に処理した引数のcallee bindingを後続の引数として使えない。引数個数と種類の不一致は拒否する。

`DynamicResolveRoots`はFamilyの任意のflat/rows viewから実際のroot objectとresolveを導く。行ID・epoch・容量の固定配置を仮定しない。`DynamicResolve.one_sound`は純粋な1引数の成功から実CppNestedCall.resolveの成功、GoodF、Ext、解決済み引数のCompatibleを返す。一般の値式は既存の自動式証明を使い、参照引数は実grantと最大権限を検査する。family_extensionは引数式が追加する一時参照を許し、同じ具体的Heap witnessを保つ。

`all_sound`は引数列の構造帰納法で、実resolveAllの成功・Family・Compatible・Realizesを導く。先行する引数式の一時bindingを保持したまま後続引数へ進み、callerのスカラー値/bindings/slots/scopeとストア/森林/rootWritableを保存する。モデルの仕事量と一時領域は、値引数ごとの2×式ノード数と参照引数ごとの1を合計したtotalWorkで上から評価する。空列は観測のためのchargeを追加せず元の状態をそのまま返す。

`DynamicCallPrepare.sound`はcallerのRealizes、純粋resolveAll成功、実prepare成功からcallee FamilyとsnapshotのRealizesへ接続する。解決後のFamilyやCompatibleを入力する必要はなくなった。calleeのストア/森林・rootWritableがcallerと同じで、scopeがcaller+1であることも導く。実prepare成功は依然前提であり、純粋な引数解決だけで全束縛の成功やfinishまでを証明したとはしない。この純粋な入口のvector参照は登録済みrootを対象とし、未登録root/child参照への対応を新たに主張しない。

`tests/test_dynamic_resolve.py`は任意のRealizes状態に新resolveAll/prepare定理を適用し、解決後Familyやlookup前提を手で再構築しない。2つの値引数が合計3一時参照を作る間にmutable/const同根参照・scalar参照・別flat参照を混在させ、局所値と物理状態の保存、費用上界、解放後の予約セル数と参照先を確認する。calleeへ自動read証明を接続する。空列、const/mutableの逆順、権限・型・アドレス・個数・overflowの拒否と、一時binding/callee変数をcaller引数に使えないことを確認する。共通AST生成関数のcallFuel全体を固定C++17/ASan/UBSanと照合し、戻り値、caller参照先への更新、再確保と内容、caller metadata、別の根を確認する。

次は純粋な引数解決成功からbindAll/prepare成功を導く型・アドレス条件と、finishでのcaller Family/スカラーprefixの復元である。局所所有vector、vector戻り値の移転、行コピー/resize/構造体要素、元のグラフ・木クラス全体の検証は未完了である。


## 純粋な引数成功から実prepare成功を構成（2026-10-14）

`DynamicResultValid.expression`は、純粋な式評価の成功からresultTypeの値範囲を導く。literal/変数の検査、算術と除算余りの変換、論理値、符号なし剰余、固定ターゲットの符号付きcast、vectorのsize/readを扱う。式の具体的な入力値を固定しない。

`DynamicBoundArguments.Boundable`は、値引数の型範囲、scalar参照先の既存セル・型・値範囲、rootのview/type/scopeと実最大権限をまとめる。one/allはcallerのFamily/Realizesと純粋な引数解決成功からこの条件を導く。transportはrootWritableの保存とメモリprefixの延長に沿って条件を保存する。const rootでは最大権限falseをそのまま保持する。

`DynamicBindExists.one_exists/all_exists`はこの条件から元のbindOne/bindAllの成功結果を構成する。scalar値は新しいセルを追加し、参照引数はcallerの元セルを指し続ける。root束縛ではFamilyのModelsから実root object/型/scopeを導き、最大権限を確認する。全束縛後のFamily、rootWritable/scopeの保存、メモリprefixの延長も返す。

`DynamicPrepareExists.prepare`はcallerのRealizesと純粋resolveAll成功だけから実prepare成功を導く。実prepare成功を前提として受け取る必要がなくなった。引数評価、一時参照の解放、予約セルの追加、全束縛を元のprepareへ接続し、calleeのRealizes、ストア/森林・rootWritableの保存、scope+1、callerメモリprefixの保存を返す。vector参照の対象は従来の登録済みrootである。関数本体・finishの成功や呼出し全体の領域上界はこの定理の結論に含まれない。

`tests/test_dynamic_prepare_exists.py`は、任意のRealizesに実prepare成功の仮定なしで定理を適用する。mutable/const同根別名、値引数、元セルへのscalar参照、別flat、空列を確認する。最大権限falseのconst rootでもFamilyから準備成功を導き、権限強化を拒否する。cast/算術/除算余り/短絡評価の型範囲、overflow・範囲外参照・個数不一致の拒否を確認する。共通AST生成callFuelを固定C++17/ASan/UBSanと有限照合し、戻り値、scalar参照先の更新、再確保、callerのmetadata復元を確認する。この有限照合は全入力のfinish証明ではない。

次はfinishでのcaller Family/スカラーprefixの復元と関数本体への接続である。局所所有vectorの破棄、vector戻り値移転、行コピー/resize/構造体要素、元のグラフ・木クラスAPIも未完了。


## caller状態の復元と関数呼出しの接続（2026-10-14）

`DynamicFinish.SameShape`は内容の変化を許しながら各rootの要素型とscopeを保存する。erase_shape/views_of_shapeにより、論理ContentsHeapの形の保存を具体的Heapのview対応へ戻せる。appendRoot_shape/appendChild_shapeは純粋なappend成功からこの保存を導く。論理viewの行ID・epoch・容量を固定しない。

`DynamicFinish.finish`は純粋なscalarメモリprefixの長さと型列を検査してcallerのbindings/slotsを戻し、scalar戻り値の型範囲またはunit/noneを検査する。`restored`は元の実finishの状態を表し、calleeのvector bindingsをcallerの一覧で置き換える。lexical scopeのleaveと異なり、callee一覧のtakeでは復元しない。

`rebound_family`はcallerの元Family、calleeの更新後Family、SameShape、rootWritableのprefix保存から、callerのbindingsを持つ更新後Familyを構築する。calleeに渡していないcallerのrootもHeapModelsと形の保存で扱い、同根const/mutable別名を復元する。soundはcaller/callee Realizes、純粋finish成功、SameShape、権限prefix、終了scopeの所有不在から元の実finish成功とcaller Realizesを導く。scalar参照先の更新とvector内容を保ち、新しいscalarセルを除く。終了仕事量はcallee+1。restored_peakは現在のcaller生存領域とvector storageの観測を含む正確なpeak式を返す。

`DynamicCall.sound`は純粋引数成功によるprepare、coupled Runsで証明した関数本体、上記finishを元のNProgram.callFuelへ接続する。prepare/finishの実成功を前提として受け取らず、成功fuelの存在とcaller Realizesを返す。本体の証明は、breakなし、純粋finish成功、SameShape、権限prefix、終了scopeの所有不在を満たす必要がある。本体の停止と費用を自動で証明する定理ではない。

`tests/test_dynamic_finish.py`は共通AST生成のscalar参照更新・行append・size返却関数に、prepareからcallFuelまでの定理を適用する。非連続行ID・再確保epochのfixtureでcallerの参照一覧とcallee一覧が異なること、caller const/mutable別名・未渡しflat・scalar bindings/slots/scopeの復元、参照先更新・再確保後内容を確認する。C++17/ASan/UBSanと戻り値・更新・容量を有限照合する。unit終了、overflow/戻り値種類/型列/短いメモリの拒否、appendのSameShape、scope変更やcallee所有vectorで必要な前提が成立しない例も扱う。有限fixtureの本体照合を全入力の本体証明とはしない。

次は本体の一般証明に対する形・権限prefix・scalar型列保存の規則を揃えることと、局所所有vectorの破棄/vector戻り値移転である。行コピー/resize/構造体要素、元のグラフ・木クラスAPIの検証も未完了。


## 本体の形・scalar型列保存と終了検査の導出（2026-10-15）

`DynamicPreserve.TypesPrefix`は、更新後scalarメモリの型列が更新前型列に追加の型列を付けたものであることを表す。値の更新を許し、既存セルの型と順序を保存する。fieldsは復元するメモリprefixの長さ・型列条件を導く。assigned_typesは実際に見つかったセルと同じ型での代入が型列を変えないことを証明する。

`DynamicPreserve.primitive`は現在の純粋実行器で成功する全primitiveに対し、SameShapeとTypesPrefixを導く。declareはscalarセルを追加し、assignは型列を保存、appendRoot/appendChildはrootの要素型とscopeを保存する。unsupported構文が成功したとは仮定しない。leaveはscope終了の型列検査から外側型列の復元を導く。leave_exists/finish_existsはTypesPrefixと適合する戻り値から純粋な終了検査の成功を構成する。

`DynamicControlPreserve.run`は成功した純粋runFuelに対し、任意のfuel/本体/初期状態でSameShapeとTypesPrefixを導く。sequence、branch、while、scope、returnとbreakによる停止を扱う。成功fuelの存在やループの停止を新たに仮定なしで証明するものではない。coupledは既存のcoupled Runsにこの保存事実を追加する。

`DynamicCallAuto.sound`はprepareのcallerメモリprefixと、本体の型列保存を合成し、終了時のscalarメモリ検査を導く。SameShapeも本体の純粋実行から導き、従来のcall定理で必要だった純粋finish成功とSameShapeの手指定を不要にする。本体はcoupled Runs、breakなし、戻り値の適合、実rootWritableのprefix、終了scopeの所有不在を与える。物理権限と所有不在は純粋な内容だけでは得られず、今回は前提に残す。全入力の本体停止/計算量や局所所有vector/vector戻り値を扱ったとはしない。

`tests/test_dynamic_preserve.py`は任意の成功runFuelへの定理適用と、型変更・メモリ短縮の拒否を確認する。生成したwhile/branch/scope/break、scalar参照先更新、root行追加とchild appendの混在関数を5入力で評価し、型列/形の保存から終了検査成功を導く。固定C++17/ASan/UBSanと結果・変更値・行数・長さを有限照合する。既存test_dynamic_finishもDynamicCallAutoを使用し、SameShapeと純粋finishをcallの前提へ渡さずにcaller Realizesを構成する。有限の本体照合を全入力の停止証明とはしない。

次は実rootWritableのprefixと所有scopeの保存を現在の実文/制御構造から導く規則、および局所所有vector破棄/vector戻り値移転である。行コピー/resize/構造体要素、元のグラフ・木クラスAPIも未完了。


## 実権限と所有scopeの保存条件（2026-10-15）

`DynamicForestEffects.NoScope f scope`はそのscopeに属する所有物がないことを表す。Preservesは任意のscopeについてこの不在を保存する関係で、合成できる。NoScope.of_tagsは有限のscope不一致検査から不在を導く。各tagのscopeを上から制限せず、無関係な深いscopeのrootを許す。

append_context_newは新しく追加した子のcontextが元の親contextと同じことを示す。append_preservesは旧オブジェクトのcontext保存とこの新しい子のcontextを組み合わせ、行追加が新しい所有scopeを作らないことを示す。非連続ID、tombstone、範囲外lookupも扱い、元の森林のwellFormedと実親lookupだけを要求する。

`DynamicPhysicalEffects.Authority`は実rootWritableのprefix保存と森林のPreservesを合わせる。Changeは現在scopeの保存も加える。flag/absentは既存のowner権限とscope不在を取り出し、transは逐次実行を合成する。GoodFからの導出、charge/release/scalar変更/declare、Frame.updatedの保存、式評価の一時bindingとbuffer更新の合成を扱う。appendRowは実Frame.appendRow成功から、appendRoot_stmtは元の実NStmt.run成功からこの条件を導く。parentのreserveや固定layoutを要求しない。

`DynamicCallEffects.sound`はcallerのcallee予定scopeに所有物がない条件と、検証済み本体のChangeを使い、終了時の権限prefix・現在scope・所有不在を導く。prepareの状態/権限保存も合成し、既存のDynamicCallAutoへ接続する。Changeは本体証明が与える条件であり、全文・全制御構造に対して自動生成できる段階ではない。今回の一般補題は行追加と共通更新操作が対象。局所所有vectorを構築する文やvector戻り値には別の破棄/移転証明が必要である。

`tests/test_dynamic_physical_effects.py`は任意の有効森林・実親lookupに対する所有不在保存と、任意の実行成功した行追加文への定理適用を確認する。scope 99の別rootを持つfixtureで2回行追加し、既存権限位置、追加flag false、新しい子の親context、scope 3の不在、tombstone/範囲外lookupと別rootを確認する。const操作と既存権限の変更を拒否する。共通AST生成の2回行追加関数を固定C++17/ASan/UBSanと有限照合する。既存test_dynamic_finishはChange証明とcaller NoScopeを使う新callへ接続する。有限本体照合を全入力の本体証明とはしない。

次はscalar文・child appendの実成功からChangeを導く入口と、制御構造での合成を揃えることである。局所所有vector/vector戻り値、行コピー/resize/構造体要素、元のグラフ・木クラスAPIの検証は未完了。


## primitiveの実保存と制御構造の合成（2026-10-15）

`DynamicStmtEffects.commit/append_frame`は実際のbuffer更新成功から森林と既存権限の保存を導く。scalarは純粋な式の成功から一般Ev/GoodFを取り出し、元の実NStmt.runへ接続する。declare/assign/ret/checkでscalar値とbindingが変わっても、森林・rootWritable・現在scopeは保存する。

childは任意の対応済み添字・値式を扱う。添字評価とchild binding生成、その後の値評価の一時参照をGoodFで合成し、実append成功からAuthorityを導く。保存定理にはRoomAtを追加で要求しない。成功を構成するsoundには、従来どおり実際のmax-sizeに余裕があるAvailableを要求する。effectsは現在の純粋実行器で成功する全文について、純粋成功・実成功・初期RealizesからChangeを返す。未対応文を実行できると主張しない。

`DynamicEffectRuns.Runs`はcoupled RunsのpostにChangeを保持する。primitiveで新soundへ接続し、sequenceは両段階のChangeを合成する。branchはguardの一般式評価を含めて保存する。scopeは本体の型列保存から純粋leave成功を導き、初期の所有不在と本体Changeから実破棄の条件を導く。scope内の新規scalarを除き、外側の変更とreturned/breakingを保存する。

whileGhostStopは継続反復に減少するghost counterを使い、開始状態から各反復までのChangeを別に合成する。guard評価、通常終了、return、break、継続の全経路で保存を引き継ぐ。breakLoop規則も含む。停止のための不変条件とcounterの減少、本体のAvailableは証明者が与える責務として残る。callはこの合成済み本体を元のcallFuelへ渡し、呼出し元の次scopeに所有物がない条件から終了時の権限/所有条件を自動で導く。

`tests/test_dynamic_stmt_effects.py`は任意のRealizesと純粋/実文成功からのeffectsを確認する。添字と値の両方がvectorを読み、一時参照を追加するchild appendで再確保と権限/森林保存を確認する。任意の対応した初期状態にdeclare→assign→retを組み、branch/scope、減少counterによるループ継続、return/breakの終了経路を合成する。生成した引数なしの定数返却関数は、caller配置・資源値を固定せずRealizesとNoScopeだけからcallFuel成功を証明する。生成した動的添字appendとscope内参照更新関数を固定C++17/ASan/UBSanと有限照合し、checkゼロ、overflow、const append、負添字を拒否する。

次はこの共通基盤を元のクラス・アルゴリズムへ接続するための局所所有vectorの構築/破棄とvector戻り値移転である。行コピー/resize/構造体要素、元のグラフ・木クラスAPIの検証は未完了。今回の規則は対応済みbodyの証明を合成するもので、任意のC++本体の自動停止証明や全入力の費用評価ではない。


## 所有vectorを含むscopeの破棄と復元（2026-10-15）

`DynamicRetire.retireHeap/retireContents`は終了scopeに属するrootを取り除く。実際の子オブジェクトは森林のcontextに従って破棄され、論理的な子の内容はrootのviewとともに消える。erase_retireは具体的Heapの破棄とContentsHeapの破棄を結ぶ。

Models.contextはroot viewのscopeと実contextを結び、Models.retiredは他scopeのviewを保存する。入れ子vectorでは全行のcontextがrootと同じことを既存の所有モデルから導き、行ID/epoch/内容を保つ。Family.retiredは残す各パラメータが元の一覧に属することとscope不一致から、破棄後の論理ヒープに対応したFamilyを構成する。Frame.retireScope成功は入力のwellFormedから導く。局所rootのbindingsを存続パラメータとして残すことは許さない。

`DynamicOwnedScope.leave`はscalarメモリprefixの型列検査に加え、ContentsHeapから終了scopeのrootを除く。soundは外側/内側のRealizes、外側パラメータが内側にも登録されていること、外側パラメータが終了scopeに属さないこと、純粋leave成功から、元の実NState.leave成功と外側Realizesを導く。終了scopeに所有物がない条件は要求しない。scalar return/returnなしを扱い、vector returnの移転はまだ対象外である。

leftは元の実処理と同じscalar prefix・bindings/slots/scopeを復元する。終了仕事量はinner.work + inner.frame.state.destroyWork scope + 1で、破棄するvectorの費用を省略しない。left_peakは外側の生存scalar領域と破棄前vector領域の観測を含む正確なpeak式を返す。資源の測定は実際の破棄後Frameから作り、解放前のlive量を残さない。

`tests/test_dynamic_owned_scope.py`は局所の入れ子vector・空const flat・fill flatを構築し、行追加と再確保、flat append、外側行の変更、外側scalar参照先の変更、局所scalar宣言を行う。更新後Familyを構成して一般破棄定理を適用し、局所root/子だけの除去、外側の内容/別名/metadata、費用、IDを再利用しないことを確認する。旧NoScope前提が実際に成立しない例で新定理を使う。共通AST生成関数のcallFuelを固定C++17/ASan/UBSanと有限照合する。

この変更はscope終了の一般境界証明である。構築操作から局所パラメータを登録したFamilyを自動で構成する証明と、純粋なbody実行器への構築/破棄の組込みは未完了で、テストの更新後Familyはfixtureから明示的に構成している。vector戻り値の移転、行コピー/resize/構造体要素、元のグラフ・木クラスAPIも残る。


## 構築からの局所root登録（2026-10-15）

`DynamicAllocateModels.prefix_model`はタグ/バッファの既存prefix保存と新状態wellFormedから任意の既存flat/rows viewを保存する。rows_old/empty_old/filled_oldは3構築操作へ適用し、非連続ID・再確保epoch・const別名・tombstoneを持つ入力を許す。rows_new/empty_new/filled_newは構築したrootの型/scope/内容と実バッファを結ぶ。rowsの新しい行IDは元の操作と同じappend位置から導く。

`DynamicAllocateFamily.Family.allocated`は全既存viewとパラメータを保存し、新しいrootのviewをHeapへ追加する。freshは新owner IDに既存viewがないことをModelsの範囲から導く。rows/empty/filledは構築後のrootWritable長と実森林長も揃える。registerは既存のbindRoot定理を使って束縛成功と追加パラメータのFamilyを構成し、束縛成功を前提にしない。新rootの最大権限は宣言のwritableと同じで、既存const/mutable別名の最大権限は保つ。remeasuredは現在のFrameから資源値を取り直す。

`DynamicDeclareOwned.sound`はFamilyと対応型の条件から、元のNStmt.declareVector成功、登録後Family、Realizes、scope保存、仕事量+2を導く。State.declareVector/bindRootの成功を前提として受け取らない。rows/fillのFamily登録はState構築成功を入力とする境界証明であり、式付きNStmt構築の純粋な成功からの自動導出はまだ未完了。

`nested_ir.lower_source`は既存scalar生成器と同じsigned_conversion選択を受け取るようになった。既定checkedは範囲外signed変換を拒否する従来の動作と生成物を保つ。明示的なgcc13.3-lp64-twos-complement契約では既存のターゲット/ABI検査を行い、nested本体とscalar calleeの両ASTへ適用してtargetCastを生成する。選択契約をIRと生成Leanのコメントに記録する。signed算術のoverflowチェックを外す変更ではない。

`tests/test_dynamic_allocate.py`は旧fixtureからrows確保→const空宣言→負値fill確保を一般定理で登録し、構築後Modelsを手で作らない。登録済みの局所rootで一般式評価/child appendを行い、OwnedScopeで破棄して外側Familyへ戻す。ゼロ行、max-size超過、範囲外fill、const書込、既存別名/別root/tombstoneを確認する。空宣言は任意のFamily/対応型への定理も適用する。固定GCC契約によるsizeと負値の混在return、ヘッダー内scalar calleeの範囲外signed変換をC++17/ASan/UBSanと有限照合し、既定checkedの拒否も確認する。

次は式付きrows/fill構築からのNStmt成功/Realizes導出と、局所参照一覧を更新する純粋bodyへの統合である。vector戻り値移転、行コピー/resize/構造体要素、元のグラフ・木クラスAPIも未完了。


## 一般式からのrows/fill構築と費用（2026-10-15）

`DynamicConstructCore.release_family/release_bindings`は一般式のGoodFと追加binding列から、元のFamilyと参照一覧を一時参照解放後へ戻す。installは共通の構築後フレームと新rootのbinding成功を構成し、Family/Realizes、局所slot追加、scope保存、仕事量とpeakの正確な式を返す。

`DynamicConstructRows.sound`はcount式の純粋成功、非負、対応型、max-size条件から元のNStmt.constructRows成功を導く。State構築やbindRoot成功を前提として受け取らない。元のheapを保存し、新root/行のviewを追加して登録する。root IDと新binding番号は一時参照解放後の元状態から導き、Realizesの局所slotへ追加する。仕事量上界は元の仕事量 + 2×count.nodes + count + 4。peak上界は式評価の一時領域と、元のlive量 + count + 2を観測する構築領域を合わせる。

`DynamicConstructFill.sound`はcount/valueの両方を一般式として評価する。先行式の一時参照を保持したまま後続式を評価し、全参照を元のbinding一覧まで解放してから構築する。countの非負/上限、対応型、初期値の型範囲から実fillVector成功、Family/Realizes/slot追加/scope保存を導く。仕事量上界は元 + 2×count.nodes + 2×value.nodes + count + 4。peakも両式の費用と構築領域を含めて評価する。ゼロ要素の場合もvalue式の評価費用を落とさない。

`tests/test_dynamic_construct.py`はvectorを読むcount式でrowsを構築し、そのFamilyへvectorを読むcount/value式のconst fillを続ける。更新後Familyを手で作らず、一般式読出し、root append、局所scope破棄へ接続する。間に別flat rootを確保して新しい行IDが非連続になり、parent epochも変わる場合を確認する。一般のcaller/heap witnessへの適用、複数の一時参照の解放、scope/元scalar/別root/既存権限の保存、ゼロcountと短絡式、負countと範囲外値の拒否を確認する。共通AST生成関数を固定C++17/ASan/UBSanと有限照合する。

次は局所参照一覧とallocation cursorを持つ純粋な所有状態へ接続し、構築を含む本体・scope・呼出しの証明を合成することである。既存ContentsHeapは未登録の実オブジェクト数やtombstoneを保持しないため、新owner IDを内容だけから仮定しない。vector戻り値移転、行コピー/resize/構造体要素、元のグラフ・木クラスAPIも未完了。


## 純粋な所有状態と構築操作の対応（2026-10-15）

`DynamicConstructCore.install_full`、rows/fillのsound_fullは構築後の実状態と参照数/オブジェクト数も返す。参照数は元+1、rowsの確保位置は元+1+count、empty/fillは元+1。既存install/soundは同じ結論のwrapperとして残し、費用証明を複製しない。DynamicOwnedLayoutは元のbindRootと空宣言から参照数/確保数/slotの正確な更新を導く。

`DynamicOwnedState.State`は従来のLocals/ContentsHeapに、可変の登録パラメータ一覧、nextOwner、nextBinding、現在scopeを加える。Realizesは従来の状態対応に加え、確保位置=実storage.objects.length、参照位置=実frame.bindings.length、scope一致を要求する。確保位置は生きているrootの最大値ではなく、子・未登録root・tombstoneを含む全確保枠を数える。参照番号の欠番や同根別名も許す。

runConstructはrows/empty/fillの純粋な構築を計算し、対応型、count/value式、非負/上限/初期値範囲を検査する。allocatedは現在の確保位置にroot viewを置き、可変paramsへbindingを追加し、slotと両cursorを進める。構築以外の文や制御構造はこの入口の対象に含まれない。

`DynamicOwnedConstruct.sound`はRealizesと純粋runConstruct成功だけから元の実NStmt成功と更新後Realizesを導く。Family witness、構築成功、bindRoot成功、参照数を手で与えない。rows/fillは一般式付き構築のfull証明、emptyは元の宣言証明と実layout補題へ接続し、既存の費用上界は元のhelperに残す。

`tests/test_dynamic_owned_state.py`はrows→const empty→const fillの純粋状態を計算し、各実状態の対応を定理だけで構成する。任意の対応callerから3文のrunFuel成功も合成する。4行と別flat・同根別名・tombstoneを持つ初期状態で、確保位置7→9→10→11、参照位置3→4→5→6を確認し、新規局所vectorを一般式で読む。誤cursor/参照数/scope、ゼロcount、負count、型/値不一致、const書込を確認する。共通AST生成関数を固定C++17/ASan/UBSanと有限照合する。

次は通常文/appendとscope終了をこの可変params・cursor付き純粋状態へ接続し、構築を含む本体の制御構造を合成することである。vector戻り値移転、行コピー/resize/構造体要素、元のグラフ・木クラスAPIも未完了。


## 所有状態のscope終了と制御構造（2026-10-15）

`DynamicOwnedCleanup.enter`はscopeを一段進める。leaveは外側paramsの包含、破棄scopeからの独立、復帰できる参照数、scalar prefixの型を検査し、外側params/参照cursor/scopeを復元する。内側の確保cursorを保持し、破棄対象の論理rootを取り除く。実storageはtombstoneを残すので、破棄した所有者IDを再利用しない。

soundは純粋leave成功と前後のRealizesから元NState.leave成功、復帰後の強いRealizes、破棄費用を含む仕事量の正確な式を導く。戻り値noneとscalarを扱う境界証明であり、vector戻り値の移転は含まれない。

`DynamicOwnedControl.runFuel`は可変params/cursorを持つ状態でsequence、scope、if、while、breakを実行する。primitiveは全3構築とskipを扱い、一般のscalar文、append、invokeScalarは現在この入口では拒否する。fuel切れはexhaustedとして区別する。soundは純粋実行の成功から同じfuelによる元CppNestedProgram.runFuelの成功と、結果/参照数/確保数/scope/return/breakの対応を導く。条件式評価後は一時参照を解放し、whileのbreakを解除する前にもscopeの破棄を実行する。

`tests/test_dynamic_owned_control.py`は共通生成器によるC++本体を純粋実行し、一般callerへのsoundを適用する。3種類の構築、ブロック、if、while/break、呼出し準備/終了、既存別rootの保存、破棄後の追加構築、参照一覧復元、誤った復帰条件の拒否、ゼロfuel/非停止ループのexhaustedを確認する。純粋prepareからcallee対応を構成し、実prepare成功を手指定しない。固定C++17/ASan/UBSanと有限照合する。

次は通常scalar文/appendを同じ所有状態へ接続し、vector戻り値移転と元のグラフ・木クラスAPIへ進む。この制御構造の証明だけでは元の各アルゴリズムの仕様・停止・計算量を検証済みとはしない。


## 所有状態に対する通常scalar文（2026-10-15）

`DynamicOwnedScalar.released`は任意の認証済み式を評価した後、一時参照を解放するとvectorフレーム全体が元に戻ることを導く。layoutは実NStmt成功と純粋式成功から、skip/宣言/代入/return/checkの完了後もフレームとscopeが同一であることを証明する。scalarメモリの更新をvector保存と混同しない。

soundは従来DynamicStmtAuto.scalar_soundの論理対応/仕事量/peak上界へ、確保cursor/参照cursor/scopeの対応を追加する。主定理は純粋文成功と初期Realizesを受け取り、実文成功を前提にしない。新しいFamilyや実式評価成功を手で作らない。

DynamicOwnedControl.primitiveは同じ所有状態のまま上記5種類の通常文も実行する。scalarの局所slotを更新し、returnを制御結果へ伝える。構築と通常文をsequence/if/for由来のwhile/scopeへ合成し、途中returnもscopeの破棄を通る。append/write/一般呼出し/vector戻り値は依然この入口では未対応である。

`tests/test_dynamic_owned_scalar.py`は共通生成C++の3種類の構築とforによる要素読出し/加算、assert、負値時の途中return、通常returnを異なる3入力で純粋実行し、一般callerへの実行対応を適用する。実prepare成功を手指定せずcallee対応を構成する。破棄したroot/子、元の別root、scalar prefixと参照一覧、const代入/範囲外変換/偽assertの拒否、return後の文の非実行、while内returnによるscope破棄を確認し、固定C++17/ASan/UBSanと照合する。従来の未対応文テストは、今回対応したscalar宣言から引き続き未対応のvector writeへ置き換えた。

次はappendの実確保余地とcursor更新を所有状態へ接続し、vector戻り値移転と元のグラフ・木クラスAPIの検証を進める。


## appendの所有状態と確保位置（2026-10-15）

`DynamicOwnedAppendLayout`は実Frame/NStmt成功から、行追加で実storage.objects.lengthが1増えること、整数appendではその長さが変わらないことを証明する。どちらも既存の参照一覧とscopeを保持する。行内appendは一般のindex/value式を認証して評価し、両式の一時参照と行参照を解放した後の参照一覧を復元する。未登録の子とtombstoneを含む確保位置を、生きている論理rootの数から推測しない。

`DynamicOwnedAppend.run`は現在の可変paramsを使って既存DynamicStmtの行追加/行内appendを純粋実行し、coreとnextOwnerを更新する。行追加はnextOwner+1、行内appendは同じnextOwnerで、nextBindingとscopeはいずれも保存する。flat rootへのappendやその他の未対応文は拒否する。

soundは純粋成功、強いRealizes、実対象bufferのAvailableから元NStmt成功と更新後の強いRealizesを導く。実NStmt成功や更新後Familyを手指定しない。Availableは実bufferのlength<limitであり、純粋内容だけから無制限の確保を仮定しない。root_soundは実仕事量=元+r.work+3を、child_soundは実前後bufferに結び付いたRowUpdateとpotentialを含む償却仕事量/peak上界を保存する。

`tests/test_dynamic_owned_append.py`は構築→新行追加→一般index/value式を使う3回のappend→所有scope破棄→追加構築を、一般定理でつなぐ。新行のID、確保位置の保存、容量0/1/2/4への拡張、元の別root/参照一覧、墓標を含む再確保位置を確認する。任意の対応callerに実room条件を与えて定理を適用する。満杯のparentとchildは実wellFormedでも実appendが失敗すること、const/負添字/未対応flat appendの拒否を確認する。共通生成C++のcallFuelはcallerの行追加がscope終了後にも残る場合を含め、固定C++17/ASan/UBSanと有限照合する。

この段階ではDynamicOwnedControl.runFuelのappend対応は追加していない。実room条件を各到達状態へ運ぶ本体合成、flat root append、vector戻り値移転、元のグラフ・木クラスAPIが残る。有限callFuel照合を本体全入力の証明済みとは扱わない。


## 到達状態のroom条件を使う所有本体の合成（2026-10-15）

`DynamicOwnedRuns.Runs`は初期の強いRealizesと、元CppNestedHoare.RunsToの成功/終了時の強いMatches/任意の事後条件を持つHoare実行証明である。純粋runFuelのappend対応を無条件に追加するものではない。各primitiveの純粋計算と実room証明を組み合わせ、元の実インタプリタで成功するfuelの存在を構成する。

primitive/control規則は既存の所有状態対応を再利用し、append規則はその到達状態のAvailableを受け取る。sequenceは最初の結果/実状態を次へ渡し、return/breakなら後続を実行しない。scopeは可変params/cursorの純粋leaveから実破棄と復帰後Matchesを構成する。branchは実条件評価と一時参照解放後の強いRealizesを渡す。任意の事後条件には実buffer/潜在量/仕事量/peakも保持できる。inspectはMatchesを事後条件にも渡し、identifyは実成功の一意性から具体的な検査結果と結ぶ。

whileGhostStopは純粋状態と実状態の両方を持つ不変条件を使う。各guard評価後に実roomや資源の証明をbodyへ渡し、継続する場合だけ減少するNatカウンタを要求する。return/breakはカウンタ0でも終了できる。fuel切れを成功や停止の証明とは扱わない。

`tests/test_dynamic_owned_runs.py`は共通生成C++のbodyと合成対象Commandの定義上の一致を確認し、構築/行追加/3回のchild append/skip/所有scope破棄を合成する。固定fixtureで局所の成功を個別検査し、一意性で次の状態へ接続する。満杯のケースを含む既存append fixtureを共有する。分岐先のappendは任意の対応callerとguard後roomで証明し、append後にbreakするwhileはcounter0で正確な最終所有状態を確認する。return後の偽assertを実行しないことも確認する。生成callFuelと固定C++17/ASan/UBSanを有限照合する。

これは本体の証明を合成する一般規則であり、既存の各アルゴリズムの全入力の仕様/計算量証明を完了させたものではない。flat append、vector戻り値移転、一般呼出し、元のグラフ・木クラスAPI、各アルゴリズムの不変条件が引き続き残る。


## flat rootの一般式appendと所有状態（2026-10-15）

`DynamicFlatFamily.other/updated`はflat rootの更新を扱う。所有権tagから更新rootが他rootの子ではないことを示し、既存の非連続行IDや別rootの内容を保存する。ownerをキーに論理heapを更新するため、同じrootの別名にも新しい内容を反映する。Familyの権限/参照一覧は保存し、資源は更新後の実frameから測る。appendは実bufferのcheckedな成長処理からFamily、初期値範囲、limit保存、実前後のitems、potentialを含む償却仕事量を導く。

`DynamicFlatAppend.run`は可変paramsのmutableRoot、一般value式の純粋評価、flat viewと要素型/値範囲を検査してcontentsを更新する。旧DynamicStmt.runのprofileは変更しない。Availableは該当実rootのlength<limitを要求する。

execute/soundは純粋成功と初期の強いRealizes/実roomから、元NStmt.append成功と更新後の強いRealizesを構成する。値の評価中は標準の一時参照を保持し、append後に解放する。nextOwner/nextBinding/scopeは保存する。償却上界はout.work+potential(new) ≤ 元.work+2×value.nodes+7+potential(old)。peak上界は一般式の一時領域と更新後storage.peakを含む。実更新後bufferのlookup/limit/itemsも返すため、次のroomや償却費用へ接続できる。

OwnedAppend.run/soundはflat root appendにも対応する。OwnedAppend.Availableはflatの場合に上記roomを要求し、既存root/child appendには従来Availableを使う。OwnedRuns.appendも同じ条件を用いて、本体の到達状態ごとに容量の証明を受け取る。無条件に成功するとしていた旧pure interpreterの範囲を広げてはいない。

`tests/test_dynamic_flat_append.py`は局所flat構築後、別vectorを読む値/自分自身を読む値/複合式の値をappendする。Family/Modelsを手指定せず、一般callerのroom条件からOwnedRunsへ適用する。容量0/1/2/4、確保数/参照数/scope、元の別rootと非連続行、scope破棄とID非再利用、const/異種container/範囲外値/満杯の拒否を確認する。共通生成C++のpush_back/emplace_backを含むcallFuelと固定C++17/ASan/UBSanを有限照合する。

次はvector戻り値移転とcall終了の所有状態対応、元のグラフ・木クラスAPIや各アルゴリズムの不変条件を進める。一般呼出し、行コピー/resize/構造体要素、残り全分野も未完了である。


## vector戻り値のscope移転と境界証明（2026-10-15）

`DynamicTransfer`はflat/rows viewのscopeだけを変える論理heap操作と、そのerase後のcontents操作を定義する。Models.moved/otherは根のtagを更新して内容/行ID/epoch/物理bufferを保存し、実State.transferに対応させる。Family.movedは残すparamsを明示し、移転対象のrootを指す旧scopeの登録を除く。Frame.transferRootはbindingのheaderを書き換えないため、その登録をそのまま保持しない。転送後も資源と確保数を実frameから測り、子vectorのcontextも新scopeに従う。

`DynamicVectorScope.leave`は返すrootのscope/要素型、外側paramsの包含/対象ownerからの独立/破棄scopeからの独立、参照数とscalar prefixを検査する。返すrootのcontents.scopeを外側へ移し、他の局所rootを削除し、外側params/参照cursor/scopeへ戻す。確保cursorは墓標を含むまま保持する。

soundは純粋境界成功と前後の強いRealizesから、元Frame.transferRootとNState.leaveのvector返却成功、復帰後の強いRealizes、実移転後frameのdestroyWork+1を含む正確な仕事量を導く。実転送/実scope終了成功を前提として受け取らない。返すrootは論理heapに残るが復帰直後には登録一覧に含まれず、利用時には外側scopeで再束縛する。

`DynamicVectorReturn.run/sound`は現在scopeのmutableな登録済みrootを返すprimitiveを扱い、純粋パラメータ解決/contentsのscope・要素型から元NStmt.retVector成功と強いRealizes保存、仕事量+1を導く。共通生成器は検査済み標準move constructorによるmutable局所vectorの返却だけを生成し、const局所/引数/コピー返却を拒否する。この既存profileを変更してはいない。

`tests/test_dynamic_vector_scope.py`はflat構築/rows構築/別flat構築を挟み、rowsへ新行と値を追加して非連続行IDを作る。一般の前後対応状態へ境界定理を適用し、primitive返却から境界へも接続する。rows返却は根と全子を保持し、flat返却は他rowsと全子を破棄する。兄弟root/元の別root/元参照一覧、確保数と正確な破棄費用、外側scopeでの再束縛、外国scope/要素不一致/参照数不足/返却ownerの旧登録保持の拒否を確認する。共通生成C++のflat/rows返却callFuelを固定C++17/ASan/UBSanと有限照合する。

この段階はprimitiveとscope境界の一般証明である。OwnedControl.Step/OwnedRunsは依然scalar returnedのみを扱い、vector返却を含む本体合成と、引数を並べ替えるcall終了の一般対応が残る。有限callFuel照合を全入力のcall証明とは扱わない。元の各クラスAPI・各アルゴリズムの仕様/不変条件/費用も引き続き未完了である。


## scalar/vector結果の本体合成と終端return（2026-10-15）

`DynamicResultScope.leave/sound`はnone/scalar/unitを従来cleanupへ、vectorを移転付きscope復帰へ接続する。純粋な復帰成功と前後の強いRealizesから元NState.leave成功と復帰後対応を導き、実leave成功を前提にしない。

`DynamicResultRuns.Step`はOption Retを持ち、Matchesは状態対応に加えて返却値とbreakを一致させる。Runsは初期の強いRealizesと元CppNestedHoare.RunsToの成功、終了時Matches/任意の事後条件を持つ。liftで旧OwnedRunsのscalar/構築/append証明と資源の事後条件を再利用し、retVectorで純粋解決から元primitive成功を導く。sequenceはvector返却でも後続を止める。scopeはpure resultに従って移転/破棄し、実復帰後状態を事後条件へ渡す。branch/whileGhostStopはOption Retをそのまま扱い、継続時のカウンタ減少、break解除、vectorを含むreturn停止を合成する。旧OwnedControl/OwnedRunsの型や公開定理は変更しない。

nested_irの終端判定は末尾scope内のreturnと、ifの両枝がreturnする場合も扱うようになった。従来はこれらをone final return is requiredで拒否していた。構造的に終端returnを確認し、関数のresult kindとも照合する。片枝だけのreturn、ゼロ回の可能性があるwhileだけのreturn、末尾に非return文がある場合は許可しない。この判定自体はループの停止や各アルゴリズムの仕様を証明するものではない。

`tests/test_dynamic_result_runs.py`は生成bodyと合成Commandの定義上の一致を確認し、flat/rows構築、行追加/child append、vector return、scope復帰、返却後skipの非実行を合成する。さらに2段scopeの移転、一般callerの分岐返却、counter0で終了するwhile内vector返却、unit境界を確認する。元vector fixtureをvector_checksへ切り出して共有する。生成器のscope/両枝return成功と片枝/whileのみの拒否を確認し、生成callFuelと固定C++17/ASan/UBSanを有限照合する。

次は引数を並べ替えるcall終了で、転送/破棄後のheapからcallerの登録一覧を復元する一般対応である。元の各クラスAPI/各アルゴリズムの不変条件・仕様・費用、一般呼出し、行コピー/resize/構造体要素、残り全分野も引き続き未完了である。


## 所有callの終了とcaller登録一覧の復元（2026-10-15）

`DynamicFinishFamily.compatible`はcallerの各登録ownerについて転送/破棄後contentsの要素型とscopeを検査する。heap全体の形の同一性は要求せず、新root/戻り値を許す。reboundはcallerの元binding一覧と権限を復元し、終了時heapのModelsと実flag prefixから新Familyを構成する。calleeのparamsにcallerのparamsが含まれることや、caller参照数≤callee参照数は仮定しない。unused caller rootと同根別名も元の一覧から復元する。

`DynamicFinishSelect.contents/frame/sound`はresult kindと返却値を検査し、vectorは現在callee scopeのrootをcaller scopeへ移す。scalarの型範囲、unitのnone、vectorの要素型/scopeを確認する。純粋成功と強いRealizesから実選択/転送とheap/Family、flags/確保数/workの保存を導く。

`DynamicOwnedFinish.finish/sound`はscalar prefixを検査し、選択・移転後にcallee scopeを実破棄してcallerのscalar bindings/slots/vector bindings/params/scopeを復元する。確保cursorはcallee終了時のまま保持し、参照cursorはcallerの元値に戻す。純粋finish成功、前後の強いRealizes、実flag prefixから元CppNestedCall.finish成功/復帰後強いRealizesを導く。実finish成功や更新Familyを手指定しない。仕事量はcallee.work+移転後frame.destroyWork(callee.scope)+1であり、scalar/unitでもowned localsの破棄費用を落とさない。

`DynamicResultCall.sound`は純粋引数解決から実prepareと初期の強いRealizesを構成する。ResultRunsの本体証明と純粋finish/flag postを受け取り、元program.callFuelの成功とcaller復帰後の強いRealizesを導く。call側へscope復帰のparams包含を持ち込まない。bodyでは各到達状態のroom、result kind、finishの型/scope整合性、flag保存を証明する。

`tests/test_dynamic_owned_finish.py`は参照順序を[flat別root,nested root]へ変更し、callee2参照→caller3参照の復元を確認する。生成bodyと合成Commandの定義上の一致、純粋prepare→構築/append/vector return→finishの一般定理からcallFuelの成功を構成する。scalar/unit finish、満たさない型/返却種別/foreign scope/scalar prefix/caller viewの拒否、墓標/戻り値の全子/元scalar/別名を確認する。さらにcallee1参照のunit callでcaller vectorを更新し、旧mutable/const別名をともに更新後heapへ戻す。固定C++17/ASan/UBSanと有限照合する。

これは全入力の個別アルゴリズム証明を構成するためのcall境界である。元の各クラスAPI・各アルゴリズムの仕様/不変条件/費用、一般呼出しの生成、行コピー/resize/構造体要素、残り全分野の検証は引き続き未完了である。


## flat vectorのコピー構築モデル（2026-10-18）

新ownerへのコピーとストア拡張・既存参照保存を`CppVectorCopy`で証明した。固定GCCプロファイル、暗黙特殊メンバーの有限照合と未対応範囲は[コピー契約](vector_copy_contract.md)に記す。copy代入をassignRangeで代用しない。UF全体のcopy/move生成・意味対応は未完了。


## scalar vectorコピーのforest/Frame接続（2026-10-18）

CppNestedCopy/CppFrameCopyで任意forestのrootまたはchildから独立rootへの実コピー、新binding/permission、全成功旧参照の値保存、コピー先への書込み分離を証明した。常駐領域とpeakはnestedのheader計数へ接続した。クラスscalarフィールドとC++ ASTからの意味対応は未完了。詳細は[コピー契約](vector_copy_contract.md)。


## vectorコピーの標準宣言監査（2026-10-18）

共有vector_stl監査でflat scalar vectorのconst参照copy構成子を識別する。default allocator/pristine primary/used helperと同じdumpの宣言を照合し、stale印を消して再監査する。これはAST identityの追加で、既存IRへのcopy実行対応はまだない。class witnessとの接続はclass_copy_audit.md。


標準vector primaryのpristine照合は、source直書きincludeのregexに代えて、同じ固定Clang AST取得時のordered user→system include JSON reportを使う。forced/quoted/macro/conditional/include shadowを実解決し、replayは固定GCC system roots内の実ヘッダーへ限定する。vector-only比較と実profileの厳密比較を維持し、macroで改変したprimaryや不整合profileは拒否する。tests/test_standard_include_profile.pyと[class_copy_audit.md](class_copy_audit.md)を参照。


コピー元の式を評価するCppCopyStatementモデルは、row参照temporaryをreleaseした後でfresh owner/bindingを作る。work/peakにはsource評価を含む。CppFrameCopyCoreとCppCopyStatementFactsの実終了/Extends/旧成功readとscalarCell保持/資源補題は[class_copy_audit.md](class_copy_audit.md)を参照。flat scalar vectorのcopyはnested_ir→NStmt.copyVectorへ接続した。クラスObjectRefとfield-slotの接続は未完了。


### 行vector引数のheader借用

具体的CppNestedCall.resolveはflat vector引数にlive child headerも受け付ける。元bindingをFrame.resolveで検査し、writable要求が元権限を超えないことを確認してResolved.vectorChild(owner,address,type,writable)へ保存する。bindOneは同じchild header/addressを新callee aliasへ追加し、候補aliasのFrame.resolveを再確認する。親epoch不一致、owner不一致、型不一致、権限強化は受渡さない。root引数の既存branchは保持する。

CppCallFrame/CppPreparePeak/CppPrepareTargetは新caseについてstore/forest/flags/ピークと引数位置を保存する。DynamicFamilyInitのroot Familyにはchildをrootとして登録せず、binding位置を1つ進めて既存root paramsの登録を保つ。DynamicBoundArguments.Boundableはchildの実headerOwner/object/maximum/permissionを持ち、transportにはframe.state同一を明示する。flagsだけでは親epochと寿命を保存できないためであり、実bind_one/引数評価が返す既存state保存を使う。DynamicBindExistsはこれらguardからchild束縛の実成功を構成する。純粋DynamicArgumentsの自動解決は従来の登録済みroot profileを維持し、row参照の全C++呼出しの自動証明完了とは区別する。

内部VecPrepareの結果分類はchild vectorをscalarから除外し、resolve_vector_res/prepare_vec_frameはHeaderを返す形へ一般化した。既存root専用bindOne_vector_frameは保持する。tests/test_vector_copy_ir.pyはroot/child両入力の生成copy実行、borrowed childへのwrite、readonly→mutable拒否、stale/header-owner拒否、コピー先のscope退去とcaller保持を確認し、同C++関数をnative UBSanと照合する。
