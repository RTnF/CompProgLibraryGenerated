# UnionFindの元APIを保つ候補

`experiments/verification/data_structure/union_find.hpp` は、元の `experiments/library/cpp/union_find/union_find.hpp` の全APIと表現を保つ候補である。公開版の番兵表現からの移行に使用する。公開版への置き換えはまだ行っていない。

- `UnionFind()`、`UnionFind(int)`、`unite`、`same`、`root`、`size`、`num_groups` を保持する。メソッドのconst修飾も元と同じで、`same` と `size` も経路圧縮する。
- `_ps` は要素数と同じ長さで、番兵を持たない。木の数と要素数は元と同じ別フィールド `_num_groups` と `_n` に保存する。番兵のための `n+1` や `-1-n` はなく、元のint入力範囲を狭めない。実際の確保可能量はstd::vectorの契約と実行環境に従う。
- 元のassertを保持する。構成子のフィールド初期化は本体assertより先に実行されるため、負のnは確保例外で停止する場合もある。

元のソースからの変更:

- 名前空間を `cp` に置き、標準型と必要なincludeを明示する。
- 再帰的な `return _ps[a] = root(_ps[a])` を、根を探すループと経路を圧縮するループに置き換える。結果だけでなく、圧縮後の各要素と根に保存されたサイズも同じになることを確認する。
- int同士のswapを一時変数による交換に展開し、`_ps[x] += _ps[y]` を `_ps[x] = _ps[x] + _ps[y]` にする。添字は変更されず、式に副作用はない。共通生成器が扱う構文へ揃えるための変更で、元の機能・型・入力範囲を減らしていない。

`tests/test_union_find_original_api.py` は共通生成器からその場でLeanモデルを生成する。3要素以下の全ての閉路のない親配列、深さ3の平衡木、2成分の森、深さ31の鎖で、760件の全状態をPythonの再帰モデル・元C++・候補C++・生成NProgramと照合する。戻り値、親配列、木の数、要素数を比較し、呼出し後のcaller binding・未使用セル・カウンタの別名も確認する。元C++と候補C++ではさらに32,000回の状態を引き継いだ操作列とコピー/代入を比較する。ASan/UBSanで検査し、不正な添字のassert失敗も両者と生成モデルで確認する。

C++の比較用ハーネス `tests/imports/union_find_original_api.cpp` だけを `-fno-access-control` でコンパイルし、両クラスのprivateフィールドを読み取る。元ヘッダーと候補ヘッダーの内容は変更しない。テストの入力はPythonの生成関数に定義し、TOML等へケース内容を埋め込まない。

`Proofs/UfCompression.lean` は経路圧縮後の配列を `Compressed` で記述する。全要素の所属する根、全ての負の根要素（成分サイズ）、他の木が保存されることを一般の入力で証明し、既存の検証済み2ループ実行本体へ接続する。元の再帰代入に対応する純粋なfuel付き `recursive` についても停止と圧縮結果を証明し、同じ圧縮仕様の一意性から2ループ本体との全配列・根の一致を導く。

現在の検証状況（2026-10-18）:

- C++から生成したモデルで、両構成子、全5メソッド、任意有限有効操作列の実終了、成分・サイズ・カウンタの不変条件と既存buffer/参照の保存を接続した。
- 構成子から操作列までのwork境界はO(n+m log n)。常駐領域とscalar/storage/outerのピークを分離し、操作数mに依存しない一時領域のモデル境界を証明した。詳細は末尾の「構成子前から全操作列までの領域境界」を参照する。
- 逆アッカーマンの償却時間、暗黙copy/move・代入を含む全意味対応と公開版への移行条件は未完了。有限C++照合や通常APIの証明を、元クラス全体のverify完了とは扱わない。

以下は証明を接続した順の記録である。各節の未完了記述は追加当時の状態を示し、現在の判定には上記と末尾の最新結果を用いる。


`Proofs/Generated/UnionFindCandidate.lean` は候補の6本体を共通生成器で生成したモデルで、公開部品とは別のsupportモデルとして登録する。`tests/test_union_find_fields_call.py` がC++からの再生成結果との完全一致を検査する。

`Proofs/VecShift.lean` は既存のflat-vector純粋executorに対して、vector位置0を固定し、その後に任意個のスカラーbindingを追加する対応を証明する。scalar位置0は元のとおり無効に保ち、添字式の内部も移す。成功・失敗・fuel、全scalar memory、vector内容、返却値、work、storage書込み量を保存し、scalar一時領域のneedだけbinding追加数分を加える。scope復帰とwhileを含む。未対応のnested containerやappend等を実行可能にする変換ではない。

`Proofs/UfFieldsRoot.root_call` は候補の生成rootに対し、vector参照・可変カウンタ参照・要素数・添字の引数準備から終了までを証明する。成功したprepare/body/callを前提として要求せず、型付きscalar式の値とcallerのvector/counter対応から構成する。`_n = ps.length`、`a < ps.length < 2^31` を使い、番兵のための `n < INT_MAX` という追加制限は課さない。元の再帰的純粋モデルと全配列/根が一致し、`Compressed`と森を保存する。callerのscalar memoryをそのまま戻すためカウンタやその別名も変わらず、callerのslot、vectorの参照一覧、scope、vectorの確保数/liveSpaceも保存する。

費用は `ScalarPost3` で記録する。scalar workの増分は引数式のnode数と `90 * rank a + 140` 以下、storage workの増分は `rank a` 以下。既存vectorのサイズ・容量を増やさず、storage peakと、引数準備後のpeakを基準とするscalar peakの定数上界も持つ。ここでrankは親へ進むたびに減少する値であり、union by sizeからの高さ上界や逆アッカーマン償却解析はまだ導いていない。

新テストは一般定理の具体的callerへの適用、複合式の引数、readonlyなカウンタの拒否、同じカウンタの別名、const vector別名、callerの未使用セル/参照一覧の保存、INT_MAXの要素数に対する一般の添字検査、vector添字の変数位置と無効なslot0の拒否を確認する。


`Proofs/VecCapture.lean` は、関数本体の終端returnを、新しいwritable scalar localへのコピーへ置き換える対応を証明する。途中の区間には純粋実行が正常に継続する条件 `Silent` を要求し、戻り値の型変換が恒等になることも要求する。元の実行結果のscalar memory/vector/work/wkを保ち、1セルと1bindingを追加しneedは高々2だけ増える。右側の終端skipだけを後続本体へ置き換える `plug` と、継続処理の費用・状態を合成する定理も持つ。whileについてのSilent補題は旧純粋executorの成功時の性質であり、任意のC++ while内returnを捕捉できるという主張ではない。

`Proofs/UfInlineRoot.lean` は生成器がrootを式の中へ展開する形を扱う。要素数・値引数のコピー、assert、2ループ、戻り値localを実行し、元の全セルを保って `[n,r,r,r]` の4セルを追加する。元のbinding一覧へ4つの新しいbindingを足し、CompressedとForestを保存する。任意の後続処理へ接続でき、scalar workは `90 * rank a + 72` 以下、needは元のmemory長+binding数+64以下、storage書込み量はrank以下となる。

`UfFieldsSame.body_eq` は、2つのassert・2回の上記root展開・比較の組合せが候補の生成same本体と定義上同じであることを確認する。`same_call` はvector参照、counter参照、n/a/bの型付き値引数の準備からcall終了までを構成する。最初の圧縮後もForestとroot到達関係が保たれることを使い、返す値が元の森で共通の負の根へ到達できること（Connected）と一致する。最終配列は2回のCompressed、callerのscalar memoryはcounterを含め元のまま、vector参照一覧/slot/scope/確保数/liveSpaceを保つ。scalar workの増分は引数式nodesと `90*rank a+90*rank b+220` 以下、storage workはrank和以下、追加領域はScalarPost3の上界を持つ。クラス全体の償却解析は未完了である。

`tests/test_union_find_same_call.py` は生成モデル照合、一般same_callの適用、connected/separateの正常結果、カウンタのreadonly別名を読む引数、callerの未使用セル/参照一覧、終端return捕捉後の後続計算、途中returnの除外、型変換条件とfuel不足を確認する。既存rootテストのcaller/Forest fixtureを共用する。元のbody_exec_findの定理文は保ち、内部に最終PSを返す強い補題body_exec_find_stateを追加して捕捉へ接続している。


### sizeとvector読取りの単項演算

`VecExpr.vden`/`VecWrite.vdenL`はvectorを読む式への単項演算（plus/neg/not）も扱う。`Ev.unary`と`ev_vden`は元の`NExpr.eval`への意味対応とwork/一時領域上界を証明する。符号付きnegは変換の範囲検査を残し、INT_MINを成功にしない。scalar-onlyの意味/費用とvector位置を保つ`VecShift`の性質も保持する。

`UfFieldsSize.body_eq`は候補のassert・root展開・vector読取りへの単項negと生成size本体の定義上の一致を確認する。`size_call`は引数準備から元のcallFuel/終了を構成し、元の根の負値wに対して-wを返すこと、Compressed/Forest、counterを含むcaller scalar memory/参照/slot/scope/確保数/liveSpaceの保存とScalarPost3の費用/追加領域上界を持つ。scalar work増分は引数nodes+90*rank a+160以下、storage workはrank a以下。

追加の`Weights`条件は全ての負根が`-ps.length`以上であること。ForestだけではINT_MINを許すため、この条件は必要である。構成子とuniteからのWeightsの導出は未完了。成分要素数仕様への接続は、下記Validを前提にした一般呼出しで証明する。全クラス完成まで候補をexperimentsに保持する。`tests/test_union_find_size_call.py`は一般size_callの適用/全状態、根の圧縮、単項3演算の境界値と実evalの値/work一致、複合式/符号なしwrap/INT_MIN/空vector/不正要素/未対応containerの拒否を確認する。


共通評価器の拡張で公開定理文の依存定義閉包をレビューした。変更は評価器3定義に属する12個のコンパイラ生成定義と、`vden.eq_2..5`の自動分岐等式の番号変更。旧binary/size/readの3等式は番号を1つずらすとハッシュが完全一致する。新eq_2はunary、新eq_6はunaryを除外するfallbackである。手書きの公開アルゴリズム定理文に変更はない。rootsは1776から1777、閉包は4536から4537へ増えた。無関係な変更を許可せず、この差分を照合してstatements.jsonを更新した。


### 成分要素数と根数の不変条件

`UfClassInvariant`は0以上vector長未満の添字リストをfilterして、負根一覧roots、根へ到達する要素一覧members、Connectedで同じ成分に属する要素一覧componentを定義する。各一覧がNodupであることを証明し、長さを重複のない要素数として扱う。新しいMathlib依存や公理を追加しない。

`Valid ps groups rank`はForest、長さの型範囲、各負根の値がmembersの要素数の負値であること、groupsがrootsの要素数であることを要求する。負根のWeightsとgroupsの0..nの型範囲を導出する。Compressedは全負根/根の各成分一覧を保存し、Validを保存する。`initial_valid`はreplicate(n,-1)とgroups=nがこの条件を満たすことを全n<2^31について証明する。これは数学的な初期表現の証明であり、元C++構成子のvector確保・field初期化の実call証明とは別である。

`component_eq_members`はrootへの到達からConnectedによる成分一覧とmembersの一致を証明する。`size_card_call`は候補の元size.callFuelがcomponentの要素数を返すことと、経路圧縮後のValid/元counterの保存、既存ScalarPost3の資源上界を導く。成功したprepare/body/callを前提とせず、Validを含むcallerの型付きfield/vector対応から構成する。uniteの一般呼出しは下記UfFieldsUniteへ接続した。構成子の実行からのValid構成とunion-by-sizeの高さ/償却解析は未完了。num_groupsの一般呼出しは下記UfFieldsCounterへ接続した。候補はexperimentsのままである。

`tests/test_union_find_class_invariant.py`は数学的初期状態n=0/1/INT_MAX、根/成分一覧とNodup、範囲外要素の除外、非自明な経路圧縮の森でのValid、実size一般呼出しと圧縮保存、誤ったサイズ/カウンタ/INT_MINの排除を確認する。INT_MAXは一般証明への適用であり、巨大vectorを実確保した性能測定ではない。


### uniteの結合不変条件

`UfMergeInvariant`は異なる負根のmembersが交わらないことから、成分要素数の和≤vector長を証明する。Validから根のサイズ加算のi32範囲、根が異なるときgroups≥2とgroups-1の安全性を導く。個々のWeightsだけでは2成分のサイズを二重に数え得るため、この加算の証明にはValidの実要素数条件を使う。n=INT_MAXを排除する番兵の追加制限はない。

`linked ps X Y sz`は元候補と同じ2書込み（Xの負サイズ更新、YをXの子にする）で、vector長を増やさない。結合後の到達は旧到達、またはXを終点とする旧Yへの到達に一致する。負根一覧からYだけが除かれ、Xのmembersは旧X/旧Yの互いに交わらない和、他のmembersは保存される。既存link_forestを再利用し、Valid.linkedはサイズ和を書いた結合後のValidとgroups-1を返す。rankはYの旧成分を持ち上げた存在証明であり、高さの対数上界や償却時間の証明ではない。

Valid.unite_vecは既存の番兵なしuniteVec（union-by-sizeの根選択）に接続し、同根ではvector/groupsを保存、異根ではgroups-1のValidを返す。カウンタをvector末尾に書く旧uniteVecCは用いない。Valid.unite_compressedは2回のCompressed後にこの結合を合成し、圧縮/結合全体の表現不変条件を証明する。結合後半の実行は下記UfUniteTailへ接続した。本体全体・引数準備・finishへの接続は下記UfFieldsUniteで証明する。数学的効果や後半単独の実行だけを全call証明の代用にはしない。

`tests/test_union_find_merge_invariant.py`は3回の連続結合とValid、同根保存、swapで大きい側を根に選ぶ効果、他成分保存、根一覧の1要素減少、範囲全端を保つ一般算術補題への適用、Weightsだけを満たす不正サイズの排除を確認する。候補から全6本体を再生成して照合し、同じ小さな連続操作の生成unite.callFuelの全vector/別カウンタ/別名/未使用セルも有限照合する。この有限照合を一般call証明の代用にはしない。


### 生成unite後半の実行証明

`UfUniteTail.body_eq`は候補の生成unite全本体とbefore_tail(tail)の定義上の一致を証明する。before_tailには2assert・2回のroot展開とx/yへの結果のdeclareを含む。xはslot9、yはslot14、swap temporaryはslot15、別カウンタ参照はslot1である。旧公開版のslot5/8を単に同一視しない。

`swap_exec`は候補のscope付き3命令swapを実行し、x/yのcellだけを入れ替え、temporaryのcell/bindingを除去し、vector/カウンタを保存する。`writes_exec`はrootサイズ/親への2書込み、別scalar fieldのgroups-1更新、xのreturnを実行する。vector末尾の番兵やlast変数は使わず、storage書込みは2回。元counterのreadonly aliasも同じcellの新値を見る。

`tail_correct`は同根returnと異根swap/結合の両分岐を合成する。Validと14bindingsの型付きLoc（bs index8/13/0、x/y/counterの異なるcell addresses）から、成功した後半実行を前提とせずpexecWの成功を構成する。返却根/全vectorはuniteX/uniteVec、全scalar memoryは同根なら元state、異根なら必要なx/y swapとcounter1cellの更新、bindingsはscopeで復元。新rankのValidと、scalar work≤160、need≤初期memory長+bindings長+70、storage work=同根0/異根2を返す。後半にloopはなく任意fuel（0を含む）で扱うが、前半rootループのfuel・引数prepare・callerへのfinishの接続は下記UfFieldsUniteを参照する。

`tests/test_union_find_unite_tail.py`は生成モデル全6本体一致、一般tail_correct適用、same/no-swap/swapの全後状態、counter readonly aliasと未使用cell保存、swap scope解放、番兵なし2書込みと資源上界、readonly counter拒否を確認する。結合テストから共有FIXTUREを切り出し、既存PROOF文字列を完全に保って利用する。


### 候補uniteの全本体と一般呼出し

`UfFieldsUnite.body_correct`は候補の全生成本体を、2assert→root捕捉→x宣言→root捕捉→y宣言→後半処理の順に合成する。inlineStateへの4cells/4bindings追加は元のLocを保存し、x/yは新しい別cell（P.length+7/P.length+12）となる。counterは元P内の別参照であり、両root処理と宣言で保存される。2回のCompressedと結合結果、全scalar prefixが同根ならP・異根ならcounter1cell更新となること、conditional countのValidを返す。全本体cost≤90*rank a+90*rank b+340、need≤P.length+100、storage書込み≤rank a+rank b+2。

`unite_call`はvector/可変counter参照/n/a/bの型付き値引数からprepare・callFuel・finishを構成し、成功したprepare/body/callを前提に置かない。元のConnectedとr1=r2が同値で、同根はカウンタを保存、異根は1減らし、union-by-sizeで選んだ根を返す。最終vectorは2回のCompressed後のuniteVec、最終countに対するValidを保つ。caller scalar memoryはcounter1cell以外を保存し、scalar bindings/baseMemory、vector参照一覧/slot/scope/確保数/liveSpaceも保存する。readonlyなcounter aliasは元の同じaddressから更新後の値を見る。scalar work増分は引数nodes+90*rank a+90*rank b+400以下、storage work増分はrank和+2以下、peakは既存ScalarPost3の引数prepare後peak/callerP長に対する上界であり、準備前からの閉じた定数上界と同一視しない。

`finish_scalar_metadata`/`call_scalar_metadata`はscalar結果の成功呼出しが元のscalar bindings/baseMemoryを復元することを定義から証明し、一般unite_callの結論へ明示した。counterの型はi32のままであり、n=INT_MAXまでを扱う。構成子からValidと_n=vector長を成立させる実行証明とunion-by-sizeの高さ/償却解析は未完了。num_groupsの一般callは下記を参照する。公開版はまだ置き換えない。

`tests/test_union_find_unite_call.py`は元候補全6本体の再生成一致、同成分とswapを伴う異成分の一般unite_call適用、通常結合、2root圧縮、readonly counter aliasを読む値引数、prepare時のコピー値と型、終了後の全memory/各binding一覧/別名/未使用cell、const vector alias、権限/fuel拒否を確認する。INT_MAXは抽象vectorの長さ条件を使った全入力定理の適用で検査し、巨大replicate項を実展開しない。親のValidを証明する共通PARENT_FIXTUREを切り出し、既存テストのPROOF文字列は完全に保つ。


### num_groupsの一般呼出しと成分代表

`UfFieldsCounter.prepare_counter`はvector/countRef/nの3引数の解決と束縛を構成する。`body_eq`は候補の生成本体がcounter slot1のreturnであることを確認し、`body_correct`は任意fuelでcountを返す純粋実行（work2、need≤P.length+6、storage work0）を証明する。`counter_call`は型付きcounter参照とn式、receiver資源からprepare/callFuel/finishまで構成し、成功したprepare/body/callを前提にしない。countの全i32範囲を扱い、元scalar memory/各bindings/baseMemory/slot/scope/vector内容/確保数/liveSpaceを保存する。scalar workは引数n式nodes+40以下、storage work増分0、peakは既存ScalarPost3の上界。

`Valid.root_representative`は森の各in-range要素が、roots一覧にある一意な根へ到達することを証明する。`roots_distinct_components`はrootsの2要素がConnectedであることと同じ根であることの同値を示す。rootsのNodup/全成分被覆/一意な成分代表により、その長さを成分数として扱う。`num_groups_call`はValidを使い実getterの返却値をこのrootsの要素数へ接続する。空の森では0、独立したn要素ではnを返し、getterはrootの経路圧縮やvectorへの書込みを行わない。型付きraw counterの証明と、Validを前提とする成分数解釈を区別する。

`tests/test_union_find_num_groups_call.py`は生成全6本体一致、非自明な木/独立成分/空の森の一般call適用と実実行、成分代表の一意性、別成分の識別、readonly counter aliasを読むn値引数、3paramsのprepare、元memory/各bindings/slots/baseMemory/storage workと未圧縮pathの保存、typed raw INT_MIN、権限/fuel拒否を確認する。uniteテストから汎用CALLER_STRICT fixtureを切り出して共用し、既存PROOF文字列は保つ。元C++構成子の実行/fields永続化/_n=vector長/Valid初期化、対数高さ/償却解析と元API全体の監査は未完了で、候補はexperimentsに保持する。


### 構成子の初期化処理の生成

`nested_ir.lower_source(..., construction_stages=True)`は構成子の初期化子と本体を生成する。既存のメソッド用モデルとは別の入口であり、`Proofs/Generated/UnionFindConstruction.lean`に空の構成子とint引数の構成子を記録する。field宣言順にvectorをdefault/fill構築し、counterと_nを局所fieldとして初期化してから元の本体を実行する。メンバー初期化リストの記述順を入れ替えても実行順はfield宣言順のままである。vectorの型同一性プローブは元構成子の本体先頭で`decltype(this->field)`を検査し、標準vectorの具体化・構築子の出所は同じASTで監査する。通常入口が生成する既存の6モデルは変更しない。

生成した`*_fields`はfield名と実行stateのslot位置を記録する。これは`runFuel`終了直後の初期化処理であり、fieldをcallerの永続オブジェクトへ移す処理の証明はまだない。unitの`callFuel`はscopeを破棄するため、このstageを完成した構成子の呼出しモデルとは扱わない。初期化処理の全入力の実行と初期Validへの接続は下記の一般証明で扱う。callerへの永続fieldの移行と資源上界への接続は未完了である。

`tests/test_union_find_construction.py`でdefaultおよびn=0/1/2/17/128の生成処理を実行し、全vector/counter/_nをC++ UBSan実行と照合する。初期化値/長さ/本体assertの変更検出、初期化リストの並べ替え、先に初期化したfieldの参照、未対応の継承/委譲/defaulted/range構築/未初期化field参照/構成子属性の拒否を検査する。負のnでは元と同じくvector構築がassertより先であり、モデルはサイズ上限で拒否する。確保例外とassert失敗を同一のC++機構とは主張しない。


### 確保を含む初期化処理の一般証明

`Proofs/UfConstructionStage.lean`は、生成したdefault/int構成子の初期化処理を、任意のscalar prefix・既存の論理heap/参照・確保位置・scopeについて証明する。`sized_pure`はn<2^31でfill構築→counter初期化→_n初期化→本体assertの純粋実行を構成し、`sized_stage`は既存の所有権シミュレーションから実`runFuel`の正常終了を導く。成功したpure/actual実行を入力の仮定には置かない。入力の`Realizes`は準備済みstateの型・所有権・資源対応である。

終了時の全scalar memory/bindings/slots、全vector内容`replicate n (-1)`、counter=n、_n=n、次のowner/binding位置とscopeを`final`で指定し、`Valid`（rank=0）へ接続する。`final_fields`はその対応から具体的な全配列・tag・新参照・書込み権限を取り出す。`default_pure/default_stage`は実default構築から空配列と2つのゼロfieldを得る。同じscopeでの初期化処理であり、callerへのexportを含む完成した構成子呼出しではない。一般のprepareからの前提構成は下記の証明へ接続した。永続export、copy/move、時間・追加領域の全上界と全クラスの計算量は引き続き未完了。

証明の構成では、一般のInt値に対するfield評価とscalar declareを先に独立して証明し、自然数nの変換へ適用する。自然数に特殊化した評価器の直接展開で発生したkernel深度エラーを避けるためであり、C++入力の制限は追加していない。深度上限は既存root証明と同じ4000に戻した。`tests/test_union_find_construction_proof.py`は実prepareから得たdefault/4要素stateへの定理適用、具体的全配列への接続、任意prefix/heap/owner/binding/scopeと抽象n=INT_MAX端点を確認する。


### 一般callerからの引数準備と初期化処理

`UfConstructionPrepare.prepare_sized/prepare_default`は、callerのframeのwellFormedと型の合うscalarOnlyなi32式から実prepareの成功を構成し、caller cellと既存参照数のbookkeepingを保存したscalar prefix、引数の値コピー、空のcallee vector参照一覧、scope/baseMemoryを特定する。int構成子の準備workは引数式nodes+2以下、defaultは1である。readonlyなcaller別名からも値を読める。

`sized_real/default_real`は、そのstateと任意のcaller heap対応・rootWritable一覧の長さから、前節のentry/defaultEntryのRealizesを導く。`sized_from_caller/default_from_caller`は一般callerのprepareから実runFuelへ接続し、新しいvector/counter/nの全状態と初期Validを返す。成功したprepareや実行、準備後のRealizesをcallerに仮定させない。defaultとn<2^31の全範囲を扱う。

`tests/test_union_find_construction_prepare.py`は空/既存vector付きcaller、readonly counter aliasを読むn式、元cell・既存vector/tagの保存、新owner/binding/scopeと実storage work、型不一致の拒否、任意caller/heap/式と抽象INT_MAX端点を確認する。終了stateはまだcallee scopeにある。callerへの永続field移行とtemporaryの退役を含む構成子全呼出し、資源の全上界、copy/move、クラスの高さ/償却解析は未完了である。


### callerへ保持するfieldと構成子専用の終了処理

`CppConstructorFinish.finish`は1つの所有vectorと任意個数のscalar fieldを受け取り、scalarの型付き値と書込み属性を取得し、vectorをcaller scopeへ移してからcallee scopeを解放する。scalar値はcallerの旧cellの直後へコピーし、元のscalar/vector参照・slot一覧に新fieldの位置を追加する。`ObjectRef`はcaller内のvector/scalar slotを記録する。`finish_ok`は型付きfieldの対応、所有vectorのモデル、scopeと元cellの型対応から成功を構成する。`restored_scalar/restored_vector`は新slotからの読取りを証明し、`old_view_kept`は別scopeにある既存viewの保存を示す。

`NProgram.constructFuel`は実prepare/runFuelとこの終了処理を組み合わせる。通常のunit `callFuel`は変更しない。終了処理のprofileは所有vector1つとscalar fieldsであり、C++クラスへ適用する際は生成された全fieldとの対応が必要である。複数vectorを持つクラスへの対応は未完了。

`UfConstructionExport.sized_layout/default_layout`は選択したvector/counter/nの配置と、生成された全field名・slot一覧との一致を確認する。`fields_match/export_fields`は初期化後の対応から実exportを構成する。`construct_sized/construct_default`は一般callerのprepare、確保・初期化、field移行と一時領域の解放まで実行し、caller側のvectorモデルと参照、2つの型付きscalar cell、元scalar prefix、初期Validへ接続する。成功したprepare/run/finishを利用者の前提には置かない。

`tests/test_union_find_construction_export.py`は返却receiverでgetter/uniteを実行し、新しいcounterだけの更新、_nと旧callerのcounter別名/vectorの保存を確認する。別C++ fixtureから生成したconstructorでは、i32/bool/u64の異なる値のfieldを保持し、構成子内のtemporary vectorだけを解放する。UBSanでそのC++ fixtureのfield値も照合する。readonly scalar属性、型不一致/fuel不足と抽象INT_MAXへの定理適用も検査する。

**残る義務**: 任意callerで構成子前から終了後までの全既存buffer/capacity/epoch/参照の保存、rootWritable一覧とscopeの正確な対応、新vectorのcapacity/limit等を割当てから導くこと、そこから全メソッドの一般前提を組み立てること、資源の全上界、copy/move、対数高さ/償却解析。現在のInitializedは新receiverとscalar prefixを規定するもので、これらの全クラス義務を完了したとは扱わない。候補はexperimentsに保持する。


### 初期化処理の正確な割当てframe

`CppConstructionFootprint.empty_layout/fill_layout`は実`NStmt.run`を分解し、初期化後のframe全体を`installed`と`emptyState/filledState`で規定する。空構築は旧objectsに空bufferを1つ追加し、値埋め構築は旧objectsにcapacity=count、limit=sizeLimit、epoch=0のbufferを追加する。旧forestのtag、rootWritable、binding一覧も追加前の値を保持する。`filled_old/filled_new/filled_old_tag/empty_old/empty_new`はその具体的な保存・新規lookupを取り出す。fillの式profileはscalarOnlyである。

`UfConstructionFootprint.sized_stage/default_stage`は生成された構成子本体の確保、2scalar field宣言とassert/skipを実行し、各scalar操作のframe完全保存を合成する。`sized_from_caller/default_from_caller`は一般callerの実prepareからこの結果を導く。成功したprepare/stageを利用者の前提には置かない。旧bufferのcapacity/limit/epochを含む全値、新bufferの正確なmetadataと書込み権限を追える。

`test_union_find_construction_footprint.py`は容量29・limit64・epoch7の既存buffer付きcallerでdefault/0/1/2/17要素の実stageを検査する。取得済み要素参照が、保存された元binding一覧と新storageで同じ値を読めることも確認する。任意callerと抽象INT_MAXの一般定理適用を含む。stage中の参照一覧はcallee専用であり、この検査をcallerへの復元完了と混同しない。transfer/retireを経た終了後までの全旧buffer/参照保存、scope前提と全メソッドへの一般接続、資源上界等は未完了。


### 終了scopeの解放後までのbuffer保存

`CppConstructionRetire.context_prefix`は、前方lookupが一致するforestでは旧objectのcontextも一致することを親への強帰納法で証明する。子objectを含め、旧contextがcallee scopeでなければ新rootの追加・移行・scope解放後も旧buffer全値とtagを保存する（`settled_old`）。移行した新rootのbufferもcapacity/limit/epochを保つ（`settled_new`）。`finish_frame`は実際の成功した終了処理を分解し、その正確なstate、rootWritableとcallerへ復元するbinding一覧を取り出す。

`UfConstructionPreserve.construct_sized/construct_default`は一般callerのprepareから終了後までを接続し、新receiverのInitialized、全旧buffer/tagのlookup一致、新bufferの正確なmetadata、元rootWritableとbinding一覧への追加を同時に導く。利用者に成功したprepare/run/finishを要求しない。`OldScopes`は全旧objectが次の構成子scopeを所有しないというcaller側のscope条件である。元callerのobjectがこのscopeを所有すれば、終了処理で退役するため必要となる。

`test_union_find_construction_preserve.py`は容量29/limit64/epoch7の旧bufferと取得済み要素参照を保持したまま、default/0/1/2/17要素の実constructFuelを検査する。入れ子vectorのroot/2child bufferとreadonly child bindingから取得した要素参照も、終了後のframeで直接読めることを確認する。一般定理は全buffer/tag/metadata保存とbinding/権限追加を扱い、任意取得済みReferenceのgrant/read結果の一般同値、scope条件の他のクラス不変条件からの導出、全TypedRootメソッドへの前提接続、資源全上界とcopy/move等は引き続き未完了。


### 取得済み参照の一般保存

`CppFrameExtension.Extends`は旧buffer/tag/権限/bindingのprefix対応と両frameのwellFormed・権限一覧長を記録する。`root_prefix/root_le`は旧ownerの親探索が旧領域を出ないことを証明し、`maximum_eq/object_eq/grant_eq/read_eq`は旧slot/ownerを指す参照の権限判定・オブジェクト解決・読取り結果の一致を導く。`read_eq`はstale epochや権限違反による失敗も同じ結果であることを扱う。新規追加領域を直接指す参照には適用しない。

`read_kept`は元frameでの読取り成功から必要なslot/ownerの範囲を導き、任意の取得済み参照の成功結果を保存する。`UfConstructionReferences.construct_sized/construct_default`は実構成子呼出しからInitializedとExtendsを構成し、すべての元の正常な読取りが終了後も同じ値を返すことを同時に示す。`UfConstructionPreserve`のpostにはforest長が1増える等式も追加し、終了後の権限一覧長を導出する。`oldScopes_of_bound`はcontextのscopeがcaller.scope以下という通常の上界条件からOldScopesを導く。

`test_union_find_construction_references.py`は入れ子vectorの取得済みreadonly要素参照、stale epoch、readonly grantへの書込み属性の偽装を検査する。一般Extends/構成子定理とread/grant同値へ適用し、具体的な正常値と拒否結果も照合する。任意caller/defaultと抽象INT_MAXも扱う。全TypedRootメソッドへの前提接続、scalar field別名を含む全クラス不変条件の継続保存、資源全上界、copy/move、対数高さ/償却解析等は引き続き未完了。


### 構成直後のメソッド前提とgetter

`UfConstructedReceiver.finish_base/construct_base`は実構成子終了処理がcallerのscalar基準位置を保存することを示す。`context_inside/scope_bound`は旧forest prefixと新rootのcontextから全所有者のscope上界を保存する。`receiver_ok`はInitialized、Extends、新buffer lookupとcallerのscope/base上界から、既存メソッド定理が要求するVOKWFを構成する。`sized_ready/default_ready`は実構成子呼出しの成功、Initialized、VOKWF、初期Validを一般callerから同時に導く。成功呼出しや準備済みメソッド前提を利用者には要求しない。

`n_expression`は保存された_n fieldの実scalar読取りを一般Int値で示す。`getter_from_ready/sized_getter/default_getter`はこの式をnum_groupsの実callFuelへ渡し、defaultで0、サイズ指定でnを返すことを構成子から接続する。テストはdefault/0/1/2/17要素、元readonly counter aliasからの構成、getter後のcell/binding/rootWritable/旧vector保存、任意callerと抽象INT_MAXの適用を確認する。

構成直後のroot/same/size/uniteへの接続と、その後の連続呼出しをまとめたクラス不変条件の一般保存、資源全上界、copy/move、任意callsite式、対数高さ/償却解析等は未完了。VOKWFの導出を全クラスの検証完了とは扱わない。


### root呼出し後の前提と連続呼出し

従来のScalarPost3は値・資源上界を記録するが、次のメソッド呼出しに必要なbuffer.limitや所有scopeをpostへ返していなかった。`VecWriteFrame.FramePost`は実FWからbuffer.Valid/limit/owner、tag、flag、権限一覧長、全scope上界とscalar bindings/baseの保存を取り出す。`call_vecw_frame`は従来と同じ実checked実行を構成し、ScalarPost3とFramePostを同時に返す。既存のcall_vecwと公開定理は変更しない。

`UfRootReady.ready_of_frame`はFramePostと従来postから次のメソッド用のVOKWFと型付きbuffer契約を再構成する。`root_call_ready`は実root呼出しの圧縮・再帰との一致・rankに対する資源上界に加え、終了後のVOKWFと全scalarCell結果一致を返す。`two_roots`は最初の実圧縮済みreceiverへ2回目の実root呼出しを渡し、最終forest/型付きbuffer/全scalarCell保存を一般証明する。成功した途中呼出しを利用者に仮定しない。

`test_union_find_root_ready.py`は非自明な森[-4,0,0,2]の2連続rootを一般定理へ適用し、実callFuelでも圧縮結果、counterのreadonly別名、marker9876、buffer.limit/capacity/epochを検査する。任意caller/forest/式の一般2呼出し定理にも適用する。root後のcapacity/epoch値の有限検査を、全旧参照の一般保存と混同しない。size/same/unite後の同様のpost再構成、構成子から全メソッドと任意長連続呼出しへつなぐクラス不変条件、資源全上界・copy/move・対数高さ/償却解析等は未完了。


### same・size・unite・num_groups終了後の前提

`UfSameReady.same_call_ready`、`UfSizeReady.size_call_ready`、`UfUniteReady.unite_call_ready`、`UfCounterReady.counter_call_ready/num_groups_call_ready`は、元の実prepare/body証明をcall_vecw_frameへ接続する。元の返却値・圧縮・連結性・成分サイズ・結合後Valid・資源上界に加え、終了後VOKWFと型付きbuffer契約を返す。same/size/getterは全scalarCell結果を保存する。getterのraw版はi32全域のcounter値を維持し、数学的版は根数へ接続する。

uniteはcounter cellをcountAfterへ更新し、同cellを指すreadonly等の別名も新値を読み、別addressのscalar cellを保持する。updated_other/updated_counterは実postのupdatedMemory・scalar bindings・slotsからこの対応を導く。新counterの型範囲は結合後Valid.count_rangeから証明する。

`test_union_find_method_ready.py`は既存のsame/size/unite/getterの全証明fixtureを新しい強い定理へ適用する。unite後に実getter/size/sameを呼び、counter別名が1へ更新され、marker9876と結合後配列が保たれることも照合する。これらのpostをまとめたクラス不変条件と任意長呼出し列、全buffer epoch/capacity・要素参照のメソッド後一般保存、構成子を含む資源全上界、copy/move・対数高さ/償却解析等は未完了。


### クラス不変条件と任意の有限呼出し列

`UfReceiverState.Layout`はvector/counter/nの位置とvector owner/binding/scopeを記録する。`Inv/Represents`はVOKWFとbuffer契約、数学的Valid、型付きcounter/n cells、書込み可能counter、n cellがcounterと別addressであることをまとめる。nは現在の全配列長を表す。両構成子は別々のfresh scalar cellsからこの不変条件を成立させる。

root/getter/same/size/uniteのstep定理は実生成プログラムのcallFuelを構成し、更新後のRepresentsを返す。root/same/sizeは圧縮と元の配列からの意味対応、sameの連結性、sizeの実成分要素数、uniteの2圧縮・union-by-size・count更新と新rankのValidも返す。uniteではcounter更新と別addressのn保持を組み合わせる。各stepで成功したcallを前提にはしない。

`UfReceiverTrace`のOperationは元APIの5メソッドを表す。runCallsは純粋oracleでなく実NProgram.callFuelを順に呼ぶ。calls_preserveは任意の有限な有効操作列について、適切な各callのfuelが存在し、生成プログラムが全操作を終了し、クラス不変条件と配列長を保存することを示す。constructed_calls/default_callsは実構成子からこの結果を導く。出力数・fuel数は操作数に一致する。有効とは各indexが固定された配列長内にあることをいう。各stepの値の正しさと、列の終了・不変条件保存の主張を区別する。

`test_union_find_receiver_trace.py`は12操作の混在列を実生成モデルとUBSan付きC++で照合し、返却列、最終全配列/count/n、元callerのcell/vector/取得済み要素参照を検査する。default構築後のgetter列、fuel数不一致、fuel0、範囲外indexも検査する。任意caller/操作列と抽象INT_MAXへの一般定理適用を含む。

この結果は正常な全5メソッド列の構成子からの不変条件保存を扱う。全体の時間・追加領域の計算量、対数高さ/償却解析、copy/move、全旧要素参照とcapacity/epochの各メソッド後一般保存、一般callsite/複数vector等の義務は引き続き未完了。全experimentsの検証完了や候補の公開条件充足とは扱わない。


### 到達状態のrank倍増条件とrootのwork上界

`UfRankDoubling.Balanced`は全負根のrank=0と、root rへ到達するiについて2^rank(i)≤成分rの要素数を記録する。initial_balancedは初期rank0、Balanced.compressedは経路圧縮での保存を示す。Balanced.linkedは小成分だけをrank+1するshiftで条件を保存する。forest_shiftはこの明示rankでForestを証明し、valid_linked/unite_balancedは元のunion-by-sizeの比較から大小関係を導き、ValidとBalancedを同時に保存する。任意ValidへBalancedや対数高さを仮定する形ではない。

rank_boundは根へ到達する既存の一般証明と成分サイズ≤配列長からrank(i)≤log2(n)を導く。`UfBalancedReceiver.Strong`は実receiverのRepresentsとBalancedを組み合わせる。両構成子・全5メソッド・任意の有限な有効列でStrongを成立・保存する。uniteでは実圧縮2回とuniteVecの結果から明示した新rankへ証明だけを付け替え、runtime stateを変更しない。strong_rank_boundは到達した各receiverへ適用できる。

root_workは既存の実root呼出しのScalarPost3にこのrank上界を適用し、scalar workとstorage workの合計増分≤91*log2(n)+142を示す。これは実行モデル上のwork上界で、実測時間ではない。root以外の各callと列全体・構成子を含む時間/追加領域の上界、償却α(n)解析、copy/move、全旧参照/epoch等の残る義務は未完了。

`test_union_find_rank_doubling.py`は初期/結合の一般定理、実構成からStrongへの接続、全5メソッドを混ぜた一般列、default列、実rootのwork、任意のStrong状態と列へ適用する。抽象n=INT_MAXではrank≤30を確認し巨大配列を確保しない。単なるValidとBalancedを混同しないため、負根rank=5の状態をBalancedとできないことも検査する。


### 全メソッド列のwork合計

`UfTraceWork.step_work`はStrongのrank≤log2(n)と、各実callのScalarPost3のscalar/storage workを組み合わせ、全5メソッドで共通にwork増分≤budget(n)=182*log2(n)+405を導く。uniteの2書込みも含める。実終了stateのStrongと配列長も同時に保存する。

calls_workは実runCallsの有限列に帰納し、m操作の終了後work≤開始work+m*budget(n)を示す。長さ保存により全段階で同じnを使う。構成子からのconstructed_calls_work/default_calls_workも実呼出しへ接続するが、増分の基準は構成子終了後receiver.workであり、構成子自身の確保・初期化コストはまだ含まない。これは実行モデルのworst-case work上界O(m*(1+log n))で、実測時間やα(n)償却上界ではない。

`test_union_find_trace_work.py`は混在12操作、default列、任意Strong状態/操作列へ一般証明を適用し、実生成モデルの終了workを照合する。抽象INT_MAXではbudget=5865を確認し、m*5865の上界へ接続する。追加領域と構成子を含む全資源、償却解析、copy/move等は未完了。


### 構成子を含むwork上界

`CppConstructorWork`はDynamicOwnedScalar/ConstructFill/DeclareOwnedの実step結果からworkを取り出す。新rootを移行したforestがcaller scopeでのdeclareRootと等しいこと、全旧ownerのscope上界が保たれることを示す。finish_scalar_workは実capture/finishから取得field数+1のscalar workを導く。共通補題はUnionFind固有のmoduleへ依存しない。

`UfConstructionWork.sized_stage_work/default_stage_work`は実初期化処理を合成し、work増分≤n+25/8を証明する。export_workは実field移行後にcallee scopeのobjectが残らないことを証明し、destroyWork=0のscope解放とscalar work+3から全work増分=3を導く。解放のworkを無条件に省略しない。

construct_sized_workは引数prepare、初期化、終了処理、Strongを接続し、増分≤n+en.nodes+30を示す。defaultは≤12。constructed_trace_work/default_trace_workはその後の全5メソッド列へ合計し、サイズ指定では終了work≤開始work+n+en.nodes+30+m*(182log2(n)+405)、defaultでは開始work+12+m*405を示す。実行モデル上のworst-case上界であり、実測時間や償却α(n)解析ではない。

`test_union_find_construction_work.py`はdefault/0/1/2/17、readonly変数引数と2+2の式引数、混在12操作、任意caller/列と抽象INT_MAXを検査する。追加領域、償却解析、copy/move、全旧参照/epoch等の残る義務は未完了。


構成子の領域補題（全体上界への接続は未完了）

`CppConstructorPeak.scalar_peak` / `fill_peak` は実checked stepとsound結果の一致からピーク上界を取得する。`empty_peak` は空vector確保について旧storage peakと`liveSpace+1-baseSpace`を比較した正確な式を返す。`restored_live`はcallerのbaseMemory≤memory長、calleeが旧caller memoryを収容する条件下で、k個のfieldを戻した後のscalar live量が旧caller+2kであることを示す。`restored_peak` / `finish_peak` は過去のcaller/callee peak、scalar peak、復元後のscalar live量、退役後のstorage peakをmax/sumで結合した正確な式を返す。過去の大きなpeakを現在live量へ置き換えない。

単位は既存checked modelの抽象セルであり、実測bytesではない。scalar側は`CppState.State.observe`に従いmemoryとscalar bindingsを保守的に数える。nested側はbuffer capacityとroot headerを数え、vector bindings/slot map/forest metadataそのもののLean割当量は数えない。構成子の引数評価から全stage、さらに有限method列全体への追加領域上界はまだ未証明である。


構成子stageの領域上界

`CppScalarComponents`はscalarOnly式の実declare/check/fillについてscalar側のmemory/bindings/base保存または増分、scalar peakを独立に証明する。declareはmemory/bindings各+1とpeak≤max旧peak(liveS+式nodes+2)、checkはCore保存とpeak≤max旧peak(liveS+式nodes)、fillはscalar memory/bindings/base完全保存とpeak≤max旧peak(liveS+max(count.nodes,value.nodes))。空確保も同じscalar状態を保ち、scalar peak=max旧peak(liveS)。owned wrapperは純粋primitiveの成功とRealizesから値/変換条件を抽出する。

`UfConstructionPeak.sized_stage_peak`は実生成bodyをfuel8で実行し、Realizes/正確なframeとともに、入口sからmemory/bindings各+2、base保存、scalar peak≤max s.scalarPeak(liveS(s)+7)を証明する。全体peakはmax s.peak(max s.scalarPeak(liveS(s)+10)+max s.storagePeak(s.liveSpace+n+2-s.baseSpace))以下。配列のcapacity分をscalar宣言ごとに重ねて加算しない。default_stage_peakではscalar定数5、全体定数6、storage新規分1となる。任意の適切な入口のRealizesから実bodyの成功を構成し、body成功を前提にはしない。

これらは**prepare後からbody終了まで**のモデル上界である。caller引数評価・callee用予約・finish/retireまで含めた構成子全体および任意method列全体のspace上界は依然未完了。過去のpeakを保持し、Natのbaseline差分の切捨てを考慮する。


構成子全体のwork・常駐領域・peak

`UfPreparePeak`は一般Intの引数を評価する実prepareを構成し、旧scalar/vector bindings用の予約を含むlive量とscalar/outer peakを返す。`CppConstructionSpace.appended_root_live`は旧forest/storage長一致、fresh root追加、buffer1個追加から、新liveSpace=旧liveSpace+buffer.capacity+1を証明する。`finish_live`は実field capture/finishに対してcaller scalar live+2*field数を導く。

`UfConstructorSpace.construct_sized` / `construct_default`は実constructFuel8の成功、終了後Strong、従来のwork上界、終了後の常駐領域とpeakを同じout stateで返す。sizedのscalar liveはcaller+4、nested liveSpaceはcaller+n+1。peakは次の上界（すべて既存モデルの抽象セル）を持つ:

```text
max caller.peak (
  max caller.scalarPeak (caller.liveS + caller.vectorBindings.length + en.nodes + 12)
  + max caller.storagePeak (caller.liveSpace + n + 2 - caller.baseSpace))
```

defaultはnested liveSpaceがcaller+1、scalar項の定数6（en.nodesなし）、storage項がcaller.liveSpace+1-baseSpaceとなる。終了処理で選択rootをcaller scopeへ移行し、callee scopeの解放対象がないことを示した上で、retired_freshが再観測するstorage peakを含めて合成する。prepare/stage/finishの成功を利用者に仮定しない。過去のpeakやcaller保有領域を0と置かず、scalar baseline≤caller memory長を前提にNat差分の切捨てを扱う。入力サイズ・callerの保有状態・式を固定したときのモデル上界であり、実測bytesではない。

ここまでで構成子全体の追加領域に接続した。任意のmethod列全体のspace上界、償却α、copy/move等は引き続き未完了。


式評価と要素代入のbuffer情報保存

`CppBufferHeaders.SameHeaders`はforest、storage objects長、storage baselineと全ownerのbuffer owner/capacity/limit/epoch/items長を保存する関係で、要素値の変更を許す。反射・推移性、Frame.updatedによる要素代入での保存、およびliveSpace保存を証明する。`CppEvalFrame.expression_frame` / `container_frame`は全NExpr/Containerの成功評価からframe.stateとrootWritableの完全保存を導く。子参照生成ではbindingが増えるため、frame全体の同一性は主張しない。短絡評価、targetCast、divrem、入れ子containerにも対応する。

`CppWriteHeaders.frame_write`は実Frame.writeのgrant/object/writeRef/commitを通した成功からSameHeadersとrootWritable/bindings保存を導く。`stmt_write`は実NStmt.writeの右辺→container→index評価→参照取得→write→一時binding解放を追跡し、任意containerの要素代入後のSameHeaders/rootWritable保存を導く。これらは実checked stepが成功した場合の効果定理であり、各method全体の成功/終了証明とは別である。

参照のreadはimmutable grantのslotを束縛表から検証するため、保存される既存参照についてはそのgrantが入口に登録されていることを確認する。新たに評価中だけ追加したchild bindingを、登録処理なしに永続参照として扱わない。全UF bodyの制御・scope/finishへこれらの保存を接続する義務はまだ残る。


スカラー文・scope終了の効果

`CppEvalScope`は全NExpr/Containerの成功評価でscope番号が保存されることを示す。`CppScalarFrame.scalar_frame`はskip/declare/assign/ret/checkの実成功からframe.state/rootWritable保存を導く。`CppNoResizeStmt.Effects`はSameHeaders、root権限、scope、返却値がnoneまたはscalarであることをまとめる。primitiveは上記scalar文と要素writeに対してEffectsを証明し、式にscalarOnlyを要求しない。

`CppNoResizeScope.retire_frame`は対象scopeに旧ownerがいない条件下で、実retireScope後のSameHeaders/root権限保存を証明する。leave_effectは旧forest contexts≤outer.scope、innerのSameHeaders/root権限、none/scalar返却、実leave成功から、終了後もSameHeaders/root権限を保ちscopeがouterへ戻ることを導く。peak再観測を無視せず、会計値を除くbuffer情報のみを保存する。

CommandのAllowedはscalar/write、sequence/scope/branch/while/breakの十分条件を分類する。生成UFの全5method bodyがこの条件を満たすことをkernelで確認した。reserve/確保/範囲代入/sort/dedup/vector返却/invokeScalarを含む文はこのfragmentへ入れない。Allowedの確認は本体の効果定理の証明ではない。runFuelの制御構造に対する帰納的合成、prepare/finish、全method・有限列への接続はまだ未完了。


制御・実call・任意有限操作列のmetadata保存

`CppNoResizeRun.run_headers`はfuelへの帰納により、対象fragmentの成功した実runFuelからEffectsを導く。sequenceの早期return/break、branch両側、whileのzero/return/break/継続、scopeのleaveを含む。終了やfuel存在そのものをこの効果定理で証明したことにはしない。

`CppCallFrame`は全対応引数型の実resolve/resolveAll/bindOne/bindAll/prepareについてframe.state/rootWritable保存とcallee scope=caller+1を証明する。call_headersはスカラー返却・対象body・旧context上界・実call成功からCallEffectsを返す。終了時の退役対象がないことを示し、全bufferのSignature、forest、root権限、vector/scalar bindings、slots、scope、scalar baseline、memory長、scalar live量を保存する。grant検証結果も任意Referenceで保存される。ただし要素値や任意headerOwner/resolveの結果まで同一とは主張しない。

`UfReceiverMetadata`は生成UFの全5methodへこの一般定理を適用する。sameの返却型は1bit bool、他はi32として実生成型を保つ。actual_callsは任意の終了した実runCalls列のCallEffectsを返す。calls_work_effectsは既存Strong/work定理が構成する終了結果へ接続し、任意有限な有効操作列について終了・Strong・work上界・metadata保存を同じ結果で得る。constructed_work_effects/default_work_effectsは構成子からつなぎ、最終scalar live=構成子前caller+4、nested liveSpace=caller+n+1（defaultは+1）と構成子を含む総workを証明する。

ここまでの列の領域主張は**操作列終了後の常駐領域**である。実行中の一様peak/一時領域、任意参照のread/headerOwner/resolveの一般保存、他ownerの要素値の完全保存、償却α、copy/move等は引き続き未完了。


既存参照の読取り成功・失敗の保存

`CppReferenceHeaders.read_kept`はCallEffects、新heapのwellFormed、旧Frame.readの成功から、新Frame.readも何らかのIntを返すことを証明する。immutable grant、owner、epoch、index境界と型を実read/object/readRefから抽出し、Signatureと新wellFormedから新buffer/itemへ接続する。返却値は更新で変わり得るため同一性を要求しない。headers_symm/effects_symmにより関係を逆向きにも使え、read_isSomeは**両側wellFormed**の条件で任意Referenceの読取り成功/失敗が同じであることを示す。stale、範囲外、型・owner・grant不一致も対象となる。

`UfReceiverReferences`は表現不変条件からwellFormedを取り出し、全5methodの実callと任意の終了実操作列へ接続する。calls_work_readsはStrongと有効操作列から終了結果を構成し、Strong/work/metadataと全Referenceのread.isSome保存を同じ結果で返す。成功したcallを利用者に仮定して済ませる定理とは区別する。

この同値は操作列開始後にgrant/owner数が変わらないcall履歴についてのものであり、fresh grantを追加する構成子前後の任意の未登録Referenceへ拡張しない。構成子前に実際に取得済みで読めた参照は、既存の構成子extension/read保存と接続できる。任意headerOwner/resolveと他owner値の同一性、一様peak、償却α、copy/move等は未完了。


headerOwner・resolveの保存

`CppHeaderAliases.nested_lookup_kept`は両側wellFormedと同forest、同Signatureから、nested bufferの内容が同じtag.children列であることを導き、そのbuffer全体のlookupを保存する。整数bufferの値はこの定理で固定しない。header_ownerは任意Bindingのroot/child headerについてOption Natを完全保存する。resolve_kept/resolve_signatureは任意slot・elementの成功と拒否を扱い、成功時のbindingとbuffer Signatureを保存する。整数bufferの中身は変わり得るため、resolveのbuffer全体の同一性を要求しない。

`UfReceiverAliases.Preserves`は上記headerOwner/resolveと既存read.isSome保存をまとめる。全5methodの実call、任意の終了実列へ適用し、calls_work_aliasesではStrongと有効操作列が構成する終了結果へ接続する。終了・Strong・work・metadataとalias解決の性質を同じoutで保持する。両側wellFormedを落とすと不正payloadの旧heapと新valid heapでheaderOwner/resolveの拒否が変わる負例がある。

これで通常method/call履歴のheaderOwner/resolveを一般接続した。別ownerの整数buffer値の同一性、一様peak/一時領域、償却α、copy/move等は依然未完了。


固定rootのprimitive書込みと他bufferの値保存

`CppExprPrefix`は全Container/NExprの成功評価についてslots不変と既存binding列のprefix保存を示し、式のrelease後にはframe全体が復元されることを証明する。nested readで一時child bindingを追加する式も対象となる。

`CppFixedWrite.Target`はlocal slot 0が指すbindingのownerを固定する。binding indexとowner番号が同じであることは仮定しない。write_localは実write(.local 0)の参照ownerをTargetへ接続し、対象root以外の全buffer lookupを完全保存する。scalar_full_frame/scalar_targetはscalar primitiveのframe完全保存とslot末尾追加、Target保存を示す。これらはprimitiveの結果であり、制御・prepare/finish・UF全method/有限履歴への他owner値保存はまだ未接続。一様peak、償却α、copy/moveと残りの義務も継続する。


固定rootの制御構造とscope終了

`CppFixedScope.retire_values/leave_values`は実scope退役に対象ownerが存在しないことから、全buffer lookupの保存とbinding/slots復元を導く。peak観測値の変化は許す。`CppFixedRun.Allowed`はscalar primitive、write(.local 0)、sequence/scope/branch/while/breakを扱う。Effectsは既存metadata効果、Target、元binding列、slots末尾追加、root以外の全buffer lookup一致を束ねる。run_valuesはfuel帰納により任意の成功実runFuelへ適用し、式条件の一時binding解放、早期return、break、zero loopを含む。単独では終了やfuel存在を構成せず、既存UF終了証明と接続する必要がある。

UF全5methodの生成bodyはこの分類を満たす。実prepare/finish/callとUF全有限履歴への他owner値保存はまだ未接続。一様peak、償却α、copy/move等も未完了。


他owner値保存の実call・UF有限履歴への接続

`CppPrepareTarget`は実bindRootで追加されたbinding、bindOneのbinding/slot末尾追加、後続bindAllでのTarget保存を証明する。prepare_targetは先頭のvector引数がcallerの既存bindingを指すことと実prepareから、callee local0が同ownerを指すことを導く。後続の値引数にnested readがあっても扱い、caller binding番号とowner番号の一致を仮定しない。

`CppFixedCall.finish_values/call_values`は実prepare、固定root body効果、scalar finishを合成してroot以外の全buffer lookupを保存する。read_otherはCallEffectsと両側wellFormed、他owner lookup保存から、任意Referenceのread Option Int全体の一致を示す。

`UfReceiverValues`はUF全5methodの生成body、実prepare対象ownerをLayoutへ接続する。call_values/actual_callsは全methodと任意の終了実列でreceiver以外の全buffer lookupを保存する。Selectedは既存vectorSlot/binding/ownerだけの条件で、CallEffectsから次状態へ移せる。calls_work_values/calls_work_readsはStrongと任意有限有効列から終了を構成する既存work証明へ接続し、同じoutでStrong/work/metadata、他owner全lookupと他owner参照のread値・拒否完全保存を返す。receiver自体の整数値は操作で変わる。

一様peak/一時領域、償却α、copy/move、元汎用APIと残り全分野の検証は継続する。


scalar peakと過去outer peakの分離

`CppCallUnique.call_unique`は同じprogram/caller/argumentsで成功したcallの結果がfuel量によらず同じであることを、bodyのrunFuel_success_uniqueから示す。`VecWriteScalarPeak.call_vecw_scalar_peak`は実prepareと対応するpexecWの条件から、実call成功とscalar peak≤max Sinit.scalarPeak (callerP.length+12-baseMemory+100)を構成する。call_vecw_scalar_peak_actualは任意fuelの実成功結果へこの境界を移す。

内部のCqでSPBをscalar専用境界にし、過去outer peakはTPB側の証明用envelopeへ入れる。これにより従来のScalarPost3境界にあったSinit.peakをscalar上界から除く。このTPBは実storage peakの最適境界ではない。`UfRootScalarPeak`は実root body/prepare/pexecWの証明へ適用し、任意fuelの実root成功へ同じscalar境界を返す。

検査ではcaller.outerPeakだけを1億へ増やし、同じroot callのscalar peak/memory/storage結果が変わらないことと定理の境界を確認する。他4methodとprepareのscalar上界、操作列の一様scalar/outer peakへの合成は未接続であり、これだけで一様一時領域の証明済みとは扱わない。


全5操作のscalar componentへの統合

`UfSameScalarPeak/UfSizeScalarPeak/UfUniteScalarPeak/UfCounterScalarPeak`は各ready theoremと同じ入力条件・型・汎用式・境界条件を保ち、実prepare/bodyの対応からscalar専用境界を構成する。各actual版は任意fuelの成功callへ同じ境界を移す。sameのbool結果、sizeのWeights、uniteのcount共有cell、counterの一般Int値を維持する。

`UfReceiverScalarPeak.call_peak`はRepresentsと有効Operation、実call成功から、同じ実prepareのinitとout.scalarPeak≤max init.scalarPeak (callerP.length+12-base+100)を返す。step_peakは既存Strong/workが構成する終了結果へこの境界を付け、全5操作を統一する。callerのouter履歴のみ1億へ増やした全5操作で、scalar peakとmemory/storage結果の不変・境界を検査する。

この境界にはinit.scalarPeakが残る。method prepareのscalar上界と、CallEffectsによる有限列の一様scalar境界への合成は別途必要。一様outer/storage peak、償却α、copy/move等も未完了。


操作列の一様scalarピーク

`UfMethodPreparePeak`は一般scalarOnly式とInt値を保ち、counterの1値式、root/sizeの2値式、same/uniteの3値式について、実prepare成功とinit.scalarPeak≤max caller.scalarPeak (liveS caller+caller.vectorBindings.length+各式nodesの和+12)を構成する。outerの過去ピークを上界へ混ぜない。

`UfUniformScalarPeak.budget s = liveS s+s.frame.bindings.length+112`と定義する。prepare_peakは全5Operationの引数式（nセル読取りとindex literal）を上記へ適用し、initのlocal増分を15で抑える。call_peakは既存body境界と同じinitを同一化し、out.scalarPeak≤max s.scalarPeak (budget s)を導く。budget_keptはCallEffectsからbudgetの不変を示す。

calls_peakはStrongと任意有限有効列から実終了/fuel列/Strong/workを構成し、**操作回数によらず**out.scalarPeak≤max start.scalarPeak (budget start)を証明する。run_calls_uniqueとactual_calls_peakは異なるfuel列でも成功結果が同じことを使い、任意の実終了列へ同じ境界を移す。資源の単位はモデルのscalar cellであり、実測bytesではない。全体のouter/storage peak、償却α、copy/move等は別義務。


storageピークの制御・call・有限履歴への接続

`CppWritePeak`は実writeのstorageピークがmax 前peak (前liveSpace+1-前baseSpace)であり、fresh退役はmax 前peak (前liveSpace-前baseSpace)であることを正確に示す。全Containerと成功式を扱う。`CppStoragePeak.bound`は前者の上界で、scalar/条件式、書込み、分岐・ループ・scopeを含むNoResize fragmentの実成功へrun_peakで接続する。SameHeadersによるliveSpace/baseSpace保存を用い、繰返し回数に依存しない。

`CppCallStoragePeak`は実prepareのstate保存とscalar finishのfresh退役へ接続する。`UfUniformStoragePeak.actual_calls`は全5methodと任意の終了実操作列へ適用する。calls_componentsはStrongと任意有限有効列から実終了/Strong/workを構成し、同じoutについてmetadataと一様scalar境界、storagePeak≤max 開始storagePeak (開始liveSpace+1-開始baseSpace)を返す。自然数の減算はbaseがliveより大きい場合にも飽和する。

これらはcomponentごとのモデル境界である。outer peakの過去履歴を含む全体境界と構成子からの総合、償却α、copy/move等は未完了。


outer履歴を分離した実式・primitiveのピーク関係

`CppPeakComponents.Grows`はscalarPeak/storagePeakの単調性と、outerPeak後≤max outerPeak前 (scalarPeak後+storagePeak後)を束ねる。推移性とcharge/release/observe/raw reframe・rescalar、最終component境界への接続を証明する。初期outerPeakがcomponent合計より大きい履歴も許す。

`CppEvalPeak`は全Container/NExprの成功実評価にGrowsを構造帰納で接続する。nested childの一時binding、read/size、型変換・算術・div/rem・短絡論理を含む。`CppStmtPeak`はscalar primitiveと任意containerへの実writeに適用し、RHSを先に評価する順序を保つ。writeのstorage単調性はCppWritePeakの正確な等式から導く。

制御構造・scope・prepare/finish/call・UF有限履歴へのGrows接続は未完了であり、この関係だけで全体outer上界を証明済みと扱わない。


任意有限操作列のouterピーク

`CppPeakScope`は実scope終了でscalar/storage componentがbodyから減らず、入口・bodyのouter履歴を保持することを証明する。`CppPeakRun.run_grows`はNoResize fragmentの全制御へGrowsをfuel帰納で接続する。breakでのcharge、条件式のrelease、早期returnも扱う。

`CppPreparePeak`は全対応引数型についてresolve/resolveAll、scalar bindArgument、vector/nested rootのbindOne/bindAll、実prepareへGrowsを証明する。callerセルの予約、bindings/slots初期化、複数vector引数とnested read値引数を扱う。`CppCallPeak`は実prepare/body/scalar finishを合成する。

`UfUniformPeak`は全5methodと任意の実終了操作列へGrowsを適用する。calls_peakはStrongと任意有限有効列から実終了・Strong/work/metadataと全component境界を構成し、同じoutについて
`out.peak ≤ max start.peak (max start.scalarPeak (liveS start+start.vectorBindings.length+112) + max start.storagePeak (start.liveSpace+1-start.baseSpace))`
を示す。この上界は操作回数に依存しない。actual_calls_peakは任意の実成功fuel列にも適用する。資源単位はモデルのcell/headerであり実測bytesではない。

構成子前からの全領域境界への整理、償却α、copy/moveと残り全分野の検証は継続する。


構成子前から全操作列までの領域境界

`UfConstructorSpace.construct_sized_components/construct_default_components`は、既存の構成子終了/Strong/work/常駐領域/outer境界に、独立scalar/storageピーク、storage baseline保存、vector binding数+1を追加する。従来のconstruct_sized/construct_default/export_storageは同じstatementを保つwrapperとし、証明の重複を統合した。

`UfConstructedPeak.sized/default`は実構成子と任意有限有効操作列を同じ結果へ接続する。構成子前をc、サイズをn、構成子引数式のnodesをe（defaultは0）とすると、最終scalar liveはc+4、vector liveはc+n+1。全履歴のscalar peakは`max c.scalarPeak (liveS c+c.vectorBindings.length+e+117)`、storage peakは`max c.storagePeak (c.liveSpace+n+2-c.baseSpace)`以下となる。outer peakは開始outer履歴とこの2上界の和のmax以下。いずれも操作回数を含まず、scalar上界はnも含まない。

scalar_resident/storage_residentは同じ上界を最終常駐領域で表す。scalar側の増分は最終liveSに開始vector binding数・e・113を足したもの、storage側は最終liveSpaceに1を足したもの（開始baselineを引く）で抑える。過去の各peakはmaxで保持する。単位はモデルのscalar cell/binding・vector cell/headerで、C++の実測bytesではない。

時間は構成子O(n)と各操作の最悪O(log n)による既存work境界を維持する。償却α、暗黙copy/moveの全意味対応、元汎用APIと残り全分野の検証は未完了であり、候補を公開済みとは扱わない。


## 暗黙特殊メンバーの照合とコピーの基礎モデル（2026-10-18）

元・候補C++のcopy/move構築、copy/move代入、自己代入、容量再利用と参照、移動元scalar保持・復元を追加照合した。新vectorのflatストア割当てと全旧参照保存は一般証明済み。クラス全体のC++生成モデルへは未接続であり、copy/move完了ではない。契約とテスト範囲は[vector_copy_contract.md](vector_copy_contract.md)を参照する。


## コピーのFrame基盤（2026-10-18）

CppNestedCopy/CppFrameCopyにより、元bufferの型付きresolveから新root・bindingへの実コピーと旧参照保存、独立した書込み、正確なモデルwork/spaceを接続した。UFのscalarフィールド2件とStrong、暗黙C++構成子の生成・意味保存は未接続で、UFコピー全体は未完了。詳細はvector_copy_contract.md。


## UFコピーの不変条件接続（2026-10-18）

UfCopyFields/UfCopyReceiverで新vectorと独立scalar2セルを宣言順のlayoutへ結び、コピー直後の元・先のStrongと実成功を証明した。コピー先の任意有限有効操作列の終了/Strong/workにも一般接続した。暗黙C++ ASTからの生成・意味対応と操作列後の元receiver保持は未完了。範囲と残る義務は[union_find_copy.md](union_find_copy.md)。


## コピー先操作列後の元receiver保持（2026-10-18）

UfScalarOther/UfScalarTrace/UfCopyPreserveで、コピー先の任意有限有効列の終了後も元Strong、全旧成功scalarCellとvector参照の値を保つ一般証明を追加した。workも同じoutへ接続する。暗黙copy ASTの生成・意味対応、copy全体のscalar/outer境界、代入/move/償却αは未完了。詳細はunion_find_copy.md。


## コピー前から操作列までの領域境界（2026-10-18）

UfCopyPeakで既存構成子envelopeをnodes=0として再利用し、copyReceiver前から任意有効列までのscalar/storage/outer上界を同じ終了・両Strong・全旧成功参照保存・workのoutへ接続した。scalar/storageの常駐増分は+4/n+1。暗黙copy AST生成・意味対応と代入/move/償却αは未完了。詳細はunion_find_copy.md。
