# vector の破棄と scope 終了

`Proofs/CppMoveDestroy.lean` は [header/allocation モデル](move_headers.md) の破棄を定義し、[caller Context](move_context.md) の借用 call の終了へ接続する。現在の Frame 接続対象は同一整数型の flat vector である。元のクラス全体の destructor AST と実 callee body からの生成接続は未完了であり、このモデルの検査だけで元ライブラリ全体を検証済みとはしない。

## 寿命と順序

`destroyHeader` は実 header と割当状態の可読性を検査し、現在の allocation を退役させ、header を tombstone にする。const オブジェクトも破棄できる。move 済みの空 source は移動先の allocation を解放しない。要素 grant は書き換えず、解放済みの領域や消えた object view を通じたアクセスを拒否する。

header ID は構築時の末尾追加で割り当て、代入では変えない。`scopeOrder` は ID 表を逆順に走査し、`destroyAtScope` が対象 scope の実在 header だけを破棄する。`scopeOrder_construct` は実 move 構築後の破棄順が新しい destination を先頭に追加した列になることを証明する。`scopeOrder_mem` と `scopeOrder_nodup` は全 ID を一度ずつ含むことを示す。tombstone の場所は再利用しない。

この逆順は現モデルの構築順に対応する。任意のユーザー定義 destructor、副作用を持つ要素、例外巻戻し、クラスの member/base の破棄順までを表してはいない。元 AST の各オブジェクト構築を header 追加へ対応させる接続も別途必要である。

## 一般定理

`destroyed_space` は一回の破棄で liveSpace が旧容量と header 一個分だけ減ることを示す。`destroyList_effects` は任意長の成功列について allocation/header が部分集合になり、grant と ID 表の長さが変わらないことを示す。

`destroyScope_ready` は Unique と全 header の ReadableHeaders から実破棄の成功を導く。実行全体の成功を入力条件には置かない。`destroyScope_invariants` は元の OwnsAll、AllocationsValid、GrantBounds を合わせ、終了後も所有の一意性・被覆、型、可読性、参照範囲、HeadersLive を保持する。

`destroyScope_closed` / `destroyScope_all` は対象 scope の生きた header が残らないことを示す。`destroyScope_no_resurrection` は既に無効な捕捉済み要素参照が、成功した scope 破棄で復活しないことを示す。新規割当・resize・nested vector を含む任意混在列はこの定理の対象外である。

## work と追加領域

実 destructor 一個に旧要素数 + 1 の抽象 work 予算を与える。これは scalar vector の線形破棄上界を表すモデル定義であり、実命令数や測定結果ではない。標準ライブラリの内部を証明したものでも、新しい STL 契約公理でもない。固定環境の allocation/deallocation とモデルの意味対応は信頼境界に残る。

`scopeCost` は初期 header が対象 scope に属す場合だけ旧要素数 + 1 を計上する。`destroyScope_work` は最終 work ≤ 初期 work + 初期 scopeBudget を証明する。一般 `destroyList_work` は重複 ID を含む任意列にも成立する上界であり、重複の費用を正確に二度払うとは主張しない。tombstone と scope の検索は ghost 台帳の処理であり、C++ work へ課金しない。

`destroyList_resources` は baseline 不変、liveSpace 非増加、過去 work/peak の保持と、最終 peak ≤ max 初期 peak (初期 liveSpace − baseline) を証明する。破棄に新しい領域は割り当てない。

## caller への復元と検査

`finishScope` は callee の対象 scope を破棄し、実 peak を Context に反映して `finishBorrowed` へ渡す。`finishScope_ready` は scope、caller view/grant prefix、scalar memory の型と長さ、Unique/ReadableHeaders から終了の成功を導く。callee で借用 vector を local に move した場合も、その local を破棄した状態で caller の scalar 更新を戻せる。返却先を外側に構築するモデルは [返却 move](move_return.md) に登録した。元 return AST と実 body への生成接続は引き続き必要である。

`tests/test_cpp_move_destroy.py` は Lean 一般定理と実成功例、空の move 元・const destination・不正 header・別 scope・二重破棄・無効参照・重複 ID の予算、caller の scalar 参照更新を検査する。固定 GCC 13.3 / C++17 / ASan / UBSan では標準 allocator の実解放を記録し、逆構築順、move 元の scope 終了での転送領域保持、const destination の一回の解放、reserve 済み空と未確保空を照合する。有限実行例から任意 C++ プログラムの意味対応を主張しない。

元 destructor AST、実 body/finish、返却 move、nested/異種 vector、通常操作の戻し込み、allocation/resize と任意混在寿命列、元クラスの全 scalar 宣言順と overload、公開 UF の機能差の解消、他分野の旧ライブラリ検証は残る。

[暗黙 destructor の宣言監査](class_destroy.md) は元 FieldDecl の逆順と標準 vector destructor の同一性を確認する。現行の scope モデルへの一般生成接続は未完了である。
