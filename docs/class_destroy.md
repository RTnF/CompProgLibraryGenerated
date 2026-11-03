# 暗黙 destructor の宣言監査

`verifier/class_destroy.py` は、元 C++ クラスの暗黙 destructor と各フィールドの寿命終了順を同一翻訳単位の AST から監査する。出力の coverage は `member_identity_only` である。[scope 破棄モデル](move_destroy.md)・[返却 move モデル](move_return.md) へ接続するための宣言計画であり、実 caller/body の生成と一般的な実行対応は引き続き必要である。

## 実体化と宣言の同一性

`materialize_destroy` は元ソースを変更せず、`Class*` から destructor を明示的に呼ぶ witness をコンパイルする。既定構築・copy・move は要求せず、deleted copy/move の型も監査できる。private/deleted destructor は実コンパイルで拒否され、アクセス権を変更するオプションは使わない。

witness は標準 `<vector>` も include し、scalar だけのクラスでも同じ標準宣言の監査経路を使う。これは元クラスの定義を書き換えない。標準宣言の pristine primary、include profile、source hash、翻訳単位 ID は既存 vector 監査で確認する。新しい destruction mode は copy/move mode と排他にする。

`audit_destroy_record` は元クラスの完全定義、名前・位置・FieldDecl ID、元ソース hash と標準宣言の翻訳単位を検査する。フィールドの source offset が宣言順に増加することを確認し、その逆順に計画を作る。元 UnionFind では `_n`、`_num_groups`、`_ps` の順になる。

非 trivial destructor は implicit、used、defaulted、非 virtual、非 deleted、非 throwing で、元クラス位置にある一意の宣言と空の CompoundStmt を要求する。暗黙 member 破棄はこの CompoundStmt の明示呼出しとして現れないため、フィールドを別に列挙する。

全フィールドが対応済み scalar 型で、クラスの destructor が trivial と記録される場合には、Clang が本体を作らず isReferenced だけを記録する形式も受理する。この条件を vector を含む destructor へ適用しない。

## フィールド計画

対応する固定幅 scalar は `scalar_lifetime_end` とする。`std::vector<I>` は対応済み scalar 要素・標準 allocator・同一 TU の primary に由来する特殊化を確認し、used な `~vector` の TemplateInstantiationPattern が primary の destructor 宣言 ID と一致する場合だけ `vector_destroy` を作る。const vector も破棄でき、複数の vector と scalar が混在する宣言順も保持する。フィールド名で規則を選ばない。

vector の内部実装と、C++ からモデルへの意味対応は既存の信頼境界に従う。標準 destructor の内部処理を Lean で検証したという主張はしない。監査計画が複数の整数型を表せても、現行 Context/Frame の返却モデルは同一整数型 flat vector の範囲であり、異種要素の一般実行器が完成したことを意味しない。

ユーザー宣言 destructor、基底・virtual、参照フィールド、未対応型、独自 allocator、vector<bool>、nested vector は対応するモデルが必要なため拒否する。これらを持つ元ライブラリは experiments に保持して検証を続ける。

## 検査と残る接続

`tests/test_class_destroy_audit.py` は元 UnionFind の逆順計画、destructor の flags/body/位置、フィールド入替え、別 TU/source 改変、標準 destructor pattern・allocator の変異を検査する。renamed 型、copy/move deleted、const と複数 vector、scalar だけの trivial destructor、private/deleted destructor と標準特殊化の拒否も確認する。

元 caller の local 宣言・return AST、クラス scalar の保存/解放と vector header の具体的対応、実 destructor/return 計画から Lean 呼出しへの生成、callee body 全体との一般対応は未完了である。
