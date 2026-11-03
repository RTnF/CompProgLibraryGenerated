# move 構築の header・allocation・参照

`Proofs/CppMoveHeaders.lean` は、move 構築の基礎として、vector オブジェクトを表す header ID と要素の割当領域を表す allocation ID を分ける。固定 scalar vector の同一性・寿命世代を扱う抽象レイヤーであり、[実 AST 監査](class_move_audit.md)から caller 全体への意味対応は未接続である。これだけで元クラスの move を検証済みとは扱わない。

## 状態と参照

header は allocation の有無、scope、最大書込み権限、サイズ上限を持つ。allocation は既存の `CppVectorCopyAssign.Tracked` を使い、Buffer と要素の寿命世代を持つ。割当領域のない空 vector は header だけで表し、架空の要素 allocation を作らない。空でも reserve 済みなら allocation と容量を保持する。

オブジェクトの別名参照は同じ header ID を使う。捕捉済み要素参照は別の immutable grant ledger を使い、allocation/owner・epoch・要素世代と捕捉時の権限を保持する。`capture` は header・Buffer の型条件に相当する accept 条件、owner・limit、権限と添字を検査する。`read` / `write` は現在の header へ再解決せず、grant が指す allocation を使う。readonly grant の書込みは拒否する。

このレイヤーは型パラメータ α と accept 関数を使う。元 C++ の整数型・`std::allocator` と異種 Frame への型付き対応は接続側の義務である。header の最大権限と、特定の const view を通じたアクセス権限の区別も caller adapter で扱う必要がある。

## move 構築の証明

`moveConstruct` は存在する書込み可能な元 header と読取り可能な割当状態から、元の allocation 対応を none にし、新しい先 header を追加する。元 header の ID・scope・権限は残り、先 header の scope・権限は構築の引数に従う。要素 allocation・owner・epoch・世代・捕捉済み grant は変更しない。

- `move_construct_runs` / `move_construct_success`: 前提からの実成功と、任意実成功の実出力・先 ID の対応。
- `constructed_source` / `constructed_target` / `constructed_other`: 元の空化、先の同じ allocation、他 header の保持。
- `move_construct_read` / `move_construct_write`: 捕捉済み参照の読取り、および書込み後の allocation データが移動前と同じ。先オブジェクトが readonly でも、元から取得した writable 要素参照の権限は失わない。先から新しい writable 参照を取得することとは区別する。
- `move_construct_unique`: allocation の owning header が高々1つという `Unique` を保持。
- `move_construct_ownsAll`: live allocation に owning header が存在するという `OwnsAll` を保持。

`Unique` と `OwnsAll` は元の状態の前提である。元のすべての header・allocation を検証せずに任意の不整合状態を C++ の有効な状態として扱うものではない。ヘルパーの `read` / `write` / `capture` はデータ・grant の操作であり、caller の式評価全体の仕事量を表さない。

## 使用領域と仕事量

`Heap.liveSpace` は live vector header を1単位ずつ、live allocation の要素容量を一度ずつ数える。tombstone、識別子、grant 履歴、世代関数はモデルの管理情報であり、C++ の常駐領域へ加算しない。参照変数など caller の stack 領域は外側で別途数える必要がある。

`move_construct_resources` は、構築の抽象イベントの仕事量増分を1、liveSpace の増分を新 header 1単位、結果 peak を `max oldPeak (newLiveSpace - oldBaseSpace)` とし、baseSpace を保持することを示す。これはモデル上の単位と予算であり、C++ の命令数や時間の実測値ではない。固定 STL の定数時間 move 構築と caller の引数評価等をこのイベントへ接続する一般証明は残る。

## 検査と残る範囲

`tests/test_cpp_move_headers.py` は、mutable/readonly の捕捉済み参照、readonly の移動先、元 header の空化と別名参照、同じ割当領域と epoch/世代、空 vector・reserve 済み空、owner/limit/権限/存在/Buffer validity の拒否、古い epoch/世代の書込み拒否、所有者の一意性と存在、非零 baseline・過去 peak・モデル管理情報の領域除外を確認する。

GCC/ASan/UBSan では、移動元からの要素参照と vector オブジェクト参照の違い、const の移動先に対する元 writable 要素参照の書込み、空・reserve 済み空、元 scope 終了後の要素参照を有限照合する。scope 終了の一般的なモデル対応をこの有限照合から主張しない。

[move 代入の基礎モデル](move_assignment.md)は別途登録した。scope 終了・破棄、再確保などとの混在列の非復活、オブジェクトの const view、クラスの scalar 宣言順処理、Frame/NState/caller への接続と全資源、const rvalue の copy fallback は未完了である。元の機能を削る代わりに未完成のまま検証を継続する。
