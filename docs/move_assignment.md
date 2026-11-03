# move 代入の領域退役と参照

`Proofs/CppMoveAssign.lean` は [move 構築の header/allocation モデル](move_headers.md)を拡張する。固定 GCC の scalar vector・標準 allocator を対象にした抽象モデルであり、元クラスの AST から Frame/NState/caller までの意味対応は未接続である。元 C++ や公開部品をこの証明だけで検証済みとは扱わない。

## 状態遷移と前提

`moveAssign` は両 header の存在、書込み権限、allocation の可読性と同じ limit を確認する。別 header が同じ live allocation を所有する不整合も拒否する。`move_assign_runs` は所有者の一意性 `Unique` と上記前提から実際の成功を導く。成功自体を終了の前提にはしない。

旧 target の allocation を退役させ、source の allocation を target へ転送し、source を空にする。header ID・scope・権限・limit は各オブジェクトに残る。別名の比較は参照スロットではなく header ID による。自己 move は固定実装に合わせて旧 allocation を退役させ、同じ header を空にする。この具体的挙動を任意の STL 実装の保証とはしない。

`assigned_target` / `assigned_source` / `assigned_other_header` は移動先・元・他の header の対応を示す。`move_assign_unique` / `move_assign_ownsAll` は所有者の一意性と全 live allocation に所有者が存在する性質を、それぞれ入力の同じ性質から保持する。

## 捕捉済み参照

grant 履歴は書き換えない。`assigned_target_retired` は旧 target allocation への要素参照を拒否する。`assigned_source_read` は `Unique` と異なる header ID の下で source の捕捉済み参照を保持し、`assigned_read_other` は退役しない別 allocation への参照を保持する。const の独立した移動先が既に所有する領域を、空になった旧 source の代入で破棄しない。

`Moves.no_resurrection` は move 構築・move 代入だけからなる任意有限列で、一度読めなくなった捕捉済み参照が再び読めるようにならないことを示す。capture・copy・resize・新規 allocation・write・scope 終了との任意混在列はこの定理の対象外である。

## 仕事量と追加領域

`move_assign_resources` は実成功について次を示す。長さ・容量は移動前の target の値である。

- 仕事量増分は `oldTargetLength + 1`。
- `liveAfter + oldTargetCapacity = liveBefore`。予約済み空領域も容量分だけ解放する。
- `peakAfter = max peakBefore (liveBefore + 1 - baseSpace)`。
- `baseSpace` は保持する。

header を1単位、allocation を要素容量で数え、一時 header 1単位を peak に含める。grant・tombstone 等は ghost 情報である。これはモデルの予算であり命令数や実測時間ではない。引数評価、クラス scalar フィールドの宣言順代入、caller stack を含む全資源への接続は残る。

## 検査と残る範囲

`tests/test_cpp_move_assign.py` は Lean の一般定理適用と具体例で、参照転送・旧 target 参照拒否・自己 move・move 戻し・構築を含む非復活、header と所有不変条件、権限等の拒否、空・予約済み空、非零 baseline・過去 peak を検査する。固定 GCC/ASan/UBSan では要素参照・オブジェクト別名・戻り値・自己 move・空・独立した const 所有者を有限照合する。退役後の要素ポインタは dereference しない。

Frame/NState/caller adapter、object const view、クラス scalar の順処理、破棄と任意混在寿命列、const rvalue の copy fallback、元 union_find の公開版との差異の解消は未完了である。元 API・テンプレート・入力範囲を狭める代替実装へ置き換えない。
