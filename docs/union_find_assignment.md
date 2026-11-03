# UnionFind のコピー代入

候補 `experiments/verification/data_structure/union_find.hpp` のコピー代入を、元の別カウンタ・要素数・vector を持つ状態で扱う。公開版への昇格と全特殊メンバーの検証完了はまだ行っていない。

## 実評価器と数学的状態

`Proofs/UfAssignment.lean` は `CppClassAssign.assignClass` と既存の `UfReceiverState.Inv` / `Represents` を接続する。profile は、同じ宣言順の vector・count・n を持つ既存の `UfClassCopyBridge.profile` を使う。AST と実 caller への生成は [代入監査](class_assignment_audit.md) に記録する。C++ から Lean への変換の意味対応、標準 vector の契約、割当成功は従来の信頼前提である。

`assignment_terminates` は、代入元の有効な UnionFind 状態、代入先の有効な vector / 型付きスカラーセル、書込み権限から実際の成功を導く。代入先の旧 count・n が vector と整合するという前提は置かない。`assigned_represents` は実成功後の代入先が、代入元の ps・count・rank を表すことを証明する。vector の owner は代入先のまま、items は代入元と同じになり、limit とスコープ・参照構造を保持する。

スカラー値の対応は `Proofs/CppClassAssignValues.lean` で証明する。`scalar_written` は型付き書込みの結果、`fields_head` は後続フィールドが別アドレスだけを書く場合の値保存、`two_fields` / `class_two_fields` は元の2つの値が実出力へ入ることを示す。必要なアドレス相異は、代入先 count と n、および代入先 count と代入元 n であり、自己代入を排除しない。一般の逐次代入が全元フィールドを先にスナップショットするとは仮定しない。

`preserves_other` は、別 vector owner と、代入先が書かないスカラーアドレスを持つオブジェクトの `Represents` を保持する。代入元にも適用できる。`Separate` は slot 番号の相異ではなく、binding が指すメモリアドレスの相異を要求する。同じ object の自己代入は `assigned_represents` で扱う。`Inv` は通常の書込み可能な receiver 表現である。読取り専用の元には `Proofs/UfAssignmentView.lean` の `SourceView` を使う。これは typed resolve と元フィールドの読取り、vector・数学的状態の有効性だけを要求する。元 binding やスカラーセルの書込み権限を要求しない。`SourceView.of_inv` は従来の `Inv` との橋渡しであり、従来の定理の前提を変更しない。

`assign_ready` / `assign_represents` は、この読取り専用の元から実コピー代入が終了し、代入先の `Represents` を復元することを示す。`preserves_view` は root header、別 vector owner、スカラーのアドレス分離の下で同じ元の `SourceView` を保持する。`root_resolve_preserved` は binding・最大権限・forest・対象 object の保持から元の typed resolve を復元し、元の binding/スカラー権限を変えない。const view の prepare/finish を含む任意 caller 全体の不変条件証明まで完了したとは扱わない。

## 資源・参照寿命

既存の class / Frame / vector 代入証明が仕事量・peak・baseline と追跡付き参照を扱う。保存済み外部参照は ghost 世代を伴う tracked reference を使う。今回の数学的状態の復元だけで、任意の混在操作列の参照寿命や、任意 caller 全体の資源解析を完了したとは主張しない。

## コピー代入後の仕事量と操作列

`Proofs/UfAssignmentWork.lean` の `assign_work` は実評価器の成功について、代入の仕事量増分を `旧 vector 長 + 新 vector 長 + 6` 以下で抑える。Frame の storage work とスカラー仕事量を合算し、元からの累積仕事量を保持する。これは固定モデル上の仕事量上界であり、性能の実測値ではない。

`assignment_then_calls` は実コピー代入の後に、任意の有効な有限通常操作列を実行する。source の `History ps rho`、代入先の型・権限・アドレス条件から、実 `runCalls` の成功、最終 `Represents` / `History`、要素数と回答数を示す。元の5メソッドすべてを扱い、既存の `UfMethodAmortized.amortized_calls` を再利用する。

新しい要素数を n、操作数を m、source の初期 potential を Φsource、最終 potential を Φout とすると、モデル上で次を示す。

```
Wout + 91 Φout ≤ Wbefore + oldLength + n + 6
                         + 91 Φsource + 769 m (alpha(n) + 1)
```

コピーされる非零 potential を無料として除外しない。`assign_ready` が代入自体の正常終了を別途保証する。複数 receiver の代入を任意に混ぜる列、move、任意 caller の全 peak / prepare / finish をこの定理だけで完了したとは扱わない。

## 検査と残る範囲

`tests/test_union_find_assignment.py` は、旧 count=-7・n=99・vector 長4という整合しない代入先に有効な長2の UnionFind を代入し、一般定理を実状態へ適用する。終了、代入先復元、直後の実生成 size 呼出し、元と第三オブジェクトの保存、自己代入を Lean カーネルで確認する。追加の読取り専用 fixture では、元の vector/count/n binding の書込み権限を false にした状態で終了と代入先復元、直後の size 呼出し、元 view の保存を一般定理から確認する。元の binding/値の保持と、代入先を読取り専用にしたときの拒否も検査する。固定 GCC / UBSan の有限検査では n=0/1/2/17 の移動後再代入・自己代入・返却参照を確認する。移動自体の一般的な意味保存は未証明である。仕事量の一般定理と `assignment_then_calls` を読取り専用 fixture へ適用し、root/same/size/unite/numGroups の実答 `[0,0,1,0,1]` と元スカラーの保持を確認する。

move の AST / 生成 / 一般証明、const view を含む任意 caller の終了・資源、混在寿命列、公開版の番兵表現・経路圧縮等の違反解消、他の旧ライブラリの検証は未完了である。元 C++ の機能を削って検証対象を狭める変更は行っていない。
