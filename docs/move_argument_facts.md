# 引数評価のデータ・型保持と準備処理

`Proofs/CppMoveArgumentFacts.lean` は [caller Context](move_context.md) の実引数評価から準備条件を導く。対象は現在の NExpr が表す算術、cast、read、size、短絡論理等と、同一整数型の flat vector 参照である。class call/move/assignment の引数副作用や C++ AST の評価順全体までを代替しない。

## 評価中のデータと型

`container_data` / `expression_data` は任意の実評価成功について scalar memory、binding、baseline の保持を証明する。`evalExpression_stable` / `resolveArgument_stable` / `resolveArguments_stable` は Context の object view、slot、scope、scalar データを保持する。work と peak の更新は維持する。既存の一時 Frame binding 解放の一般定理と組み合わせて投影する。

整数 `convert` の結果は変換先型を満たす。unsigned は剰余の範囲、boolean は0/1、signed は元の範囲検査を使う。`targetConvert_valid` は固定環境の32/64 bit signed decode の既存範囲定理へ接続し、それ以外の経路は通常の convert へ従う。新しい契約公理は追加しない。

`expression_valid` は NExpr の全構成子について、成功した値が resultType.valid を満たすことを示す。read では実 readRef の Buffer.Valid と取得要素から、size では実長さ検査から導く。論理式は0/1を返す。入力が不正な場合の成功を主張するものではない。

## 実引数から準備条件へ

`captureBorrow_ready` / `captureScalarReference_ready` / `resolveArgument_ready` は実際に作成された参照・値引数が SavedReady を満たすことを示す。先行引数の参照先は後続 NExpr によって変わらないため、`resolveArguments_ready` はすべての保存引数の条件を最終 Context で導ける。

`prepareArguments_of_resolve` は実 `resolveArguments` の正常終了から、後続の準備処理が成功し、元 heap を変えず、保存引数数だけ callee slot を持つことを導く。完全な prepare の成功を前提にはせず、既存の `prepareSaved_ready` へつなぐ。元式の不正な添字や除算等は評価側で拒否される。

`resolveArguments_lengths` は保存引数数・構文引数数・パラメータ数の一致を示す。`prepareArguments_resources` は実評価後 Context を last として、準備後 work = work last + 1 + パラメータ数、および評価後の過去 peak を含む線形の準備 peak 上界を示す。scalar memory、baseline、宣言 slot は評価前と同じなので、領域予算には元 caller の個数を使える。ghost grant/view 履歴数を使わない。これは現在の引数評価と準備の接続範囲であり、callee body/一般 scope 終了を含む全 call の予算ではない。

## 検査と残る範囲

`tests/test_cpp_move_argument_facts.py` は、算術・read/size を含む5引数の実評価、scalar データ保持、先行参照の Ready 移送、全保存引数の Ready、準備の成功と資源定理を検査する。unsigned wrap、signed target cast、短絡評価で未実行の不正 read を評価しないこと、実行される不正 read と signed MIN/-1 の拒否も確認する。有限例の実成功は kernel で検証する。

NExpr に含まれない class call/move/assignment の副作用順と実 AST/caller IR への接続、所有 vector の scope 破棄・返却移動、通常操作結果の戻し込み、nested/異種 vector、allocation/resize を含む任意混在寿命列、公開 UF と元コードの相違解消、他の旧ライブラリの検証は残る。
