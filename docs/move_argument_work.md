# ObjectRef呼び出しの引数評価・準備費用

`Proofs/CppMoveArgumentWork.lean` は共通Contextの実引数評価とcallee準備の仕事量を証明する。UF固有の型やfield配置へ依存せず、任意Ty・任意長引数列を扱う。ここでの仕事量は評価器の抽象操作数であり、実測時間ではない。

`eval_work` はscalarOnlyなNExprが実際にevalExpressionで成功するとき、元から結果まで仕事量が減少せず、増分は式のnodes以下であることを示す。既存CppNestedEvalのeval_scalarをContextへ投影する。vector観測や副作用を純粋式として扱わない。

`argumentWork` は値引数の式nodes、vector/scalar参照引数の1である。`resolve_argument_work` は実resolveArgument成功からこの増分上界を導く。型・参照mode・captureの失敗分岐も分け、成功を無条件に仮定しない。

`resolve_arguments_work` は実resolveArgumentsの左から順の評価に沿い、仕事量の単調性とargumentsWork（各引数の費用和）の上界を示す。値引数についてscalarOnlyを要求し、参照引数には不要な式条件を付けない。空列と型/個数不一致も扱う。

`prepare_work` は実prepareArgumentsの成功を分解し、resolveの費用とprepareSavedの実加算費用を合成する。

```
work(source) ≤ work(prepared)
work(prepared) ≤ work(source) + argumentsWork(arguments) + 1 + parameters.length
```

この成功を前提に取る効果定理は、既存の正常call/引数構成定理が得た実preparedへ適用する。呼び出しの停止証明を成功仮定で置き換えない。

`tests/test_cpp_move_argument_work.py` は元move後Contextでfield読取り・算術・literalの実resolveとprepareを構成し、5式node/3引数の増分上界9を導く。i32のvector投影を使いつつunsigned32式のwrapと増分3、signed32 overflow拒否、引数個数/参照mode不一致を検査する。[UF列全体の費用](union_find_object_trace_work.md)がこの一般定理を利用する。
