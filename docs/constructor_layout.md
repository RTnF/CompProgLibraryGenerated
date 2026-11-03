# 実constructor exportのscalarとslot配置

`Proofs/CppConstructorLayout.lean` は実 `CppConstructorFinish.finish` / `NProgram.constructFuel` が正常終了した結果から、callerのprefixと新fieldの配置を取り出す。

`Layout` は、元memoryと同じ長さ・型列を持つprefixと、実calleeから捕捉したscalar valuesの存在を記録する。実結果のmemoryはそのprefixと新field valuesの連結、bindingsは元bindingsと新field bindingsの連結、slotsは元slotsと新vector/scalar locationsの連結となる。scopeとscalar基準量、返されたObjectRefとfield数の対応も保持する。

prefixの値を古いcaller memoryへ置き換えない。constructorが参照引数を通してcallerへ書いた値も、その実結果のまま引き継ぐ。`finish_layout` は実finishの全guardとcapture/transfer/retireを通じて証明し、`construct_layout` はunit constructorの実prepare/body/finish成功へ適用する。成功を入力とする配置定理であり、停止や正常終了の構成は別のconstructor定理を使う。

`tests/test_cpp_constructor_layout.py` は元C++の `Counter(int &outside)` を共通変換器で生成する。fieldはoutside=7を読み、その後bodyがoutside=9を書く。実生成モデルのmemory=[9,7]、bindingsとslots、一般LayoutをLean kernelで検査し、元C++をUBSanで実行して出力 `9 7` と照合する。

[UF constructorからのheap export](union_find_object_construction_export.md)でも、空/既存scalarを持つcallerに対して任意サイズの実constructor結果のslot配置とbinding数を取り出す。Contextのview/slot登録と正常State構成、caller全体の意味対応は残る。
