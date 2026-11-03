# 2つのUFへの任意の交互操作列

`Proofs/UfObjectPairTrace.lean` は、[識別情報と独立性](union_find_object_identity.md)を保つPairから、左右どちらのUFにも全5methodを呼ぶ任意の有限操作列を正常実行する。

Actionは左右と元Operationを持ち、有効添字は操作対象の要素数で判定する。PairStepは元の実Step（正常終了、返却意味、仕事量）と、非対象側のrank・親配列・成分数・size保持、両size保持を記録する。次のPairにも両正常StateとApartを保持する。

runは元の実invokeを順に使う。Historyは全中間PairとPairStepを記録し、executeは任意有限有効Action列からfuel付きscript、実正常終了、返却数一致、両size保持、全Historyを同時に構成する。成功実行を仮定するだけの定理ではない。

`tests/test_uf_object_pair_trace.py` は圧縮前の鎖を持つUFと4 singletonのUFの同居で、unite(0,1)により成分数4→3、その後別UFのroot(3)を実行しても先の配列と成分数3を保持することを確認する。任意有限有効列と、左右のunite/root/size/same/getterを混在させた8操作列も検査する。

境界では空header（placeholder owner2）のUFと空buffer（owner0）のUFを同居させ、空列、任意有限有効列、両側への任意回数getterを検査する。0要素へのroot(0)は範囲外となる。

元constructorからのPair/Apartと任意有限列は[構築からの接続](union_find_object_constructed_pair.md)で構成する。列全体の償却/peak上界、読み取り専用copy元、元caller ASTの評価順・副作用・再番号付け、寿命操作混在、公開UF相違と他旧ライブラリは未完了である。
