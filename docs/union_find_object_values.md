# UF全methodと共存する別UFの保持

`Proofs/UfObjectValues.lean` は、root/same/size/unite/num_groupsの実compact Context呼出しから、別UFのbuffer・scalar fields・正常状態を保持する。元C++や公開版を変更しない。

`operation_ready` は正常UFと有効添字から元literal引数の型・評価条件を構成する。`other_payload` は元receiverから実prepare/compactを構成し、初期FW/QSのTargetを[既存のループ効果証明とcompact接続](compact_values.md)へ渡す。全5methodの元生成bodyが対象fragmentであることをkernelで確認し、対象owner以外の全lookupを保つ。FW単独から他buffer保持を推定しない。

`scalar_frame_exists` は元methodの構成的正常実行から、成分数field以外のscalar cellを保持する。uniteでは元updatedMemoryを使い、実併合なら成分数だけを更新し、同一成分ならmemoryを保つ。`scalar_other` はfuel一意性で任意の同じ正常実行へ転送する。

`other_state` は、別UFのdata ownerが異なり、そのcounter/sizeのaddressが対象counter addressと異なる条件から、別UFの親配列・rank・成分数・sizeと正常Stateを再構成する。ObjectRefが異なるという条件だけで所有やfieldの非aliasを仮定しない。`pair_step` は元Stepの実正常終了・意味・仕事量証明を保ち、別UF保持を同時に構成する。

`tests/test_uf_object_values.py` は圧縮前の鎖を持つ4要素UF（成分数1）と4 singletonのUF（成分数4）を同じContextに置く。任意の有効operationでの両方向の保持、unite(0,1)による対象成分数4→3と別UFの親配列/成分数1/size4保持を確認する。

交互に更新する任意有限列は[PairTrace](union_find_object_pair_trace.md)へ接続する。構築直後からの非alias条件は[両constructorからのPair](union_find_object_constructed_pair.md)で構成する。列全体の償却/peak上界、const view、元caller ASTの評価順・副作用・再番号付け、寿命操作混在、公開UFの相違と他旧ライブラリは未完了である。
