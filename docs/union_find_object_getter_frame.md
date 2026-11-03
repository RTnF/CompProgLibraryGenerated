# UF getterと共存するUFの状態保持

`Proofs/UfObjectGetterFrame.lean` は実num_groups呼出しが全buffer内容とscalar memoryを保ち、同じContextにある別の正常UF Stateも保持することを証明する。

`storage_snapshot` は実prepare/compact/body/finish/restoreを分解し、[scalar return](scalar_return_frame.md)のframe定理を適用する。正常Stateのcontext範囲からcallee scopeのfreshnessを導き、projectされたforestと全storage objectsの一致を得る。対象UFだけの値保持から別bufferの保持を推定しない。

`scalar_snapshot` は正常getterの構成的実行とfuel一意性から、任意の同じ正常実行のscalar memoryを保持する。`other_state` は任意の共存する正常UFのcurrentBuffer lookupとfieldsをこのsnapshotから再構成し、rank・親配列・成分数・sizeを保つ。対象と別UFが異なることは要求しない。

`getter_pair_step` は実getterの正常終了、対象と別UF両方の正常State・内容保持、仕事量増分10以下を同時に構成する。

`tests/test_uf_object_getter_frame.py` は実sized constructorで作った任意n<2^31のUFと既存の圧縮済みUFに交互にgetterを呼び、返却1/n、両親配列/成分数保持、2回の仕事量増分20以下を確認する。空headerの同一objectを両方のStateとして渡す境界も検査する。

元C++と公開版の変更はない。更新methodの別UF保持は[全methodの非干渉](union_find_object_values.md)へ接続する。const viewの呼出し条件、構築直後の非alias条件の一般導出・交互更新列、寿命操作混在、元caller ASTの評価順・副作用・再番号付け対応、公開UFの相違と他旧ライブラリは未完了である。
