# 元constructorから独立した2UFと交互操作列を構成

`Proofs/UfObjectConstructedPair.lean` は、元UFの実constructorと既存正常Stateから、新旧UFのPairとApartを構成する。異なるObjectRefだけを理由に非aliasを仮定しない。

`apart_initialized` は実Initialized/Layoutを使う。元counter/sizeのaddressは元memory内、新counter/sizeは元memory末尾とその次になる。新allocation ownerは元表長となり、既存owned headerのownerはその範囲内、empty headerのplaceholder ownerは構築後表長+元header IDとなる。いずれも新allocationとは異なる。`receiver_same` / `state_owner` / `header_bound` でこの識別情報を実receiver/currentBufferから取り出す。

`construct_sized` / `construct_default` は実constructor正常終了、旧UFのparents/rank/counter/size保持、新singleton parents、両正常State/Apartを持つPair、HeadersLiveを同時に構成する。サイズ指定は任意n<2^31であり、0要素と元の最大intサイズを除外しない。defaultは元どおり0要素となる。

`construct_sized_trace` / `construct_default_trace` はここから[任意の有効な交互操作列](union_find_object_pair_trace.md)へ接続する。実constructor→実method列の正常終了、全中間Pair/Stepの意味と仕事量、返却数、両最終size保持を得る。列全体の償却/peak合成の代替とはしない。

`tests/test_uf_object_constructed_pair.py` は、move後の圧縮前UFと任意サイズの新UFについて両constructorと任意有限有効交互列を検査する。既存empty headerではplaceholder ownerを更新して新allocationと区別し、sized/defaultとdefault直後の任意有効交互列を確認する。

元C++や公開版の変更はない。元caller ASTの評価順・副作用・再番号付け、読み取り専用copy元と寿命操作の混在、両UF列の償却/peak合成、公開UFの相違と他旧ライブラリは未完了である。元UFのnum_groupsはnon-constであり、const getter不足を元APIの欠落とは扱わない。
