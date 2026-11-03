# UnionFind の履歴 rank

`experiments/verification/data_structure/union_find.hpp` の生成済み全5メソッドと両構築子について、既存の停止用 rank とは別に、親へ進むほど増加する履歴 rank を保持する。C++ の表現や API は変更しない。これは償却解析に必要な不変条件の一部であり、逆 Ackermann 関数による操作列全体の計算量の証明ではない。

`Proofs/UfHistoricalRank.lean` の `ParentRanks` は、各親辺について子の rank が親より小さいことを表す。`RootRanks` は、根の rank が実際の負の size 値から求めた `log2` に等しいことを表す。`History` はその両方である。根でなくなった node の rank はそのまま保持し、結合では勝者の根だけを更新する。

`merge_levels` は、`0 < b ≤ a` のとき `log2 a ≤ log2 (a+b)` と `log2 b < log2 (a+b)` を証明する。`size_gives_growth` はこれを実際の根の size へ結び付け、`merge_preserves` と `unite_history` はサイズ比較による swap を含めて結合後の不変条件を示す。経路圧縮では根の負の値と到達先が保存される既存の `Compressed` 関係を使い、rank は変えない。

`historical_rank_bound` は既存の有効な forest と実 size から、全有効 node の履歴 rank が `log2 n` 以下であることを示す。停止用 rank による根への到達の存在、履歴 rank の単調性、実成分の要素数を組み合わせる。

`Proofs/UfHistoricalTrace.lean` は全5メソッドの既存の実終了証明から履歴 rank の保持を導く。`historical_calls` は任意の有効な有限操作列の実終了と不変条件の保持を示す。`constructed_historical_calls` と `default_historical_calls` は、実構築子の実行からその列へ接続する。成功した実行を前提に置かず、既存の有効な入力・state 条件と操作の添字条件から fuel と結果の存在を導く。既存の数学的・実行時 state の不変条件は維持する。

`tests/test_union_find_historical_rank.py` は一般定理の適用、両構築子、混在する全5メソッドの生成モデルと native UBSan の照合を行う。親辺の厳密増加と根の実 size のどちらかを外した偽の rank が認められないことも検査する。入力・期待結果は既存の Python の操作列を再利用する。

未完了なのは rank 分布、level/index と potential、各実ループの走査・書込み・仕事量の対応、操作列全体への償却解析、公開版の元 API・表現・計算量に関する違反の解消である。停止用の降順 rank を履歴 rank に置換したり、既存の対数時間上界を償却上界として扱ったりしない。これを全旧ライブラリの検証完了とはしない。
