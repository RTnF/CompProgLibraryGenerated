# UnionFind の成分内 rank 分布

`UfHistoricalRank` の点ごとの条件を、各成分内で高い履歴 rank を持つ node の個数の上界で強める。対象 C++、表現、API は変更しない。

成分の要素数を `s`、rank が `k` 以上の要素数を `c`、`t = 2^k` とする。`Budget s c t` は次の両条件を表す。

- `s < t` なら `c = 0`。
- `t ≤ s` なら `c*t + t ≤ 2*s`。

`Population` はすべての根の成分とすべての `k` にこの条件を要求する。`HistoryWithPopulation` は、既存の根 size との rank 対応と親方向の厳密増加も保持する。

`Proofs/UfRankPopulation.lean` は初期 singleton、経路圧縮、実 size による結合でこの条件を保つ。成分の統合では、元の2成分の集合が交わらないことを使って filtered count を加算する。更新するのは勝者の根の rank だけであり、その根が閾値を跨ぐときだけ個数を1増やす。両旧成分が閾値未満だった場合も、既存の個数を無断で捨てず、それぞれ0であることを示す。size の比較と実 root 値を使って、rank の閾値判定を成分 size の判定へ結び付ける。

`Proofs/UfPopulationTrace.lean` は全5メソッド、両構築子、任意の有効な有限操作列の実終了に接続する。構築子からの定理では、新しい個数上界を前提として仮定せず、実初期状態から導く。既存の実 state と数学的不変条件を保つ。

`tests/test_union_find_rank_population.py` は、生成モデルと native UBSan の混在操作列、構築子からの一般定理を照合する。また4-node starで root rank 2、他の rank をすべて1とする反例が、点ごとの `History` を満たしても `Population` を満たさないことを証明する。履歴を証明せず個数上界を仮定しないための検査である。

成分間の集約による全体の rank 分布、level/index と potential、実走査・書込み・仕事量との対応、償却解析は未完了。この成分内の分布上界を、逆 Ackermann 関数による計算量や全旧ライブラリの検証完了として扱わない。
