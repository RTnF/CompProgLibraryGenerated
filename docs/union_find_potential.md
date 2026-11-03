# UnionFind の node potential の基礎

`Proofs/UfPotential.lean` は償却解析の準備として、結合時の rank 増加、Ackermann 関数の逆関数、非根 node の level/index と potential を定義する。対象 C++、表現、API は変更しない。操作列全体の償却時間はまだ証明していない。

サイズ比較で `0 < a`、`b ≤ a` のとき、`log2(a+b) ≤ log2(a)+1` を示す。実 root size と `RootRanks` を使い、結合で勝者の根だけを更新した rank が、各 node で旧 rank 以上・旧 rank+1 以下になることを証明する。

Ackermann 関数は、ローカルの Mathlib/Computability/Ackermann.lean と同じ2引数の再帰式を使う。

- `ack 0 n = n+1`
- `ack (m+1) 0 = ack m 1`
- `ack (m+1) (n+1) = ack m (ack (m+1) n)`

新しい Computability import は加えない。左右の単調性・増加性と非有界性を証明し、`alpha n` を `n < ack m 1` となる最小の `m` とする。`diagonalAlpha n` を `n < ack m m` となる最小の `m` とし、`alpha n ≤ diagonalAlpha n+2` を証明する。任意の遅い関数を名前だけ α と呼ばない。

node rank を `r`、親 rank を `p` とする。`level n r p` は `alpha n` 以下で `ack k r ≤ p` となる最大の `k`、`index n r p` は level の関数を `r` から反復して `p` 以下に留まる最大の反復数（上限 `r`）である。有効な正 rank の親辺 `0 < r < p ≤ n` で `level < alpha n` と `1 ≤ index ≤ r` を示す。親 rank の増加に対し level は非減少、level が同じなら index も非減少となる。

`nodePotential n r p = (alpha n-level n r p)*r-index n r p` と定義する。有効な正 rank では減算が切り捨てを起こさないこと、上界 `alpha n*r`、level または同 level の index の増加による厳密減少、親 rank 増加に対する非増加を証明する。rank 0 の node は potential 0 となる。

`compression_node_potential_all` は既存 `Compressed` 関係に接続する。実経路の親から根への到達、履歴 rank の単調性、根の rank 上界を使い、rank 0 を含むすべての圧縮対象 node の実更新と potential 非増加を示す。`root_call_potential` は有効な state と添字から実生成 root program の終了を導き、結果の `Represents` と各更新 node の性質を保持する。成功した呼出しを入力前提として仮定しない。

`tests/test_union_find_potential.py` は逆関数の境界、一般の potential 補題、実 root 呼出し定理を適用し、既存の全5メソッドの生成モデル/native UBSan 混在列も照合する。

未完了なのは、全 forest の potential、結合によるその増加、探索経路で potential 減少へ課金できない node 数の上界、実2-passループの走査・書込み・prepare/finish仕事量との対応、任意列への集約である。これらを示すまでは償却 α 時間と扱わない。caller 資源、公開版の違反、他の旧ライブラリの検証も残る。
