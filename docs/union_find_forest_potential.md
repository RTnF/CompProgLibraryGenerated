# UnionFind の全 forest の potential

`Proofs/UfForestPotential.lean` は各 node の potential を全 node について合計する。根では `alpha(n)*rank`、非根では既存の `nodePotential` を使う。これは potential の増減の証明であり、実行仕事量や償却時間の上界ではない。対象 C++、表現、API は変更しない。

`forest_zero` は初期 rank がすべて0のときの合計0を示す。`forest_compressed` は実 `Compressed` 関係から、対象外 node と根を保持し、更新 node では rank 0 も含めた既存の非増加を使って全体の非増加を示す。

`forest_linked` は実サイズ比較による結合で増加が高々 `alpha(n)` となることを示す。勝者の rank 増加は高々1、敗者は根から非根になっても増加せず、他の node は親 rank の変化で増加しない。新しい forest と履歴 rank の有効性は既存の結合定理から導き、前提に仮定しない。勝者の一度分だけ増加を加えるため、node 列の重複がないことも使う。

`potential_step` は全5メソッドの生成済み program の実終了と実更新へ接続する。`potential_calls` は任意の有効な有限操作列で結果の `Represents`、履歴 rank、長さと回答数を保ち、合計の増加を各 `unite` に割り当てた `alpha(n)` の和で抑える。`potentialAllowances` と `allowance_count` はこの和が `unite` 呼出し数と `alpha(n)` の積になることを示す。同じ根への `unite` も安全な上界として数える。この割当てを CPU 時間と扱わない。

`constructed_potential_calls` と `default_potential_calls` は両実構築子の初期値0から接続する。成功した実行や potential 上界を入力前提として仮定しない。

`tests/test_union_find_forest_potential.py` は深さ3の8-node木を作る7回の結合、経路圧縮、全5メソッド、元の参照とメモリの保持を生成モデル/native UBSanで照合する。2-node結合後の potential が実際に1となる例も確認し、全演算で非増加と誤って扱わない。

root の経路課金・正確な depth・prepare/finish を含む実仕事量への接続は `docs/union_find_path_amortized.md` へ進んだ。全5メソッドと操作列の実仕事量の償却解析は `docs/union_find_method_amortized.md` を参照する。caller 資源、公開版の違反、他の旧ライブラリの検証も残る。
