# UFメソッド列の準備費用を含む仕事量

`Proofs/UfObjectTraceWork.lean` は[任意長UFメソッド列](union_find_object_trace.md)に、[実引数評価・準備](move_argument_work.md)の費用を加える。元ObjectRefと実currentBufferに対応するStateを使い、実際に生成されたNProgramのparametersと引数列を照合する。

## 各呼び出しの費用

`arity` は外部添字の個数で、root/sizeが1、same/uniteが2、groupsが0である。元receiverのvector参照、counter参照、size値読取りに外部literalを加えた実引数費用は3+arity、実parameter数も3+arityとなる。

`arguments_pure` と `arguments_cost` はこの実引数について証明する。`step_work` は既存Stepが持つ実prepareArgumentsとbodyWorkを合成し、次を示す。

```
work(out) ≤ work(source) + (7 + 2*arity(op)) + bodyWork(state.rank, op)
```

7+2*arityには参照の捕捉、size読取り、外部literal評価、callee準備が含まれる。getterの合計は10、rootは91*rank(a)+90、sameは91*rank(a)+91*rank(b)+192、sizeは91*rank(a)+110、uniteは91*rank(a)+91*rank(b)+354以下である。古いprepared Contextを次callの基準値へ流用しない。

## 列全体の合成

`Charges` は各中間Stateと実Stepを持ち、その時点の準備費用とbodyWorkの和を記録する。`history_work` は既存Historyに沿ってこの和を構成し、最終仕事量が初期仕事量+charge以下であることを示す。各Stepは実callの成功・返却意味・状態保持を持ち、Chargesだけで架空の実行を費用の証拠にしない。

`execute_work` は元Stateと各添字の範囲条件から、正常終了するfuel列、結果列、最終State、全History、Chargesと列全体の上界を構成する。各callの成功や完成済み中間stateを入力にしない。空列ではcharge=0となる。

この和は各中間rankに依存する。logやαの償却上界を新たに証明したものではなく、rank/forestPotential履歴との接続が必要である。式や履歴は証明情報であり、C++の物理追加領域とは数えない。peakの列全体の上界、元caller/constructorからの初期State、返却値に依存する操作選択、寿命操作との混在も残る。

## 検査

`tests/test_uf_object_trace_work.py` は全5methodの混在列、2成分からのunite列、任意自然数回のrootについてexecute_workを適用する。任意の元Stateからgetterが正常終了し、元counterを返して増分10以下となることも一般証明で検査する。元move後のrootではrank(3)=2から増分272以下を導く。[任意の実成功scriptへの転送](union_find_object_trace_actual.md)により、構成したfuel以外の成功実行にも同じ結果の証明を接続する。元C++、既存生成照合/native検査、公開UF相違と他旧ライブラリの作業範囲は維持する。

[root/sizeの実経路長と償却評価](union_find_object_query_amortized.md)を追加した。任意rankに依存する本ページの全5method列のChargesは保持し、混在列全体のα償却接続は引き続き残る。

[全5method列のαpotential評価](union_find_object_amortized.md)を追加した。元のrank依存Chargesも保持し、数学的Historyを持つ正常Stateからは初期potentialと操作数に基づく上界を併せて使える。
