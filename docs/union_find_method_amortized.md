# UnionFind 全5メソッドと操作列の償却仕事量

`Proofs/UfMethodAmortized.lean` は、元の API を持つ候補 C++ の生成済みメソッドと両構築子について、実行の終了・`Represents`・履歴 rank を保ち、任意の有効な有限操作列の仕事量を抑える。C++ ソースや既存の定理は変更していない。

操作前後の仕事量を W、forest potential を Φ、要素数を n とすると、各メソッドについて `Wout+91*Φout ≤ Win+91*Φin+C*(alpha(n)+1)` を示す。定数 C は root が324、size が344、same が587、unite が769。num_groups は potential を保ち仕事量の増分が高々41となる。これは既存の scalar/storage 操作数 `NState.work` の上界であり、実測の CPU 時間ではない。

`same_body_paths` と `unite_body_paths` は、実生成本体の2回の inlined root の経路を個別に記録する。1回目には元の Valid の正確な depth、2回目には1回目の実圧縮後の Valid の正確な depth を使う。元の停止用 rank は燃料の存在に使い、2回目の仕事量は圧縮後の実経路長で抑える。`Trace.length_le_rank` と `depth_le_rank` が両方の実行に十分な燃料を導く。

`same_call_ready_paths` と `unite_call_ready_paths` はこれを prepare/finish を含む実 `callFuel` へ接続する。経路長を L1、L2 とすると、仕事量増分は same が `91*L1+91*L2+223`、unite が `91*L1+91*L2+405` 以下。結果、scalar memory、参照、更新後 vector の対応を保つ。unite はサイズによる swap、同根の場合、実 count 更新も既存の意味対応へ接続する。

各経路に既存の `Trace.forest_budget` を適用して中間 potential を相殺する。unite では実サイズ結合による potential 増加高々 alpha(n) を追加する。`size_work_trace` は1回の探索の仕事量を `91*L+162` で抑え、size の実返値を成分の大きさへ対応させる。

`amortized_step` は全5メソッドを統一する。`amortized_calls` は有効な m 個の任意の操作列について、生成済みメソッドを呼ぶ `runCalls` の終了と結果を存在証明し、次を示す。

```
Wout + 91*Φout ≤ Win + 91*Φin + 769*m*(alpha(n)+1)
```

`constructed_amortized_calls` は実サイズ指定構築子の仕事量も含めて、上界を `Wcaller+en.nodes+n+30+769*m*(alpha(n)+1)` とする。`default_amortized_calls` は実既定構築子を含め `Wcaller+12+769*m*(alpha(0)+1)` とする。初期 potential は0から導き、成功実行・初期仕事量上界・経路予算を入力前提に要求しない。n=0 で許されるのは num_groups のみで、n=1 の根や rank 0 も含む。

`diagonal_work_unit` は操作列の項を `2307*m*(diagonalAlpha(n)+1)` 以下とする。alpha は既存の標準2引数 Ackermann 再帰から定義した逆関数。固定引数と対角逆関数の既存の比較を使い、alpha(0)=alpha(1)=0 によって実仕事量の上界が0にならないよう正の単位を含める。ghost rank、potential、Ackermann 関数は C++ の実行中には計算しない。

`tests/test_union_find_method_amortized.py` は一般の操作列・両構築子定理を適用し、深さ3の木で same(7,7) と unite(7,7) の2回目の探索が長さ1になる場合の実生成モデルの仕事量と圧縮結果を確認する。size/num_groups の仕事量、全5メソッド混在列、元の参照とメモリの保持も検査する。候補 C++ は同じ列、サイズ swap、n=1、既定構築子を UBSan で実行する。

この証明は候補の生成済みメソッド／構築子の仕事量までを扱う。任意の外側 caller への全資源の接続、copy/move/assignment などの未対応義務、公開版の表現/API/計算量違反の解消、他の旧ライブラリの検証は残る。候補の公開昇格や全 experiments の検証完了は主張しない。
