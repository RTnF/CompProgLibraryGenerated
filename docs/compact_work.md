# compact本体の実仕事量

`Proofs/CppCompactWork.lean` は生成済みPRWと実compact実行の仕事量を接続する。[scalar peakの本体対応](compact_scalar_peak.md)の `body_run` と異なるfuelでの成功結果一意性を使い、`actual_post` は供給された実fuelの結果へQpostW全体を転送する。

元QS/FW、書込み権限、基準量とscopeの条件を保持する。正常実行は元PRWから別途構成し、成功を仮定して停止の代わりにはしない。

`post_work` はscalar仕事量とFWのheap仕事量を合わせ、`step.state.work ≤ initial.work + res.cost + res.wk` を証明する。`post_fresh` は終了時のQS/FWと元scopeからcallee scopeにownerが残らない条件を導き、実scalar finishの仕事量補題へ渡す。

`scalarBudget` は仕事量証明のための補助予算である。元の精密なscalar/heap/全体領域上界を置き換えない。[UFのroot/size](union_find_object_query_amortized.md)で実prepare、compact、本体、finish、restoreを通じて使用する。検査は `tests/test_uf_object_query_amortized.py` に登録する。
