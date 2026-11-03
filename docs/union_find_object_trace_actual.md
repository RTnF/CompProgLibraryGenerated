# 実際に成功したUF呼び出し列への証明転送

`Proofs/UfObjectTraceActual.lean` は[元ObjectRef呼び出し列](union_find_object_trace.md)について、[異なるfuelの結果一意性](move_call_unique.md)を使い、任意の供給された成功実行へ不変条件・意味・仕事量の証明を移す。既存のexecute/execute_workによる正常終了の存在構成も維持する。

## 呼び出し単体

`invoke_success_mono` と `invoke_unique` はObjectRefの実引数展開を確認し、共通compact callFuelの定理へ接続する。不正なscalar slots形による展開失敗は省かない。

`actual_step` は元State、操作の添字条件、供給されたfuelでの実invoke成功から、同じ結果Contextに対応する次Stateと、そのfuelに対応するStepを構成する。既存stepが構成する成功runとの結果一意性を使い、実runの証拠を供給されたfuelのものへ置き換える。Stepのsize保持、実payload/counterについてのEffect、実prepareとbodyWork上界も維持する。

## 列全体

`run_success_mono` は列の各fuelへ同じextraを加えても、結果Contextと返却列が変わらないことを示す。各callの実結果を次のcallへ渡す。

`run_unique` は二つのscriptの操作列（fuelを取り除いた列）が等しく、両方の実行が成功するとき、最終Contextと返却列が等しいことを示す。各callの結果一意性とtailの帰納で証明する。fuel列自体が同じである必要はない。

`actual_work` は元Stateと初期vector長に対する添字条件、供給されたscriptの実成功から、次State、全History、Charges、初期仕事量+chargeの上界、返却数とsize保持を導く。execute_workが構成する正常列と実scriptをrun_uniqueで同定し、同じ結果へ証明を転送する。意味や費用を別の結果stateへ流用しない。

成功runを入力に取るのはこの転送定理である。正常終了の存在は既存execute_workが元Stateから構成する。両者を合わせることで、構成したfuelだけに限定せず、実際に成功したfuel列を扱う。

## 検査と残件

`tests/test_uf_object_trace_actual.py` は全5method混在列の正常終了を構成し、各fuel+17の実行へState/History/Charges/仕事量上界を転送する。空列、元move後sourceの弱いgetter（空vector、size4/counter1）、rootのfuel+19の実成功とactual_stepからの圧縮の意味も確認する。getterでは任意の成功fuelの結果一致も示す。

[列全体のheap上界](union_find_object_heap_peak.md)へ接続した。スタックを含む全peak、rank/償却履歴、元caller/constructorからの初期State、評価順/副作用、copy/move/return/destructorが混在する寿命列、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは引き続き未完了である。
