# 旧UF same・sizeのContext call証明

`Proofs/UfCompactSameBody.lean` / `UfCompactSameCall.lean` と `UfCompactSizeBody.lean` / `UfCompactSizeCall.lean` は、元candidateの生成済みbodyを[callee binding整理を使うcall](move_call_bindings.md)へ接続する。[rootの正常call](union_find_compact_root.md)と同じContext準備・body実行・finish・戻し込みを使用する。

## same

正常条件はForest、signed32の要素数と範囲内のa/b、元field値に対応するQS、実vectorのFW、権限・baseline・scope、caller memoryのprefix、実prepare/compactである。元body_correct→soundWから2回の経路圧縮・更新Forest・実停止を導く。

same_callは返却値がr1=r2なら1、異なれば0であることと、r1=r2が元配列でのConnectedと同値であることを示す。最終Contextのvector payloadは証明した圧縮結果に一致し、callerのscalar memoryは保持する。body/finish/restoreの成功を入力仮定にしない。

body workは初期work＋91×rank(a)＋91×rank(b)＋180以下、call終了後は準備後work＋91×rank(a)＋91×rank(b)＋181以下である。

## size

size_body/size_callはForestに加えて既存Weights条件を使う。負のroot値wの符号反転−wが型範囲内であり、返却値に一致すること、rootまでの経路圧縮、更新後Forest/Weights、実停止を証明する。callerのscalar memoryを保持し、最終Contextのpayloadは圧縮結果に一致する。

さらに元クラスのValidがある場合、返却値は元componentの要素数と等しく、更新後も同じgroups/rankのValidを保持する。これはValid.size_value/component_eq_membersと圧縮後のValid保持から導く。Weightsだけから成分数の意味を主張しない。INT_MINの符号反転はWeightsを満たさず、正常定理の対象にしない。

body workは初期work＋91×rank(a)＋100以下、call終了後は準備後work＋91×rank(a)＋101以下である。

## 資源と状態

両methodのbody scalar budgetはrootと共通のmax(max初期scalarPeak初期peak)(prefix長＋80−scalarBaseline)。heap上界はmax初期heapPeak(初期liveSpace＋1−heapBaseline)で、既存領域をbaselineにした場合は新たなheap peakが過去peakとの最大を取って1以内となる。合成peakを実run_growsとfinish countersへ接続する。準備work/peakは既存prepareArguments_resourcesを使う。

一般finish_memoryとcall_of_bodyに、実callee memoryのcaller長prefixをhigh-levelへ戻す一致を追加した。root/same/sizeのscalar memory保持は元bodyのprefix保持から導く。参照先の更新と既存要素grant・世代の保持は一般restoreの証明を使う。

`CppMoveCallBindingsReady.gather_ready/compact_ready` は、formal vector indexが実binding表内にある条件から整理の実成功を構成する。成功済み結果を入力仮定にしない。

## 検査と残件

`tests/test_uf_compact_queries.py` は元UFをclass moveした状態で一般same_call/size_callを適用する。sameの連結・非連結、圧縮payloadとcounter保持、元grantの更新と旧領域参照の失効維持、燃料0を照合する。sizeは返却4、一般Validからのcomponent要素数との一致とValid保持を適用し、不正なINT_MIN重みのcallがfaultとなることもkernel確認する。

元caller ASTからのFieldDecl/ObjectRef、引数準備・QS/FWの一般生成、unite/countと償却証明・任意混在列、構築/返却/destructor、割当/resize/nested/異種vectorは未完了。公開UFの既存相違と全旧ライブラリのverifyも残る。

[unite/num_groups](union_find_compact_mutation_count.md)も同じcall経路へ接続した。uniteのcounter更新とgetterのraw i32範囲を保持し、元caller生成・償却/混在列への一般接続は継続する。
