# 旧UF rootのContext call証明

`Proofs/UfCompactRootBody.lean` と `Proofs/UfCompactRootCall.lean` は、旧APIを保つ候補UnionFindの生成済みroot bodyを、[callee binding整理を使うcall](move_call_bindings.md)へ接続する。元ソースは `experiments/verification/data_structure/union_find.hpp` であり、公開UFの既存相違はまだ解消していない。

## 正常入力と結果

正常条件は、parent配列のForest、要素数がsigned32に収まること、aが配列内であること、生成bodyのscalar fieldsに対応するQS、実vectorを表すFW、権限・baseline・scope条件である。call側では実引数準備とcompactの対応、caller memoryがprefix Pへ保存されること、元contextsとOwnsAllを要求する。最終body実行・finish・restoreの成功は仮定しない。

root_bodyは既存UfFieldsRoot.body_correctとVecWrite.soundWを用い、正常条件から実runFuelの終了、返却root、経路圧縮Compressed、更新後Forest、元scalar prefix保持を導く。

root_callはこれをcall_of_bodyへ渡し、実callの終了・返却と、最終high-level Contextを射影した実vector payloadが圧縮結果に一致することを示す。元rootの型妥当性は、返却rootが元配列内にあることから導く。元要素grant/世代の扱いは一般restoreの保持証明を利用する。

## 資源

bodyのworkは初期work＋91×rank(a)＋80以下、finish後のworkは準備後work＋91×rank(a)＋81以下である。準備workは別途prepareArguments_resourcesで実引数評価と接続する。rankはForestの下降尺度であり、この定理だけで反復操作列のα償却時間を主張しない。

prefix長をp、scalar baselineをB、整理後初期状態をSとすると、body scalar peakの上界SBはmax(max S.scalarPeak S.peak)(p＋80−B)である。heap peakの上界HBはmax S.heapPeak(S.liveSpace＋1−S.heapBaseline)。既存領域をheap baselineに置けば、新たなheap peakは過去peakとの最大を取って1以内となる。

call終了時のscalar peakはmax(max callerScalarPeak SB)(caller scalar live)、heap peakはHB以下。合成peakはmax(max callerPeak(SB＋HB))(終了scalar上界＋HB)以下である。これらは既存NoResizeの実run_peak/run_growsとfinish counter式へ接続している。

## 検査と残件

`tests/test_cpp_move_call_bindings.py` は元UFをclass moveした後にrootを呼ぶContextを構成し、一般root_callへForest/QS/FW/引数・prefix条件を適用する。経路3→2→0の圧縮結果、返却0、move前の要素grantによる更新値読取り、旧代入先参照の失効維持、燃料0をkernel確認する。元candidateのC++動作は既存GCC13.3/ASan/UBSan検査でも照合する。

QS/FWと引数準備の条件を任意の元caller ASTから自動生成する接続、他methodのこのcall経路への一般接続、償却証明と任意混在列、公開UFの経路圧縮・カウンタ・入力範囲の既存相違解消は残る。全旧ライブラリのverify完了を意味しない。

一般callのmemory対応を強め、root終了後もcaller scalar memoryを保持することを明記した。[same・sizeの正常call](union_find_compact_queries.md)もこの対応を使用する。
