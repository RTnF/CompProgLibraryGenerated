# 元ObjectRefに対応するUF状態の保持

`Proofs/UfObjectState.lean` と `Proofs/UfObjectStateMethods.lean` は、元ObjectRefの正常配置・実currentBuffer・UF Valid・heap条件を束ね、全5methodの実行後も同じObjectRefに対応する状態を構成する。[元ObjectRef正常call](union_find_object_methods.md)と[実結果payload](move_call_payload.md)を用いる。

## 通常状態の不変条件

`State s object` は次の条件を持つ。

- Receiverの実field配置とcounter/size addressの分離。
- 元headerの実currentBuffer、rank、現在payloadと実counter値に対するUF Valid。
- size field=実vector長。
- readable、Unique/OwnsAll/AllocationsValid、型のsizeLimit。
- scalar baselineが実準備prefix内であることと、元projected scopeの上界。

rankは証明用の情報で、C++の追加領域へ数えない。constructor/callerからこの状態を構成する一般接続は別途必要である。moved-fromで元sizeが空vector長と異なる状態はこの通常状態に含めず、既存の弱いgetter定理で引き続き扱う。

## 一般の状態遷移

`transition` は、既存の正常call定理が構成した実run、結果memoryの実field値、結果payload/UF Valid/長さから結果Stateを構成する。heap・配置条件はcallの効果定理から引き継ぐ。rank/counter/size/itemsの対応も返す。

成功runを入力に取るのはこの効果合成部分であり、各stepの正常終了は元Stateから導く。結果dataとして古いbufferを置き続けず、実currentBufferとpayloadの一致を使う。

## 全methodの保持と既存post

`root_step` / `counter_step` / `same_step` / `size_step` / `unite_step` は元Stateから正常callを構成し、結果Stateを加える。添字を取るmethodには元配列内性とpure式の型/denote条件を与える。

root/same/size/getterではcounter・size・rankを保つ。root/same/sizeは圧縮後payload、getterは同じpayloadへStateを引き継ぐ。sizeのWeightsは元Validから導く。

uniteでは元counter値に対応するValidを使い、countAfterと新rankのValidを結果memory/payloadへ結び付ける。counter更新cellと、分離されたsize cellの保持を導く。結果counterの型妥当性は新Validのcount_rangeから得る。新しいStateはその実counter値と数学的groupsを一致させる。

各stepの結果には元の正常callの全postをそのまま残す。実prepared/initial/FW、返却値・圧縮・成分情報・Valid、work/peak、memoryとpayloadを落としてStateだけの存在へ置き換えない。これらは従来の1call資源上界であり、履歴を含む償却計算量への一般接続は残る。

## 検査と残件

`tests/test_uf_object_state.py` は元move後ObjectRefで通常Stateを構成し、全5stepを適用する。rootの結果Stateと長さ保持から次の入力条件を導いてroot→rootを実行する。さらに別成分unite→size→same→getterを結果Stateでつなぎ、最終counter=1・size=4を導く。固定fuelや成功済み中間stateを証明の入力にしない。元C++は変更せず、既存native照合を維持する。

[任意長method列の一般実行と意味の履歴](union_find_object_trace.md)を追加した。列全体の資源合成、元caller/constructorからの正常配置、償却・copy/move/return/destructorとの任意混在寿命列、caller ASTと評価順/副作用、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは未完了である。
