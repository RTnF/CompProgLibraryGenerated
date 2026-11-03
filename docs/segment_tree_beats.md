# segment_tree_beats

`cp::SegmentTreeBeats` は Segment Tree Beats（`experiments/library/cpp/segment_tree/segment_tree_beats.hpp`、tjkendev の実装ベース）である。配列 `a`（`long long`）に対して、区間 chmin `chmin(a, b, x)`、区間 chmax `chmax(a, b, x)`、区間加算 `add_val(a, b, x)`、区間代入 `update_val(a, b, x)`、区間最大 `calc_max(a, b)`、区間最小 `calc_min(a, b)`（いずれも半開区間 `[a, b)`）を持つ。構成子は `SegmentTreeBeats(const std::vector<long long>& a)`。和は持たない（その代わり `INF` = 4×10^18 まで積める）。

木は `[lo, hi)` を中点で分ける。木の節点 `k` の子は `2k+1`、`2k+2`。節点は最大値・次大値・最大値の個数、最小値・次小値・最小値の個数、区間の長さ `len`、保留中の加算 `ladd`、保留中の代入 `lval`（保留なしは `inf`）を持つ。chmin は、節点の次大値が `x` より小さいとき（`smax < x`）その節点の最大値だけを `x` にして止まり、そうでなければ子へ押し下げて再帰する（chmax は対称）。

## 前提

- 構成子: `1 <= a.size()`、`8 * a.size() + 8 < 2^31`（ベクタの確保長を計算する `int` の演算も範囲内）、要素は `-INF < v < INF`（`INF = 4000000000000000000`）。空の配列は扱わない。
- 操作: `0 <= a, b < 2^31`（範囲外の `b` や `a > b` は何もしない区間として扱う）。`x` は `-INF < x < INF`。
- 値の安全性: 区間加算で、押し下げの途中の値と節点が持つ値が `±INF` に近づかないこと。Lean の定理では、操作ごとの木の述語（`chminSafe`、`chmaxSafe`、`addSafeRec`、`setSafeRec`、`calcSafe`）として前提に置く。これは「操作で触れる節点の値と保留中の加算の和がすべて `-INF < v < INF` に収まる」ことを意味する。満たさない入力は扱わない。
- 最大値と最小値の返り値は、空の区間で `-INF`（`calc_max`）、`INF`（`calc_min`）。

## 元のソースからの変更

- 再帰をやめ、明示スタック（`st_k`、`st_l`、`st_r`、深さ 128 以下）で走査する。訪れた節点を `ent` に積み、走査のあとに `ent` を逆順に `update` する（元の再帰の帰りがけの `update(k)` と同じ順）。結果は元の実装と同じ（`tests/segment_tree_beats.cpp` で元の実装の振る舞い＝素朴な配列と照合）。
- 木の大きさは 2 冪に切り上げず、`n` 要素をそのまま中点で分ける（葉は `n` 個、節点番号は `8n+8` 未満）。区間の端 `lo[k]`、`hi[k]` を配列で持つ。元の `n0`（2 冪）と、padding の葉（`-INF`/`INF`）は持たない。
- `inf` と `n` をメンバーとして持つ（元は大域の `INF` マクロ）。
- 節点の更新（`update_node_max`/`update_node_min`/`push`/`update`/`add_all`/`update_all`）は、条件分岐の中で書き込まず、条件を `g` や `leaf` の変数に落とした分岐なしの形に書き直した（検証の枠組みの制約）。意味は元と同じ。
- 構成子は、`vector<long long> a` を値渡しではなく `const` 参照で受ける。`chmin`/`chmax`/`add_val`/`update_val` は `apply_op`、`calc_max`/`calc_min` は `calc_op` に共通化した。
- 元の機能（6 つの操作、構成子）はすべて残してある。

元の入力範囲には未解消の縮小がある。元の4*nの確保と2*n0までの木に対し、公開版は未使用節点・葉の子への参照を安全にするため8*n+8を確保するが、計算はintのままである。n=2^28では元のサイズ計算と添字がintに収まり、新しい確保長は収まらない。8*n+8<2^31を前提に置くだけでこの違反を解消したとは扱わず、サイズ/子添字の型や制御フローと証明を改善する作業を残す。`tests/lean/beats_capacities.lean` は巨大配列を実確保せず、この算術境界を確認する。

## 結果（`Proofs/SegmentTreeBeatsCall.lean` の条件付き定理）

2026-11-02: 旧構築Callと容量分離版構築Callの依存閉包6824宣言は、固定版nanoda・2threads・標準16MiB stackで独立検証に成功した。仕事量上界のインライン算術証明を、抽象的なcost/boundを扱う小補題へ分離したもので、定理の前提・結論・上界は同じ。`tests/test_beats_capacities.py` で両Callを再検査する。これは全件gateや元の全API・全入力範囲の検証完了を意味しない。

木の表現 `BRep n L ys b t H` は、15 本のベクタ（節点の配列）の内容 `b`、木 `t`（節点の値と保留中の作用を持つ）、その各節点の格納 `H`、配列 `ys` が対応していることを表す（不変条件: ベクタの長さが `L`（=`8n+8`）以上、節点の番号が `L` に収まる、`len` が区間の長さと一致、値が有効、`t` が `ys` を表す `Inv`、など）。

実装への適用には未解決の不足がある。現在の `Lens b L` は3本の走査スタックにも長さ `L` 以上を要求するが、実構成子のスタックは各256要素である。構築定理の `8*n+8 ≤ L` と合わせると、`n ≥ 32` では実状態が前提を満たせない。したがって、以下の条件付き定理を、実クラスの全対象サイズの検証完了とは扱わない。節点用 `L` とスタック用 `S` を分離した公開定理を別の名前空間へ追加した（後段）。実装の容量や入力範囲は変更していない。追加定理の独立検証と全件検査は未完了である。

- `segment_tree_beats_new0`（構成子）: 前提（`n >= 1`、`8n+8 <= L < 2^31`、要素が `INF` の内側、ベクタが 0 で初期化され `lval` が `INF`）のもとで、`BRep n L a bf (buildBT a 0 n) Hf` が成り立つ。つまり `a` を表す木ができる。
- `segment_tree_beats_chmin`/`chmax`/`add_val`/`update_val`: `BRep n L ys b t H` と、その操作の安全性 `hsafe` のもとで、`ys` を `rangeMin 0 a b x ys`（区間 `[a, b)` の要素を `min(·, x)` にした配列）、`rangeMap (fun v => max v x) 0 a b ys`、`rangeMap (fun v => v + x) 0 a b ys`、`rangeMap (fun _ => x) 0 a b ys` に変えた配列を表す `BRep` が成り立つ。
- `segment_tree_beats_calc_max`/`calc_min`: 返り値は `max (-INF) (rangeMaxOf 0 a b ys)` / `min INF (rangeMinOf 0 a b ys)`（区間の最大値／最小値、空なら `-INF`／`INF`）。木が表す配列は変わらない（押し下げのみ）。
- いずれの定理も、呼び出しが停止すること（`callFuel` が `finished`）、呼び出し側の変数と他のベクタを壊さないこと（`ScalarPostMB`）を含む。

## 時間と領域

- 証明した上界は 1 回の操作あたり木の節点数に比例する（`nodesOf t * 117614 + innerOf t * 24794 + 3012` 以下の仕事量。`calc_max`/`calc_min` は `nodesOf t * 72254 + 5030` 以下、構成子の本体は `4 * n * 45414 + 100` 以下（呼出し全体の scalar work 増分はさらに34、storage work 増分は `4 * n * 18 + 10` 以下））。木は `n` 個の葉を持ち `nodesOf t = 2n - 1` なので、**最悪で 1 回の操作は `O(n)`** である。
- 償却 `O(log^2 n)`（Segment Tree Beats の既知の性質）は、まだ Lean で証明していない。この上界は未検証であり、性能の保証としては使わない。
- 追加領域は局所変数と固定長のスタック（`st_k`、`st_l`、`st_r` は各 256 要素）、節点配列は `8n+8` 要素ずつ。呼び出し側の変数に加える領域の上限は定数（`ScalarPostMB 333`、`400`、`100`）で表す。

## 証明

`Proofs/Beats*.lean`（共有の補題: 木のモデル `BeatsModel`/`BeatsTree`/…、各節点操作の不変条件、`chmin`/`chmax`/`add`/`update` の `Inv` の保存、走査 `travBT`、実行 `BeatsExec*`/`BeatsLoop*`/`BeatsOp*`/`BeatsCalc*`/`BeatsCtor*`、引数準備 `BeatsPrepGen`、呼び出し `BeatsCallGen`、生成モデル `Proofs/Generated/SegmentTreeBeats.lean`）、`Proofs/SegmentTreeBeatsCall.lean`（公開定理）。C++ のテストは `tests/segment_tree_beats.cpp`（素朴な配列との照合、`-fsanitize=address,undefined`）。

## 未解決

- 容量を分離した追加定理の独立カーネル検査と全件検査。旧Lensの制約は既存定理との互換性のため残っており、新しい適用にはBRepSを使う。
- 償却計算量（上記）。
- `x` の範囲（`|x| < INF`）と値の安全性は前提として明記したが、前提が満たされない入力（`±INF` 付近の値の加算）は扱わない。


## 容量を分離した補助証明（2026-11-01）

`Proofs/BeatsCapCtor.lean` は `Capacities b L S` と `BRepS n L S ...` を導入し、node/entered配列の容量Lと走査スタックの容量Sを別々に扱う。中点分割Shapeから区間幅≤2^kなら高さ≤kを示し、n<2^31なら初期スタック予算1+height+2≤256を得る。構築本体の正常終了・意味・cost/need/wkと表現を、S≥34で構成する。`Proofs/BeatsCapChmin.lean` は同じ分離条件をchminの走査・後処理・生成メソッド本体・表現保存まで接続する。旧BRepからの包含もあり、既存定理の前提や結論は変更していない。

`tests/test_beats_capacities.py` のLean回帰例は、実C++と同じ長さの初期配列でn=32、L=264、S=256を構成する。旧Lensは不成立、新Capacitiesは成立し、生成構築モデルから32個の0を表すBRepSを得る。全対象サイズの構築補題は一般のnを扱うが、この具体例は公開callerのallocation/prepareや任意操作列の証明ではない。構築と6操作の生成本体・公開Callへの接続は以下の追加定理へ進んだ。追加モジュールの独立カーネル検査と全件検査は未完了。


## 容量を分離した公開呼出し定理

`Proofs/BeatsCapUpdate1.lean`（chmax）、`BeatsCapUpdate2.lean`（加算）、`BeatsCapUpdate3.lean`（代入）、`BeatsCapCalc.lean`（最大/最小照会）も同じ分離条件で生成メソッドの実行と意味保存を扱う。`Proofs/SegmentTreeBeatsCall.lean` の名前空間 `Proofs.BeatsSeparate` に、既存と同名の構築・6操作の公開Call定理を追加した。これらは準備、正常終了、返却値、callerの保持、scalar/storageの仕事量と領域上界を含む。既存の `Proofs.BeatsRep` 側の定理は維持している。

構築では `BFreshS L S b0`、`34 ≤ S`、`8*n+8 ≤ L < 2^31` を使い、`BRepS n L S ...` を構成する。操作ではこの表現と `S < 2^31` を使う。実装のS=256は双方の容量条件を満たし、Lは8*n+8にできる。従来の算術安全性・区間・型・所有権の前提は維持する。これにより旧Lensの `n≥32` の矛盾を避けて公開Callへ接続するが、C++の確保処理からcallerのBFreshS/CVecsそのものを構成する証明、独立検証器と全件検査の成功は別途必要である。


## 確保処理を含む構築段階の生成

`Proofs/Generated/BeatsConstructionStage.lean` は実ソースの15本のvector初期化と構成子本体を生成した補助モデルである。構築中の `update(e)` は共通のAST展開器で実フィールド局所変数へ展開する。初期化prefixの後の本体は、既存の本体モデルに対しvector引数のスロットを循環置換したものと構文上一致する。実ソースとの全文一致・型検査と、初期化の型/順序/容量・本体の置換を回帰検査する。[構築段階と範囲](constructor_stage_methods.md)を参照。

この構文一致は、15本の実確保からBFreshS/CVecsを構成する一般証明や、評価器でのスロット置換の意味保存とは区別する。それらとクラスexport/寿命の接続は未完了である。


## 元のサイズ範囲へ戻す構築候補

[64-bit確保長・構築添字の候補](beats_wide_candidate.md)をexperimentsへ追加した。操作側の子添字は木の高さにより元のintサイズ範囲で安全と証明できるため、現候補は構成子だけを変更し、6操作の生成関数を保つ。検査済みの候補であり、公開版や構築の一般証明への切替は未完了。違反一覧の項目を解消済みにはしていない。
