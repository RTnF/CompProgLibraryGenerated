# 作業引き継ぎ

## 新方式への移行（2026-11-12〜、最優先）

目標（利用者の指示）: 全証明を `docs/redesign_2026-11.md` の新方式へ移し、全部品（取り下げた segment_tree_beats・segment_tree・lazy_segment_tree・find_cycle を含む）を再公開し、push 後の CI を 20 分以内にする。

基盤（ローカル commit、未 push）:
- `Proofs/Cpp/Prelude.lean`: `Cpp.M := StateT Nat Option`（tick と非停止）、`Cpp.forever`（while）と `WhileInv` の mvcgen 仕様、vector・整数の演算。`check`（assert）は mvcgen が展開する。
- `verifier/lean_translate.py`: Clang JSON のテンプレート定義 → Lean。符号なしは `UInt32/UInt64`、`T::value_type` のコンテナ引数は `Array`、再帰・クラス入れ子・friend・ラムダ・`std::sort` は未対応。全公開ヘッダの翻訳状況は `for f in library/*/*.hpp; do python3 verifier/lean_translate.py $f; done` で確かめる。
- `verifier/diff_harness.py`（C++/Lean のインタプリタを生成して差分テスト）、`verifier/model_bridge.py`（`translation = "lean_model"` の bridge）、`docs/translation.md`（翻訳規則・STL の表）。
- 共有補題 `Proofs/Cpp/Lib/{Basic,Lowbit,Rle}.lean`。
- 移行済み: vector_sum, fenwick_tree, vector_max, vector_min, vector_fill, vector2d_sum, safe_mod, gcd_u64, bit_width_u64, countr_zero, search_util（`counts` を復元）, element_count。旧証明・旧モデルは `verifier/support.toml` の共有モジュールに移して残してある（最後にまとめて削除する）。
- 手順（1 部品）: `python3 .cache/wip/newmethod/tools/migrate.py NAME 'T=long long;T=int'`（ローカル補助。TOML 書き換え・旧証明の共有化・Proofs.lean）→ `Proofs/Cpp/<Stem>.lean` に仕様（正しさ＋tick の上界）を mvcgen で証明 → `tests/diff/NAME.py` → `python3 verifier/model_bridge.py --component NAME` → docs 更新 → commit。
- 証明のこつ: `mvcgen [f]` → `simp +zetaDelta at *`（`simp_all` は仮定を消すことがある）。仮定は型パターン `‹_ ∧ _›`、カーソルは `range_cursor ‹range _ _ = _ ++ _ :: _›` と `subst`。名前が要るときは Mathlib の `set`。`Proofs.Cpp.size` は `Array.size` と紛れるので修飾する。
- 2026-11-12 追記: 移行済みは上記＋pow_mod, inv_gcd（原本の pair API に復元、依存 safe_mod の呼び出し）, run_length（計 17）。statements.json は再生成済み（d17a096 の後）。証明ソースでは `#` が禁止（`#[]` は `([] : List T).toArray` と書く）。
- 作業中（`.cache/wip/newmethod/scratch/`）: `CsrScratch.lean`（csr_build の証明が完成。生成コードを内包しているので、登録時は Gen と証明に分ける）、`CsScratch.lean`（CumulativeSum 1 次元が完成）、`Cs2Scratch.lean`（2 次元の構築: 補題は完成、残りの VC は `extract_goal` の名前順で `rename_i` して補題を当てる途中）、`cs.hpp`（原本どおりの cumulative_sum.hpp。登録時に library へ置き、TOML の hash を更新）。
- 全件 gate（`check_public.py --mode all`）は失敗: 旧方式の `tests/test_dynamic_result_runs.py` が `returning a vector from a block with declarations is unsupported`（旧変換器が、元の形に戻したヘッダ（inv_gcd/search_util/element_count など）を読んでいる可能性。原因未調査。移行済み部品を参照する旧テストは support.toml の checks から外すか、旧検査を削除して解消する）。ログ `.cache/wip/newmethod/gate.log`。旧方式の test_template_class_layout が verifier 変更で毎回再実行され非常に遅い（CI 20 分の障害。monoid_lazy 移行後に削除する）。
- 未了: statements.json の再生成（`tools/regenerate_statements.py`。登録を変える作業と並行に走らせない）、全件 gate、push（原本単位・手動承認）、残り約 42 部品＋取り下げ 4 部品、旧方式の削除、CI 20 分の計測。

- 2026-11-12 夕方の状態（ローカル commit、未 push）: 移行済みは計 52 部品。上記に加え csr_build, cumulative_sum, interval, interval_union, tree_* の全断片（tree_full_dp を除く）, xorshift, mod61, floor_sum_unsigned, topological_sort, floyd_warshall, bellman_ford, dijkstra, prim, square_matrix。全件 gate は 2f334ae 時点で成功（監査を含む。statements.json を再生成し、公開定理名から `'` と `!` を除いた）。その後の dijkstra 以降は個別の bridge・ビルドだけ確認済み。
- 旧数学層の再利用: tree_order（TreeOrderMath の qrun）、tree_root（TreeRootMath の runL/stepD/stepF）、topological_sort（TopoSortMath）、floyd_warshall（FloydWarshallCall の Dm/Em）、bellman_ford（BellmanFordExec/PExec の roundsL など）、dijkstra（DijkstraMath/PMath）、prim（PrimStep の PInv、PrimBridge の prim_msf）、mod61（Mod61Math）、floor_sum_unsigned（FloorSumReciprocity）、square_matrix（MatPowMath）。旧方式を消すときはこれらの純粋な定義・定理を残す（または `Proofs/Cpp/Lib` へ移す）。
- 補助スクリプト: `.cache/wip/newmethod/tools/leanrun.sh FILE`（RSS 6GB で止める監視つき lean。`simp [Nat.add_mod, Nat.mul_mod]` で OOM になり WSL が落ちた）。
- 2026-11-13 の状態（ローカル commit、未 push）: 登録 56 部品のうち 48 部品を移行済み。追加分は segtree_sum, enumerate_quotients, floor_sum（符号付き。符号なし→符号付き変換を `Cpp.toSigned` で 2 の補数として翻訳）, is_prime（純粋モジュール `Proofs/IsPrimeMath.lean`）, union_find, lowlink（`Proofs/LowlinkPhiMath.lean`、旧 `LowlinkInv` の機械 `St` を詳細化）, doubling（`numeric_limits`、`assign(begin,end)`）, extrema（型引数の混在を `Cpp.HLt`/`Cpp.Conv`）, sort_util（erase-unique を `Cpp.unique`）。`verifier/state_bridge.py` は使われなくなったので削除。statements.json は 9ab25f3 で再生成（以後の `#` 除去で再生成が要るか gate で確認）。
- tree_full_dp は ff0b413 で移行済み（ポリシー `P::f` → 明示引数 `cp.tree_full_dp.Policy_P`。全ポリシーについて可換モノイドの仮定で証明、DpHeight は heightCM）。全件 gate は 9497e65 で成功（`--mode audit --timeout-seconds 1500` を別に走らせる）。
- 残り 7 部品: rolling_hash（mvcgen が長い let 鎖＋`4*m`＋`if` で OOM。`hash` は `run_tick_ite` と `split <;> rfl` で純粋関数に置き換える回避が `.cache/wip/rolling_hash/` にある。構築子のループ本体も同様に要る）, group/monoid/monoid_lazy/modint/dynamic_modint/ratio（friend 関数・static メンバ・暗黙の変換など、クラスまわりの翻訳器拡張）。取り下げた 4 部品。最後に旧方式の削除と CI 20 分の確認。

更新: 2026-11-09。時系列ログを圧縮して上書きした。目的は **experiments の全137ファイルを検証し、元API・機能・汎用性を保って移植すること**。一部のモデルやCI成功だけで完了としない。

## 2026-11-14 ratio の移行途中（未コミット・未push）

- `Proofs/Cpp/Ratio.lean` の `init_spec` / `normalize_spec` が `sorry` なしでコンパイル成功。互除法の停止測度、正規化結果、正規化後の互いに素性、`gcdCost + 4` のtick上界を証明。docs/ratio.mdも新定理に更新。
- `tests/diff/ratio.py` を追加。`model_bridge.py --component ratio` 成功、ASan/UBSan付きC++とLeanで510出力一致（ゼロ・64bit境界・乱数）。friend定義はADLが必要なので、翻訳器で定義元を記録しdiff_harnessで非修飾呼出しを生成。
- テンプレートクラス内friendの差分テスト呼出しも修正（クラスの型引数を関数テンプレート引数として付けない）。`tests/test_lean_model_friend.py` 成功: 非公開フィールド読取り・ADLと通常の名前空間関数をC++/Leanで比較。support.tomlに登録、翻訳規則をdocs/translation.mdに追記。
- 2026-11-14 続き: 原本Ratioの前置/後置増減に必要な `*this` の値読取り、`operator++/--`、`++*this/--*this` の前置呼出しを翻訳器へ追加。`tests/test_lean_model_friend.py` の2テスト成功（サニタイザC++/Lean、返却値とreceiverを明示値でも検査）。差分ハーネスでオブジェクト戻り値のpushをreceiver更新が上書きしていた不具合も修正。候補 `.cache/wip/ratio_restore/counter.hpp` の生成Leanがコンパイル成功。原本Ratio全体はまだ置換していない。
- 2026-11-14 続き: C++20規格を新方式の登録・Clang宣言/AST抽出・翻訳CLI・bridge・差分ハーネス・公開C++/sanitizer/IO/include・配布ZIP検査まで伝播。C++17→C++20依存は拒否。`tests/test_public_support.py` 27テスト成功（C++20必須headerの実compileを含む）。`<=>`→Orderingとスカラー全フィールドのdefaulted operator==を追加、`tests/test_lean_model_friend.py` 4テスト成功（分数の大小・同値とフィールド等値の違いも検査）。元のRatioをnamespace/includeのみ変更した候補 `.cache/wip/ratio_restore/original.hpp` はC++20でAST取得可能、現時点の先頭の翻訳拒否はストリーム型 `istream &`。候補はまだ公開していない。明示defaultedメンバー（等値以外）と継承は黙って省略せず拒否する。
- 検証ログ（2026-11-14）: `.cache/wip/ratio_restore/models.log` は新方式の登録50モデルを全再生成して一致、`bridge.log` は ratio/interval のbridge成功、`package.log` はZIP56headerの外部include成功。`public_support.log` は27テスト成功。全件C++は同ディレクトリの `cpp.log` で56部品すべて成功（C++/ASan/UBSan/テンプレート先行include）。Lean全件ビルド/最終監査は未実施。
- 2026-11-14 続き: `std::gcd/lcm` の値モデル（各引数の絶対値→共通型の結果）と混在符号の差分テストを追加。規格には計算量上界がないため `[Cpp.NumericCost]` の費用パラメータを要求し、対数時間と決め打ちしない（規格/cppreferenceをdocs/translation.mdへ引用）。差分テストだけの費用1は時間証明に使わない。スカラーレコードの暗黙コピー、一時receiverの複合代入、非explicit単一引数の暗黙構築を追加。原本算術候補 `.cache/wip/ratio_restore/arithmetic.hpp` の次の拒否は左辺Tへのoperator+=。原本をGCC20でコンパイルして `1LL + Ratio<long long>` の実バグを確認、未修正としてdocs/experiments_findings.mdへ記録。復元時にRatio(a)での演算へ修正する必要がある。ストリームも未対応、公開headerはまだ旧正規化のみ。
- 最新の検証: `test_lean_model_friend.py` の6件＋ユーザー定義コピー拒否1件が成功。`lake build Proofs.Cpp.Ratio` 成功（Prelude/生成Ratio/共有補題/Ratioを再ビルド）。算術対応追加後も `models.log` の50登録モデルが再生成一致。`git diff --check` とPython compile成功。原本Ratio全体は未完であり、commit/push/新しいCI計測は未実施。
- 2026-11-14 続き（原本の実修正）: `experiments/library/cpp/number/ratio.hpp` の左辺Tの4演算をRatio(a)で計算する形に修正。operator/=は新分子/分母を先に計算し、代入後normalize（自己除算の別名と負の除数の不具合）。修正前の失敗を確認後、`tests/test_ratio_original_api.py`（`tests/imports/ratio_scalar_left.cpp`）で360入力×int/long longの4演算＋自己除算がFractionと一致、ASan/UBSan成功。fixes.mdに即時追記、experiments_findings.md更新。原本の全API公開完了ではない。
- 算術移行の到達点: 原本からストリーム2本だけを除いた全算術（28関数）のT一般翻訳が生成・Leanコンパイル成功。構築子→非const helper呼出しと修飾クラスの要求伝播を修正。`test_lean_model_friend.py` は8件成功（原本の正負3組の算術・スカラー/Ratioの両辺の組合せ・前後置・比較・自己除算を含む）。ハーネスのオブジェクト引数もコピーではなく参照束縛へ変更し、本物の別名ケースを検査する。`models.log` は50登録モデル再生成一致。
- `inventory_imports.py --check` は旧移行で消えたdoubling/floor_sumの3根拠ファイル参照も検出したため、新方式の差分テスト/bridgeへ更新。Ratio行はC++20で33宣言を再抽出、原本hash/構文compile結果を更新し、137ファイルのinventoryチェック成功。review/proof/publicの全体完了フラグはpendingのまま。
- 2026-11-14 続き（ストリーム）: Preludeへ `Streams`（状態型）/`StreamRead T`（旧値も受け取るM変換）/`StreamWrite T`/文字用`StreamChar`を追加。書式・locale・flags・コスト・失敗/不帰還の実現を明示的なパラメータにし、正本の既定実現は置かない。型引数Tのフィールド等に対する連鎖shift・状態書戻し・narrow文字挿入を翻訳。具体int/long/charの区別や多文字定数を誤って共通契約に落とさず未対応として拒否。単一自由operatorのLean名も正しくop_shr/op_shlへ変換。
- 原本Ratio全体（30関数、入出力を含む）がnamespace/include/標準gcd/lcm明示修飾だけで生成・Leanコンパイル可能になった。`tests/test_ratio_stream_model.py` 2テスト成功。`tests/lean/ratio_stream_contract.lean` は任意T/任意標準操作について入力2回/条件付き出力と生成関数が一致することをrflで証明（コストも同じM式に保持）。具体既定書式7ケース（空/不正/EOF/生の2/4等）が原本C++ ASan/UBSanと一致し、返却参照もnativeで確認。support.tomlへ登録済み。フル翻訳は `.cache/wip/ratio_restore/restored.hpp` / `Restored.lean` でも確認可能。
- 最新: 既存friend/算術8テスト成功、50登録モデル再生成一致、inventory137成功、diff --check/py_compile成功。**未完**: 汎用diff_harnessのストリーム引数/参照戻り値のプロトコル（現テストは専用driver）、原本算術の仕様/計算量のLean証明、公開header/TOML/テスト/文書の切替、全件gate/監査/CI計測。他の6旧方式部品＋取り下げ4部品等も残る。標準GCD/LCMの費用パラメータを対数時間と決め打ちしない。公開headerは引き続き旧3フィールドRatioであり、全API移植済みとは扱わない。
- 2026-11-14 続き（汎用ハーネスへの統合完了）: diff_harnessへ既定書式の入力/出力ストリームを追加。入力はcount+canonical decimal/x、出力はEOF/failまたは長さ/文字コード。返却streamはC++でauto&捕捉。非constクラス参照はobjref表示＋Lean側object表へ更新。int/long longの各9ケースでEOF/不正/欠落/上下限超過の切詰め・オブジェクト更新後の再出力が一致。short/char/unsigned/幅混在を誤った共通規則へ落とさず拒否（テスト実現の制限でありCppテンプレートの変更ではない）。
- 単独ヘッダ候補 `experiments/verification/number/ratio.hpp` を追加。修正済み原本からnamespace/std修飾/default型表記のみ変更し、全API/本体の一致、standalone include、既定型をテスト。公開libraryへはまだ移していない。自由operatorには単独でも型タグを付け、cp.op_shr_istream_Ratio/cp.op_shl_ostream_Ratioへ改名。別ヘッダの演算子モデルを同時にLean compileする回帰も追加。
- 数学層 `Proofs/Cpp/Lib/RatioMath.lean` を追加しsupport/Proofs.leanへ登録。Int正規化=Rat正規分子/分母、正の分母・coprime・値保存、GCDのtdiv=ediv、増減/符号反転の値と加減算を証明（11定理）。`tests/lean/ratio_arithmetic_contract.lean` はfresh候補生成コードに対して正規化/2引数ctor/単項minusのIntモデルと費用、1引数ctor/前後置増減/単項plusのT一般のデータ更新と費用を証明、加減算のIntモデルの結果・停止・費用も証明（14定理）。stream contract 2本も同じfresh生成環境で検査。NumericCostを対数時間へ固定しない。
- **次の作業**: Ratioの乗除算・比較・等値および二項/混合型ラッパーの仕様証明、Intから全T/固定幅のモデル対応（差分バックエンドの型別実現も必要）、GCD/LCMの計算量の根拠（stdは上界未規定なので明示helper等を検討）、全API header/TOML/公開testsの切替、statements.json再生成と全件gate/独立監査、その後に原本単位push・CI20分計測。現公開ヘッダはまだ旧3フィールド版なので原本移植完了としない。追加したshared RatioMathの定理も最終spec/security監査はまだ。
- この段階の検証: stream/model契約7テスト、既存friend/算術8テスト、原本API1テスト（計16）成功。`models.log` は自由operator名の安定化後も登録50モデルが再生成一致、`bridge.log` は現公開ratio/interval成功、inventory137成功。新しい数学層11定理＋fresh生成との対応14定理＋stream2定理をチェック済み。最終仕様catalog/両kernel監査、公開全APIのgate、push後CI20分は未実施。ローカル候補の成功を原本全体の公開完了としない。
- 実行環境: `PATH="$PWD/.tools/elan/bin:$PATH" ELAN_HOME="$PWD/.tools/elan"` を指定（通常PATHにlakeなし）。
- **原本全体の移植完了ではない**。現公開ヘッダは旧来の符号/大きさ3フィールドとnormalizeのみ。原本の任意T・各コンストラクタ・算術/比較/入出力の復元が必要。全件gate・statements再生成・文書更新も未了。部分移行を理由にpushしない。

## 現在の作業

1. `library/`の59部品を原本に似た12分野へ移動し、隣接するTOML・source/include・テスト・文書・再帰登録/cache・配布ZIPを更新済み。本handoffも原本ごとの表へ圧縮済み。
2. 配置変更で見つかった旧ModIntモデルのずれとnested oracleの旧パス参照を解消。最新の全件gateは実75688が終了0（853.562秒）。inventory137・Lean1793build・59CPP/59bridge・共有242checks・52416宣言の命題/定義/公理依存・両kernel（nanoda49238宣言）・ZIP59header単独/一括includeが成功。証拠は `.cache/wip/library_layout_20261109/final_gate/{checks_state.json,all.log,package.log,archive.log}`。この成功は原本137ファイル全体の移植完了を意味しない。
3. `monoid_lazy`の元nested API候補（experiments/verification/algebraic_structure/monoid_lazy.hpp、原本とnamespace/includeだけ異なる）を検証中。1field値構築とRangeAdd::idの任意caller証明を追加し、原本/候補の6型ずつを検査した実46323は2tests/380.630秒終了0。kernel3857×8/3885×4・C++/UBSan・入力hash不変。値構築総IR work≤引数式nodes+6（literalは7）、idは変換/scope込み≤9、raw need=P.length+7。scalar/vector・権限・const結果・scope/peakを保持。RangeSetのvalue/default/id（2field）を27rootsで共通化し、3入口のprepare→body→field export・const/scalar/vector保持・work/peakがLean compile成功。総IR workは値構築≤式nodes+9、既定≤9、id≤10。実5160で原本/候補両familyの再生成/kernel/UBSan検査は成功（2tests/139.5秒、終了0、nanoda3930宣言×4、入力hash不変、receipt: `.cache/wip/set_record_ctor_20261109/registered/receipt.json`）。次は任意T/M・strict identity/lifetime・公開切替。任意T着手前の調査(2026-11-10): 一般caller補助(`GroupCall.refs2b_correct`等)はs64版とi32版が約1300行離れて複製されており、`addE`/`addE_den`/`MonoidLazyCall`の各定理もs64/i32を直書きしている。生成モデルも具体Ty(`⟨64,true,false⟩`)を埋め込む。任意Tには(1)`refs2b_correct`/`prep_ref2`等を`t : Ty`で一般化し、s64/i32版をその特殊化に置換、(2)変換器が`T`を`Ty`変数としたプログラム族`prog (t : Ty)`を出力し、既存の具体モデルが`prog s64`と`rfl`で一致することを確認、(3)MonoidLazyCallの各定理を`t.valid`仮定で再述、の順で進める。浮動小数Tは`docs/trust_policy.md`のRat+誤差予算が別途必要。
   手順1の先行例を実施(2026-11-10): `Proofs/GenericCall.lean`を追加し、`refs2b_gen`・`convG`・`shapeG_exec`・`addG_den`・`P_cellG`と、プログラム族`composeAdd (ty : Ty)`（`composeAdd s64 = 生成compose_RangeAdd_long_long`を`rfl`で確認）、任意Tyの`rangeadd_compose_gen`（仮定: x,y,x+yが`ty.valid`）をlake buildで証明。公理はpropext/Classical.choice/Quot.soundのみ、sorryなし。続けて`Proofs/GenericLazy.lean`に`sumOpX (ty)`（`sumOpX s64 = RangeSum_long_long_op_x`をrflで確認）と任意Tyの`rangesum_op_x_gen`を追加（同公理）。`op_size`はint固定でT非依存。`setComposeV/setComposeNoop (ty)`（s64でrfl一致）と`rangeset_compose_v_gen`/`rangeset_compose_noop_gen`も追加済み。`rangeadd_applyExt_gen/applySum_gen`、`rangeset_applyExtremum_gen/applySumX_gen`、`rangeadd_new0_gen/new1_gen`（`const_gen`/`ctor_gen`/`valid_zero`/`R0z_gen`含む）も追加し、`Proofs/Generated/MonoidLazy.lean`の登録11モデルは全て任意Tyの定理に接続（各`xxx_s64`が`rfl`で生成モデルと一致、公理はpropext/Classical.choice/Quot.soundのみ、sorryなし。HEAD e1b064e系のローカルcommit）。`tests/test_generic_template_family.py`（9.7秒）を追加: 公開ヘッダをlong long/int/unsigned/unsigned long longで再具体化し、共通nested変換器の出力10プログラム×4型が`Ty`族（`castTo`で同型castの省略を再現）と`rfl`で一致することを確認。これで登録11モデルの一般定理は変換器出力の4型と接続された（浮動小数は別）。`Proofs/GenericExtrema.lean`（`tests/lean/original_extrema_object_general.lean`をTy一般化: `tail ty`/`selectionBody ty i j`/`tail_exec`/`selection_exec`、公理は標準3種、sorryなし）を追加。`tests/test_generic_template_family.py`に原本RangeMax/RangeMin friend op（Add/Set両系統×{int, unsigned long long}）の`body = selectionBody ty 0 1 / 1 0`をrflで確認するテストを追加（約4分、1生成約30秒のため型を絞った）。`tests/lean/generic_extrema_object_call.lean`（`original_extrema_object_call.lean`のTy/添字一般化: `gProgram/gFields/gPerm/gView/gCombine`、stage_ready/finish_export/view_export_correct/object_export_correct等11定理）を追加し、同テストで各具体化（Add/Set×Max/Min×{int,unsigned long long}）の`exportViewFuel`/`exportObjectsFuel`が`gView/gCombine ty i j`とrfl一致、全定理が標準3公理のみ・sorryAxなしを確認。呼出し一般化を`stage_of_exec`（任意prog・入力数・ローカル数）/`finish_export`（出力スロット可変）に分解し、`Proofs/GenericExtrema.lean`に`identBody/ctorBody/ident_exec/ctor_exec/lowestV/highestV`（numeric_limits相当、有効性証明つき）を追加、fixtureに`nullary_export_correct`/`identity_export_correct`/`default_export_correct`を追加。テストで生成された`RangeMax/RangeMin`の`factory_e`/`construct1`（と各exportViewFuel）が`gNullary ty (identBody/ctorBody ty (lowestV|highestV ty))`とrfl一致（Add/Set×{int,unsigned long long}）、全定理の公理が標準3種の部分集合であることを確認。`tests/lean/generic_extrema_add_apply.lean`（`original_extrema_add_member_general/call`をTy一般化: `GenericAddApplyRaw.raw_exec`、`gApply/gApplyFields/gApplyView/gApplyObjects`、stage_ready/finish_export/view_export_correct/object_export_correct等）を追加し、`test_original_extrema_add_apply_equals_the_ty_family`（約2.5分）で原本RangeAdd::apply on RangeMax/RangeMin（{int, unsigned long long}）の生成プログラムとexportViewFuel/exportObjectsFuelが一般形とrfl一致、公理が標準3種の部分集合であることを確認。`tests/lean/generic_extrema_set_apply.lean`（`original_extrema_set_member_general/call`のTy一般化: choice/yes/noBody族、`raw_exec`、`gApply`等）と`test_original_extrema_set_apply_equals_the_ty_family`（約2.5分）を追加し、RangeSet::apply on RangeMax/RangeMin（{int, unsigned long long}）の生成プログラム/exportViewFuel/exportObjectsFuelが一般形とrfl一致、公理が標準3種の部分集合であることを確認。`tests/lean/generic_set_record_ctor.lean`（`original_set_record_constructor_general.lean`のTy一般化: program/view/fields/permissions族、raw_exec（castTo対応でcost/needは上界）、stage_ready/finish_export/entry_correct/value・default・id_correct/work等27定理）と`test_original_set_record_constructors_equal_the_ty_family`（約2分、{int, unsigned long long}×{RangeSetRangeMaxMin, RangeSetRangeSum}）を追加。RangeSetの値構築/既定構築/id()の生成プログラム・exportViewFuelが一般形とrfl一致、公理は標準3種の部分集合。`tests/lean/generic_scalar_record_ctor.lean`/`generic_scalar_record_zero.lean`（`original_scalar_record_constructor_general`/`zero_factory_general`のTy一般化）と`test_original_scalar_record_constructors_and_id_equal_the_ty_family`（約3分; RangeAdd/RangeMax×{Add/Set}×{MaxMin/Sum}の3組×{int, unsigned long long}）を追加。1フィールドレコードの値構築と`RangeAdd::id()`の生成プログラム・exportViewFuelが一般形とrfl一致、公理は標準3種の部分集合。`tests/lean/generic_add_sum.lean`（`original_mixed_add_sum.lean`のTy一般化: 族`gApply/gE/gNew0/gNew1/gOp/gCompose`と`apply_exec/mutable_values2/constant_body/two_values_body/e/default/new/op/compose`等）、`generic_set_value_ctor.lean`（`original_mixed_set_sum_value_ctor`の一般化）を追加し、`test_original_set_sum_transferred_programs_equal_the_ty_family`（約2分）で`lower_template_class`の`OriginalMixedAddSum`/`OriginalSetSum`の生成プログラムが一般形とrfl一致（{int, unsigned long long}）、公理は標準3種の部分集合。`generic_set_callers.lean`（`original_mixed_set_sum_callers`の一般化。RangeSum側はadd_sumの定理に帰着、RangeSet new1/idは`gSetNew1`族）も追加済みで、同テストがRangeSet側RangeSumプログラム(e/new0/new1/op)がAddSum族とrfl一致することも確認。`generic_set_compose.lean`（`original_mixed_set_sum_compose`の一般化: `gSetCompose`族、compose_exec/four_values_body_correct/compose_correct）も追加済み（同テストで生成プログラムとrfl一致）。`generic_set_apply_sum.lean`（`original_mixed_set_sum_apply`の一般化: `gSetApply`族、update_exec/apply_exec/RW2V2_correct/apply_correct、castTo対応）も追加済み（同テストで生成プログラムとrfl一致）。`original_mixed_set_sum_samples`は有限サンプルの`decide`検査で、一般定理が任意入力を覆うため一般化不要。`generic_record_apply.lean`（`original_record_apply`のapply部: `gRecApply`族、add_exec/apply_correct）と`test_original_record_apply_equals_the_ty_family`（約1.4分）を追加。original_record_applyの残り（RangeAdd_idの3文形、RangeMax/Min new0/new1/e/opが公開`group`/`monoid`の具体モデルへ等式で結ばれる部分）は`group.hpp`/`monoid.hpp`側の任意T化（浮動小数含む）に依存して未了。`generic_extrema_object_call.lean`に拒否定理`incomplete_object_rejected`/`missing_slot_rejected`/`vector_slot_rejected`（任意ty・任意callerでfault）を追加し、`original_extrema_object_values`の肯定ケース（有限サンプル）は`object_export_correct`/`identity_export_correct`/`default_export_correct`が任意入力で覆うため一般化済みとした。`generic_sum_add_apply.lean`（`original_add_member_general`+`original_add_member_call`のTy一般化: RangeAdd::applyがRangeSumの完全なオブジェクト（x,size）を返す。`gSumApply/gApplyFields/gPerm/gApplyView/gApplyObjects`、castTo対応でcost/needは上界）と`test_original_sum_add_apply_equals_the_ty_family`（約1.4分）を追加。`generic_sum_set_apply.lean`（`original_set_member_general/call`の一般化: RangeSet::applyがRangeSumの完全なオブジェクトを返す）と`test_original_sum_set_apply_equals_the_ty_family`（約1.4分）も追加済み。`generic_friend_op.lean`（`original_friend_object_return_general`+`original_friend_object_call`の一般化: friend opが完全なRangeSumオブジェクトを返す。`gOp/gFields/gPerm/gView/gObjects`）と`test_original_friend_op_returns_complete_sum_objects_for_every_ty`（約2分、Add/Set両系統×{int, unsigned long long}）も追加済み。`generic_sum_value_ctor.lean`（`original_value_constructor_general`の一般化: `RangeSum(T x,int size)`の値構築。`gValueCtor/gFields/gPerm/gView`）と`test_original_sum_value_constructor_for_every_ty`（約2分、Add/Set×{int, unsigned long long}）も追加済み。`generic_sum_default_ctor.lean`（`original_delegating_constructor_general`の一般化: `RangeSum()`の既定構築。`gDefaultCtor/gFields/gPerm/gView`）と`test_original_sum_default_constructor_for_every_ty`（約2分）も追加済み。`generic_sum_factory_e.lean`（`original_factory_export_general`の一般化: `RangeSum::e()`のfactory。`gFactoryE`）と`test_original_sum_factory_identity_for_every_ty`（約2分）も追加済み。`generic_add_compose.lean`（`original_value_add_call`の一般化: `RangeAdd`のfriend composeが完全なオブジェクトを返す。`gCompose`）と`test_original_add_compose_object_for_every_ty`（約2分、{RangeAddRangeMaxMin, RangeAddRangeSum}×{int, unsigned long long}）も追加済み。コピー配置系(`original_template_object_layout`/`original_delegating_object_layout`)は型非依存の複写機構の有限サンプル検査で、値は一般定理、プログラム形はrfl照合で覆われるため一般化不要と判断。`generic_set_compose_object.lean`（`original_set_object_general`+`original_set_object_call`の一般化: `RangeSet`のfriend composeが完全なオブジェクトを返す。`gCompose`、choose/arm/tail_exec/raw_exec）と`test_original_set_compose_object_for_every_ty`（約2分、{RangeSetRangeMaxMin, RangeSetRangeSum}×{int, unsigned long long}）も追加済み。apply系4フィクスチャ（extrema add/set、sum add/set）に任意ty・任意callerの拒否定理`readonly_receiver_rejected`/`incomplete_receiver_rejected`/`vector_receiver_rejected`を追加（`original_member_record_return`/`original_template_member_result`の読み取り専用receiver・不完全オブジェクト拒否に対応。引数スロット欠落と符号付き和の折返しfaultは未了）。残りは`original_template_object_layout`/`original_delegating_object_layout`（コピー配置）。MaxMin系で残るのは（旧）値出力(`original_extrema_object_values`の有限サンプル検査)の一般化と、原本の他クラス(Sum/Set/Add本体のobject版)。残りの任意T: 原本nestedモデル(tests/lean/original_*.lean等44ファイル約1万行、MaxMin op/e/apply、RangeSet値/既定/id、RangeSum構築/apply)、未了: unsigned等の折返し(x+yが範囲外)、他の関数(Sum/Set/MaxMin/apply/id/値構築)の一般化、変換器が`prog (t : Ty)`を出力する部分、check_public/security gateへの登録。Sum構築/e/op/apply・MaxMin op/e/apply・Add/Set composeは既存一般証明へ接続済み。任意T/M・strict identity/lifetime・公開切替・原本全体は未完了。全件gateは後続変更前のsnapshot。原本1ファイル全体の移植完了前にはpushしない。

## 判定と作業制約

- **公開59部品**と**原本137ファイル（header66/template6/driver65）**は別の単位。公開部品の検証があっても元class/API・任意T・全lifetimeの完了を意味しない。表の「部分」は原本全体未完了。
- 既存の大量の変更を保持する。`MEMORY.md`、cache、ツール実体、ローカル測定値は公開候補に含めない。新commit/pushなし。HEADは `5bf952dff99f102e9aea74aa0d096ac953c5cdec`、最後に確認したorigin/mainは `096d2902959f2607b39baee5c46e786feb31db70`。
- push粒度は原本1ファイル全体の移植完了。機密情報検査→commit→手動承認push→対象SHAのActions/配布物終了確認。[Git手順](git_workflow.md)を守る。
- リクエスト量を抑え、agentを増やさない。重いjobは1本、低優先度・offline。Lean1thread、nanoda固定2threads/既定16MiB。資源不足は上限増加で回避しない。観測timeoutだけでjobを再起動しない。
- コンテストサイトへテスト/CIから通信せず、この環境から提出しない。機密値をログへ出さない。

## 重点項目・再開地点

| 項目 | 確認済み | 残件・次の手 |
| --- | --- | --- |
| monoid_lazy / Sum | RangeSum構築、friend op、Add/Set compose、Add/Set applyの全fieldを任意callerへ接続。readonly/alias・const結果・scalar/vector保持とwork/peak | 任意T/M・厳密object identity/lifetime・元のnested class公開API全体を復元 |
| monoid_lazy / MaxMin | Add/Set×Max/Minのop/e一般callerとmember templateの全field返却。RecordArgumentで同一TUの宣言ID/patternを照合しmember pointer型もcompilerで確認 | Add/Set apply<M>は任意caller exportまで一般証明済み（work≤14/21）。元nested API候補はexperimentalへ配置済み。候補のSum/MaxMinとcomposeは一般証明接続済み。1field値構築/RangeAdd idも一般caller済み。RangeSet value/default/id、任意T/M・strict identity/lifetime・公開切替は未完了。copy/値構築のconditionalは選択枝だけ実行。副作用条件・入れ子record conditional等は未対応として拒否 |
| Group/Monoid | hidden friend・既定構築・汎用型制約を復元。LLモデルと一般caller、float単位元C++回帰 | 任意T・浮動小数Lean契約/誤差・strict lifetime。原本2系統の差を保って監査 |
| ModInt | 原本/移動後ヘッダはバイト同一、移動前配置と移動後からの生成モデルも同一 | 生成モデル11定義を再生成済み。Powのloop一般定理を追加セルのscope除去込みで更新し従来の数値上界を維持。Div/全Opsの一般定理もbuild成功。独立kernel36roots/6172宣言も成功。全件gateも成功。評価を消して照合だけ合わせない |
| Beats | 元構築の15vector/2scalar、初期callerからの資源上界、export・buffer保持・6操作の呼出し/receiver復元 | Safe条件導出、任意更新列・償却、全無関係vector保持、child入力、class converter/寿命・公開切替・独立監査 |
| Tree | 利用者のLCA上限を実表size()-1へ修正した変更を保持。全小木/境界/任意root・全対C++、全行降下の一般数学定理 | 元class全体のC++由来生成、build_ancestorのsingleton assert、cost_depthの型、直径/全API・lifetimeは未 |
| Fenwick/UnionFind | 公開クラスで元APIの保持を改善。Fenwick構築の範囲外と+=のみの型を修正。UnionFindの元class/コピー/receiverを監査 | 原本ファイル全体の完了監査、任意型/厳密lifetime。部分関数の成功を全API完了にしない |
| SegmentTree/Lazy | 現公開policy版は部分的に検証済み | 元のobject型・全操作/search左右・汎用性を狭めた違反を解消。クラスを関数ごとのファイルへ分割しない |
| SquareMatrix | 比較/powの不具合とpow(ll)/traitを修正、C++/UBSan比較済み | 候補全範囲の一般証明・原本APIそのままの公開判定 |

## 検査証拠

- `.cache/wip/scalar_record_ctor_20261109/registered/`: 実46323は2tests/380.630秒終了0。原本/候補6型ずつ、kernel3857×8/3885×4、C++/UBSan・入力hash不変。新12rootsの値構築は純粋scalar式を取り総work≤nodes+6、6rootsのRangeAdd idは総work≤9。全field exportと元scalar/vector・const権限・scope/peak。任意T/M/lifetime/全体は未完。

- `.cache/wip/monoid_lazy_candidate_sum_20261109/registered/`: 実70126は7tests/507.224秒終了0。kernel4316×3（原本1/候補Sum構築2）、4086×2（Sum op）、4117×4（MaxMin op/e）、4072×2（Add compose）、4102×2（Set compose）、4126/4104（Sum apply）。C++/UBSan・入力hash不変。原本/候補で同一の証明fixturesを使用。任意T/M・strict lifetime・全体未完はreceiptに明記。

- `.cache/wip/monoid_lazy_api_20261109/registered/`: 実97763は5tests/418.354秒終了0。新idの原本/候補API/copy回帰・旧id2件のcompile負例、旧frontend3673、Add compose/id4072×2、原本/候補MaxMin apply各4080/4080/4100/4100。C++/UBSan・入力hash不変、receiptは任意T/M/lifetime/全体未完を明記。共有検査は新API check追加で243件（全件gateは未再実行）。

- `.cache/wip/extrema_set_general_20261109/registered/`: 実76341はfresh原本4具体化のkernel4080/4080/4100/4100・C++/UBSan・入力hash不変で166.179秒終了0。Add/Set applyの任意caller・全scalar/vector保持・const結果・scope/peak・総work増分≤14/21。Set rawはnoop9/代入12、need≤P.length+13、prepare2参照+1値は7work。privateのraw/prepare単体は2759×2、caller草案もcompile成功。全体未完了と任意T/M/lifetime未検証はreceiptに明記。



- `.cache/wip/contract_review_20261109/`: 旧モデル/Pow/Call/Opsと現Componentを別olean領域へbuildし、旧契約2481宣言を不一致0で再現。既存named theorem133件の型変更は9件。公開ModInt34件では本体等式1件以外同一。tail/加減乗/汎用callerの正確な状態にcaptureセルを含め、除算callerのhbodyはcapture2回へ更新、入力/結果/数値上界は保持。review.jsonにソース/契約hashと判断、旧契約はstatements.before.json。契約のroot2481件は不変、14変更5追加のみ同期。

- `.cache/wip/library_layout_20261109/`: 旧doublingパスと変異scratch配置を修正。full_gateの実54494は共有242件成功後に最終closure照合で終了1。secrets/check.pyは変更対象全ファイルの変更前後・差分・未push履歴を検査（件数とhashはreceipt/inputs.json）。全ファイル版の生検出2件は変更前後のProofs.MultiVecN.rowKeyの公開宣言digestで、HEAD/現契約/検査済Lean環境からの再計算一致を確認。認証情報0件、疑似tokenの対照1件。生検出と根拠はnoncredential_findings.jsonに保持。inputs.jsonのhash時点の検査根拠であり、その後の編集には適用しない。

- `.cache/wip/modint_discard_20261108/`: 元モデル/Pow/Call/Opsのsnapshotとbuild harness。37305はPow build終了0。penv_pushed/returnedCopies/pushedCopies/returnedCopies_execを共通化し、div_exec_copiesで戻り値コピー数≤2を扱う。実16423のCallと23883のOpsがbuild成功。pushed/returnedCopiesでret captureを全PS・費用・領域に含め、従来の数値上界は維持。実41493のregistered_check.pyはbuild/bridge/CPP/36roots6172宣言のkernelと入力hash不変で終了0。registered/{inputs,receipt}.json参照。旧full_gate/run_checks.pyの実58423は終了1。配置変更の残存パス修正後、20261109の別dirで再検査する。次段の未検証draftは.cache/wip/extrema_template_general_20261108/{add_raw,prepare_ref_value}.draft.lean。検査対象へは未反映、全件gate後にfresh生成モデルでcompile/kernel検査してから登録する。C++原本/公開headerは今回変更なし。
- `.cache/wip/library_layout_20261108/`: moves.jsonで118ファイルの移動とヘッダ58同一/1include変更を確認。登録59・登録基盤19tests成功。実38333はinventory0/all1（全件gate未完）。all.logは59CPP成功とModInt橋渡し失敗を記録。modint_relocation.jsonで同じ旧配置でも生成差分が存在することを確認。実70116は58bridge/ZIP収録59件・単独/一括include検査をすべて終了0で回収済み。relocation_state.json参照。この旧配置検査のjobは終了済み。機密検査は同dir secrets/check.py、inputs.json/receipt.jsonで最終hashと結果を確認。
- `.cache/wip/member_template_result_20261108/new/`: 新3tests/161.944秒終了0。元Add/Set×Max/Minはnanoda2825宣言×4、custom2field copy/constructは2817。native/UBSan、未具体化型・不正要求・副作用条件の拒否、入力hash不変が成功。
- 同 `related/`: 実29467は18tests/350.508秒終了0。nanoda 2815/2811/4126/4104/4102/4102/4072/4072/4086/4316/2834/2648/2820。Sum caller・const/prefix・constructor/factory・class-copy/union_find・同名record拒否が成功。私的harnessの旧base置換漏れで古いrelatedのinputs/logを上書きしたため、今回の正本をこの新relatedへ複写済み。旧16testsのreceiptだけはlegacy_related_receipt_84162.json、旧hash根拠には使わない。
- `.cache/wip/member_apply_call_20261108/registered/`: Sum applyとcomposeの3tests/209.825秒終了0。Set apply4126/Add apply4104、compose4072×2/4102×2。Add総IR work増分≤24/Set≤25。新共有prepare補題の最終proof-security/root照合と全件gateも20261109に成功。
- `.cache/wip/tree_lca_rows_20261108/registered/`: 新3rootsと既存LCA callerのnanoda5277、2tests/11.602秒終了0。旧上限だけ戻した4頂点負例は境界assertで失敗、修正後成功。TreeLcaCallのbuildも成功（既存依存の非推奨警告あり）。
- 配置変更前の共有240 checksの旧結果は、現在の成功根拠には使わない。現在の全件成功は20261109/final_gate。機密検査の現時点の根拠は20261109/secretsのinputs.jsonであり、後続変更は最終hashで再検査する。

## 原本ごとの進捗と懸念

L=`experiments/library/cpp/`、L3=`experiments/library3/cpp/`。公開部分ありでも元class全体の検証は未完了。詳細・証拠は [原本台帳](../verification_inventory.json)、[移植違反一覧](../experiments_status.md)、[問題点](../experiments_findings.md)、[修正記録](fixes.md)。

| 原本 | 進捗 | 懸念・残件 |
| --- | --- | --- |
| `L/algebraic_structure/group.hpp` | 完了（整数具体化 long long・int） | 2026-11-09 intを追加、全定理を証明、全件gate成功。浮動小数Tは基盤整備後 |
| `L/algebraic_structure/monoid.hpp` | 完了（整数具体化 long long・int） | 2026-11-09 intを追加し全定理証明、全件gate成功。浮動小数TはC++回帰のみ、Leanは基盤整備後 |
| `L/algebraic_structure/monoid_lazy.hpp` | 進行中 | Sum applyの任意caller接続済み。MaxMin apply<M>はLL全入力（Addは加算範囲内）・任意caller接続まで。元API候補はexperimentalにあり、任意T/M・lifetime・公開切替は未 |
| `L/array/cumulative_sum.hpp` | 完了（整数具体化 long long・int） | 2026-11-11: `verifier/vector_bindings.py` の `merge_type_probes` で同位置・同実体の型probeを論理和に統合し `int` 具体化を生成。`Proofs/CumulativeSum{,2D}Int{Exec,Call}.lean` に i32 版の全定理（s64 固定の準備補題 `prepare_fs/frr/ft`・`mvFT`・`fwFT_init`・`mvV2D`・`fwV2D_init` は i32 複製を同ファイルに置く）。他の整数型・浮動小数Tは基盤整備後 |
| `L/array/doubling.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/array/element_count.hpp` | 部分 | 候補あり。原本API全体の生成/証明/公開判定は未 |
| `L/array/search_util.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/array/sort_util.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/fps/convolution.hpp` | 未 | NTT/FPSの元API・modint依存と計算量の生成/証明は未 |
| `L/geometry/line.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/geometry/polygon.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/geometry/vector.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/bellman_ford.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/dijkstra.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/edge.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/edge_flow.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/find_cycle.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/graph_flow.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/graph_list.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/graph_matrix.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/lowlink.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/prim.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/topological_sort.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/warshall_floyd.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/interval/interval.hpp` | 完了（stream演算子は方針で対象外） | 2026-11-09 `==`/`!=`/`<`/`>`/`<=`/`>=` を追加し一般定理・全件gate成功（commit 171a6bb）。次は `L/interval/interval_union.hpp` など小さい原本から同じ流れ（C++追加→nested_irで生成→Lean定理→statements再生成→全件gate→commit） |
| `L/interval/interval_union.hpp` | 部分（着手調査済み） | 元APIの復元を選択（2026-11-09）。調査: `verifier/` に `pair` 対応が皆無。必要な拡張は (1) `vector<pair<T,T>>` を2要素recordの要素とするvector、(2) `std::sort` のpair比較契約（またはソートの内部モデル）、(3) 構造化束縛 `auto &&[l, r]`、(4) `emplace_back(l, r)` と `.back().second` 代入、(5) vectorの値返し。公開側は現状2本のvector＋挿入ソート（違反として一覧済み） |
| `L/modint/dynamic_modint.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/modint/modint.hpp` | 部分 | 公開ModIntの11モデル/一般証明を更新、bridge/kernel成功。全件gate成功。原本class全API/汎用型の移植は未完 |
| `L/number/ratio.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number/square_matrix.hpp` | 部分 | 比較・powの不具合とAPI型/traitを修正。候補の全class一般証明/公開切替は未 |
| `L/number_theory/enumerate_quotients.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number_theory/factorize.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/number_theory/floor_sum.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number_theory/is_prime.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/random/xorshift.hpp` | 部分（調査済み） | 台帳「済」は過大。公開版は `get()` のみ。2026-11-09の試験で `get_int`/`get_ll`（`get()` をthis呼出し）を足すと共通変換器はモデル生成に成功（`Xor64_get_int` 等、get本体をinline）。残り: 整数2メソッドのLean証明（divrem・u64→int32 cast・ma-mi オーバーフロー前提）と、`get_double`/`get_double(lo,hi)`/`get_normal`（pow/sqrt/log/cos、浮動小数のRat＋誤差予算の基盤が未整備） | 2026-11-10追記: `get_int`/`get_ll` は `signed_conversion = "gcc13.3-lp64-twos-complement"` が必要（`mi < 0` で `.cast` は失敗扱い、`.targetCast` なら正しい）。現状は `tools/public.py` が `state_ir` のみ許可、`verifier/nested_bridge.py` が `lower_source` に方針を渡さない。この2点を拡張すれば `nested_ir` でモデル生成に成功することを確認済み（`Xor64_get_ll` が `.targetCast ⟨64,true,false⟩` を含む）。残り: 参照1個＋値渡し2個の呼出し準備補題、本体の実行・結果（`mi + xnext s % (ma-mi)`）、int版、浮動小数2メソッド。
| `L/segment_tree/binary_indexed_tree.hpp` | 部分 | 公開Fenwickクラスに構築3種/add/sum2種、+=のみの型を保持。任意T・厳密lifetimeは未 |
| `L/segment_tree/lazy_segment_tree.hpp` | 部分 | 公開chmin/maxの部分検証。元のobject/全作用/search左右・汎用性は未 |
| `L/segment_tree/segment_tree.hpp` | 部分 | 公開版は値/静的policyへ変更。元のモノイドobject・search左右・全汎用性の復元は未 |
| `L/segment_tree/segment_tree_beats.hpp` | 進行中 | 構築→15vector/2scalar export・6操作→receiver復元まで。Safe導出・任意操作列・償却/総資源・全lifetime/公開切替は未 |
| `L/segment_tree/segment_tree_beats_sum.hpp` | 未 | 別原本の全API/償却・重複統合を未確認 |
| `L/set/multiset.hpp` | 未 | std::multiset契約・元APIの変換/証明が必要 |
| `L/set/set.hpp` | 未 | std::set契約・元APIの変換/証明が必要 |
| `L/string/char_count.hpp` | 部分 | 局所監査のみ。標準string操作と汎用性の生成/証明は未 |
| `L/string/rolling_hash.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/tree/tree.hpp` | 部分 | LCA上限修正と全行降下定理/全対C++成功。元class全体・singleton構築・cost型/直径等は未 |
| `L/union_find/disjoint_set_union.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/union_find/union_find.hpp` | 部分 | 公開クラスの経路圧縮/統合・5scalar/3vector連携を検証。全原本/汎用型/lifetime監査は継続 |
| `L3/AlgebraicStructure/Group.hpp` | 部分 | 有限LL・Affine<int>の生成/一般caller済み。任意T・全object/lifetimeは未 |
| `L3/AlgebraicStructure/Mapping.hpp` | 部分 | Affineの値渡し/型変換を維持して有限具体化。任意T/全objectは未 |
| `L3/AlgebraicStructure/Monoid.hpp` | 部分 | library3の有限LL具体化を監査。任意T・全object/lifetimeは未 |
| `L3/Array/CumulativeSum.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Array/SortUtil.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Geometry/Point.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/BellmanFord.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/Dijkstra.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/GraphL.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/GraphM.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/Lowlink.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/Prim.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/TopologicalSort.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/UnionFind.hpp` | 部分 | 有限クラス変換と公開版との差を確認。元版の全API/検証完了監査は未 |
| `L3/Graph/WarshallFloyd.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/ModInt/ModInt.hpp` | 部分 | 公開ModIntのモデルずれは単体検査成功。元版の全API/汎用型への適用は未完 |
| `L3/NumberTheory/Factorize.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/NumberTheory/IsPrime.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/SegmentTree/SegmentTree.hpp` | 部分 | 元版の全API/型の保持と公開版との差の解消が必要 |

テンプレート6件（L/L3各3件）とdriver65件は原本台帳で別管理。テンプレート自体の全検証と型/マクロ/乱択契約は未完。driverのコンパイル成功は依存ライブラリの証明には数えない。

## 詳細資料

- [元template class](../original_template_classes.md)、[class copy/constructor監査](../class_copy_audit.md)、[Beats候補](../beats_wide_candidate.md)、[信頼境界](../trust_policy.md)
- [CI/リリース記録](ci_release_handoff_20261103.md)は過去の経過資料。現行のpush粒度と再開地点はこの文書を優先する。
- 古い履歴は [11月1日以前](handoff_history_20261101.md)。今回の上書き前snapshotは `.cache/wip/library_layout_20261108/handoff_before.md`（ローカルのみ）。

- 2026-11-10: `Proofs/GenericCall|GenericLazy|GenericExtrema|SortPairsFrame` を `verifier/support.toml` の `lean_modules` に登録し、`verification/statements.json` を再生成（`NStmt` の sortPairs 追加分の既存ダイジェスト変更を受け入れ）。`tools/check_proof_security.py` 成功（約750秒、フル再構築時）。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: apply系の add フィクスチャ（`generic_extrema_add_apply`, `generic_sum_add_apply`）に、任意の符号付き `ty` で和が範囲外なら最初の宣言で fault する定理 `raw_sum_overflow_faults` を追加（`tests/test_generic_template_family.py` の該当2テスト成功、公理は標準3種以内）。未了: 引数スロット欠落の拒否、符号なしの折返し、`RangeAdd_id`/`RangeMax`/`RangeMin` の group/monoid 依存部、変換器の `prog (t : Ty)` 直接出力、公開側への切替。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: apply系4フィクスチャに引数オブジェクトの拒否定理（`missing_argument_object_rejected`, `extra_argument_object_rejected`, `incomplete_argument_rejected`, `vector_argument_rejected`）を任意 `ty` で追加、該当4テスト成功。apply系の「受け手・引数スロット欠落」拒否は完了。残り: 符号なし折返し、`RangeAdd_id`/`RangeMax`/`RangeMin` の group/monoid 依存部、変換器の `prog (t : Ty)` 直接出力、公開側への切替、浮動小数 `T`。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: add系2フィクスチャに、符号付き/符号なし/bool を一括して扱う `raw_exec_conv`（`ty.convert` の結果を仮定）と、符号なしの折返し（mod 2^width）を直接述べる `raw_exec_wrap` を追加。成功条件の一般化は本体（raw）層まで。`ObjectView` 層（`view_export_correct`/`object_export_correct`）の折返し版は未了。残り: `RangeAdd_id`/`RangeMax`/`RangeMin` の group/monoid 依存部、変換器の `prog (t : Ty)` 直接出力、公開側への切替、浮動小数 `T`。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: add系2フィクスチャの view/object 層まで折返しを一般化（`stage_ready_conv`/`view_export_correct_conv`/`object_export_correct_conv`＝`ty.convert` の結果を仮定、`object_export_wrap`＝符号なしで `mod 2^width` した値をエクスポート）。apply系4件の一般化は符号付き・符号なし・fault・拒否まで完了。残り: `RangeAdd_id`/`RangeMax`/`RangeMin` の group/monoid 依存部、他ファミリ（ctor/factory/compose 等）の折返し版、変換器の `prog (t : Ty)` 直接出力、公開側への切替、浮動小数 `T`。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: `generic_add_compose.lean` を `s`＋`hc : ty.convert (x+y) = some s` で既存定理ごと一般化（範囲内は `s = x+y` の特殊例）、`object_compose_wrap`（符号なし折返し）を追加。残りの算術を含むfixture: `generic_add_sum`, `generic_friend_op`, `generic_record_apply`, `generic_set_apply_sum`, `generic_sum_set_apply`（`product` を含む）。

- 2026-11-10: 共有補題に折返し版を追加。`Proofs/GenericCall.lean`: `convert_valid`, `convert_wrap`, `addG_den_conv`, `rangeadd_compose_conv_gen`, `addG_den_overflow`。`Proofs/GenericLazy.lean`: `rangesum_op_x_conv_gen`, `rangeadd_applyExt_conv_gen`, `rangeadd_applySum_conv_gen`, `rangeset_applySumX_conv_gen`（`ty.convert` の結果 `s`/`q` を仮定。公理は標準3種）。次はこれらを使うfixture（`generic_add_sum`, `generic_friend_op`, `generic_record_apply`, `generic_set_apply_sum`, `generic_sum_set_apply`）の in-place 一般化。

- 2026-11-10: 算術を含む全 generic フィクスチャ（`generic_add_sum`, `generic_friend_op`, `generic_record_apply`, `generic_add_compose`, `generic_set_apply_sum`, `generic_sum_set_apply`, add系apply2件）を `ty.convert` の結果（`s`/`q`/`s13`）を仮定する形へ一般化済み（範囲内は特殊例、符号なしの折返しは `convert_wrap`、符号付きの範囲外は `addG_den_overflow` 等でfault）。折返しの直接版（`*_wrap`）は add_compose/add_apply 2件のみ。残り: 変換器の `prog (t : Ty)` 直接出力、`RangeAdd_id`/`RangeMax`/`RangeMin` の group/monoid 依存部、公開側への切替、C++ のオブジェクト寿命の厳密検証、浮動小数 `T`。`monoid_lazy.hpp` は未完（`[x]` 未記入）。

- 2026-11-10: **公開側切替の設計メモ（`monoid_lazy` の元のネストAPI）**。レジストリの翻訳方式は `state_ir`/`nested_ir`/`context_class_ir` のみ（`tools/public.py:50`、`verifier/nested_bridge.py`）で、ネストしたクラステンプレート（`RangeAddRangeSum<T>::RangeSum` 等）は表現できない。公開するには新しい翻訳方式（例 `template_class_layout`）が要る: (1) `tools/public.py` で方式・bridge・宣言名（ネスト名）を許可、(2) bridge は登録した各インスタンス（family×T）について `emit_class_layout`/`lower_template_class` を再生成して `Proofs/Generated/*.lean` と一致を確認、(3) 現在 `tests/lean/generic_*.lean` にある一般証明を `Proofs/` のモジュールに移して `proof` に登録、(4) `public_declarations` にネスト宣言、(5) `statements.json` 再生成、(6) テスト・docs・check_public 全件。`tests/test_generic_family_*.py`（31本）は `support.toml` の `checks` に登録済み。T の対象は変換器の整数4種（`short`/`char`/浮動小数は未対応）。

- 2026-11-10: **公開側切替のアーキテクチャ（次の着手点）**。生成モデル（`emit_class_layout`）約1400行のうち、`MemberCopy`（約1000行）・`MemberView`・`MemberFactory`・`Stages` は T/family に依存しない固定の補助コード（`verifier/class_copy_layout.py` の定数）。(A) これを共有モジュール `Proofs/Member*.lean` に出し、生成物は `import`＋`open` する（インスタンス固有の `def`・`exportViewFuel` 等だけ約400行）。(B) `tests/lean/generic_*.lean` の一般証明は、生成名前空間にテスト側で貼り付ける現行方式をやめ、`ty` 族（`gApply ty` 等）だけを参照する共有 `Proofs/` モジュールとして1回だけ証明する（`lake build` が+1時間にならない）。(C) 新翻訳方式 `template_class_layout` は、登録インスタンス（family×T、T=変換器の整数4種）ごとに生成モデルを再生成して照合し、族との `rfl` 一致（現 `tests/test_generic_family_*.py` 相当）を検査する。(D) 最後に `library/` を元のネストAPI（std:: 修飾、`ll`→`long long`）へ切替、`public_declarations`・tests・docs・statements.json・全件gate。

- 2026-11-10: **公開側切替を、別アーキテクチャで実現**。`library/algebraic_structure/monoid_lazy.hpp` に元の入れ子API（4 family。`std::` 修飾と `ll`→`long long` のみ差）を追記し、既存の平らなクラスは簡便APIとして維持（`nested_ir` モデルは未インスタンス化のネストテンプレートを無視するため不変）。`monoid_lazy.toml` の `source_sha256`/`public_declarations` を更新、`tests/monoid_lazy.cpp` に入れ子APIの検査を追加、`tests/test_monoid_lazy_original_api.py` は公開版と原本のトークン一致＋全driver実行に変更（`check_public --component monoid_lazy --mode cpp` 成功）。共有補助 `Proofs/MemberSupport.lean`（`emit_class_layout(shared_support=True)`）と、一般証明の共有モジュール `Proofs/MonoidLazyGeneric/*.lean`（23本）を追加（`support.toml`・`Proofs.lean` に登録済み、`tools/public.py` の共有モジュール置き場に `Proofs/MonoidLazyGeneric` を許可）。次: フルgate（`check_proof_security.py`・`check_public.py --mode all`）、`tests/test_generic_family_*.py` を共有モジュール利用に簡素化（任意）、`[x]` 付与の判断。

- 2026-11-11: 全件gateで独立kernel（nanoda）がスタックオーバーフロー。原因は `Proofs/MonoidLazyGeneric/AddSum.lean` の `e_correct`/`default_correct` が `i32.valid 0 = true` を `rfl`（`2^31` 等の評価）で示していたこと。`Proofs.GenericLazy.valid_zero i32` に置換（スタックは増やさない）。切り分けは export の root を module ごと→宣言ごとに絞って nanoda を単独実行（`/tmp/bisect/run.py` 相当: lean4export `Proofs -- BUILTINS permitted names`、cwd はリポジトリ直下）。**教訓: 独立kernelでは具体的な幅の `Ty.valid` を `rfl`/`decide` で示さず、一般補題を使う。**

- 2026-11-11: **`monoid_lazy.hpp` を verify 完了**（チェックリスト `[x]`、コミット 83dbf50）。全件gate成功: `check_public.py --mode all` 59部品、独立kernel 51499宣言エラーなし（セキュリティ検査約850秒、他はキャッシュ）。範囲: 元の入れ子API公開、任意 `ty` の一般証明＋整数4種の生成モデル全数照合。残す制約: `short`/`char`（変換器が整数拡張未対応）・浮動小数T・C++の厳密なオブジェクト寿命（コピー/破棄回数）は未検証として `docs/monoid_lazy.md`・`docs/experiments_status.md` に記載。push は未実施（手動承認待ち）。次のチェックリスト対象は `experiments/library/cpp/array/cumulative_sum.hpp`。
- 2026-11-11: Lean検証時間の改善候補（AGENTS.md の継続改善方針）: キャッシュ無効時の `tests/test_template_class_layout.py` が単独1853秒（40ケースがそれぞれ固定nanoda約4100宣言を再検査）。`verifier/*.py` のどの変更でも再実行されるため、(1) キャッシュキーを実際に import する verifier モジュールに限定、(2) 同一生成モデルの kernel 検査を共有、(3) ケースを family 単位にまとめる、を検討する。`cumulative_sum` の i32 証明4ファイルは各1分未満。
- 2026-11-11: **`cumulative_sum.hpp` を verify 完了**（整数具体化 long long・int）。全件gate成功: `check_proof_security.py` と `check_public.py --mode all` 59部品（7200秒上限を1回超過したため2回に分けて実行、失敗なし）、独立kernel 51883宣言エラーなし。statements は既存命題の変更なしで7定理追加。push は未実施。次のチェックリスト対象は `experiments/library/cpp/array/element_count.hpp`。

- 2026-11-11: **`element_count.hpp` を移植**（公開 `library/array/element_count.hpp`、具体化 `std::vector<long long>`・`std::vector<int>`）。原本は要素型に `T`（コンテナ型）を使う不具合で標準コンテナに具体化できなかったため、`typename T::value_type` に修正（引数 `const T &v` は元のまま。`docs/agent/fixes.md`）。変換器: `vector<pair<A,B>>`（範囲が入れ子の整数型）を広い型の2行で表し狭いフィールドは拡大変換で格納（狭いフィールドの読み書き・sort・範囲forは拒否、引数は同型pairのみ）、戻り値の `typename std::vector<X>::value_type` を型probe付きでXへ、宣言のないブロックからのvector返却はスコープなしで下げる（`NState.leave` は退出スコープの根しか移さないため）。Lean: `Proofs/AppendCapacity.lean`（容量上界つき行追加）、`Proofs/FamilySteps.lean`（Family上の宣言/代入/条件）、`Proofs/ElementCountExec.lean`（行型tyと行1の式cvについて一般の本体証明）、`Proofs/ElementCountCall.lean`（`element_count_ll_correct`/`element_count_int_correct`: 結果の2行=rleの値/長さ、vの不変、仕事量・領域の線形上界、公理は標準3種）。`statements.json` は既存命題の変更なしで57定理追加。全件gateで lean4export の引数が ARG_MAX（2MiB）を超えたため、`tools/check_proof_security.py` で根を被覆集合へ縮め出力後に全宣言の包含を検証する形にした（`docs/proof_security.md`）。

- 2026-11-11: **CI の短縮と検証方式の見直し**。(1) CI を16シャード＋最終監査ジョブに分割（`tools/ci_shards.py`、重み `tools/ci_weights.json` は CI ログから `python3 tools/ci_shards.py update LOG...` で更新）。(2) CI の `LEAN_NUM_THREADS=1` で Lake がモジュールを1つずつビルドしていたため、`PROOF_BUILD_THREADS`（CIはコア数）で証明ビルドだけ並列化（冷えた全ビルド 44〜80分→約22分）。run 42994061436 は約2時間→62分（ほぼ全モジュールの再ビルドを含む）。(3) ユーザー決定で方式を変更（`docs/redesign_2026-11.md`、AGENTS.md 反映済み）: モデル証明＋制限構文の機械翻訳、整数範囲は前提、寿命・ヒープ領域は対象外、計算量はオーダー、全ビルド込みCI 30分以内。(4) `segment_tree_beats` の公開を取り下げ（旧証明228モジュール・約50%を削除、`statements.json` は削除のみ）。pushed: 722e957（CI分割）, ab698a6, 30e96f9, 1642172（重み更新・`cold_build` 手動実行入力）。local main は element_count の17コミットが未push（全件gate未完了、作業ツリーの `check_proof_security.py` の ARG_MAX 対策も未コミット）。次: 冷えたビルドの計測（workflow_dispatch `cold_build=true`）、新方式の翻訳器を小さい部品で試作。

- 2026-11-11（続き）: **全件CIが冷えた全ビルド込みで30分以内**。不要な旧方式の証明（寿命・コピー・ムーブ・ピーク領域・所有者/エイリアス）とその検査を削除し、`segment_tree`・`lazy_segment_tree`・`find_cycle` も検証待ちとして取り下げ（`docs/redesign_2026-11.md`）。計測: push run 43020608471 は12.5分、`cold_build=true` の run 43022586938 は22.4分（全ビルド735秒、kernel再生310秒、独立kernel 116秒）。公開55部品。pushed head 7e378fd。local main は element_count の17コミットが未push（全件gate未完了、作業ツリーの `check_proof_security.py` の ARG_MAX 対策も未コミット）。次: 新方式の翻訳器を小さい部品で試作し、取り下げた4部品（beats を含む）を新方式で再公開する。部品を足すたびに冷えたビルドを計測する。

### 2026-11-15 Ratio乗除算の純粋モデルと生成対応

- 前回は進捗あり（全API候補、算術・stream証明と差分検査）。継続して `Proofs/Cpp/Lib/RatioMath.lean` に exact cancellation、非ゼロ商、交差約分mul/divモデル、積・商の値、除算のcanonical fieldsを追加（6定理、既存と合わせ17）。除算はd≠0・m≠0で証明し、入力eの非ゼロはこの等式には不要。乗算の値は両分母≠0で証明するが、未正規化入力の乗算結果のcanonical性は主張しない。
- `tests/lean/ratio_arithmetic_contract.lean` に生成 `*=`/`/=` のexact runと値の4定理を追加（合わせ18）。成功を仮定せず、前提からsome結果の存在と停止を示す。仕事量は2回のnumericGcdCost（除算はnormalize分も）を保持し、std::gcdの未規定上界を決め打ちしない。
- shared moduleのlake build成功（葉1.2秒）、fresh全API生成モデルに算術18定理を連結した直接Lean検査成功。公開側は旧3フィールドのまま。次は比較・等値、二項/スカラーwrapperの仕様、型対応と計算量根拠、全API公開への切替。全件gate/独立kernel監査/CI20分とpushは未実施。
- 更新後のstream/model契約テストは7件すべて成功（ログ `.cache/wip/ratio_restore/stream_harness.log`）。差分ハーネス、ASan/UBSan、fresh生成との対応を同じ入口で再検査した。

### 2026-11-15 Ratio比較・等値

- 前回は進捗あり（乗除算の純粋モデルと生成対応）。今回 `RatioMath` に正分母のGCD約分比較の≤/<対応と、正規化結果の等値iff有理数値等値を追加（数学層20定理）。`ratio_arithmetic_contract.lean` に比較のexact run/値、任意Tのフィールド等値判定、正規化済み入力の有理数等値との対応を追加（算術層22定理）。shared module buildと生成候補連結のLean検査成功、警告なし。
- 入力operator>>はnormalizeしないため、2/4と1/2のフィールド等値は偽、比較はequalであることを保持。stream差分テストにこれと負数の大小の両方向を追加した。公開側は旧3フィールド版のまま、全APIの移植完了ではない。
- 次は二項/スカラーwrapperの仕様、全型の対応、GCD/LCM費用根拠と計算量オーダー、全API公開切替・全件gate・独立監査・push後CI20分測定。push未実施。
- 検証結果: stream/model契約7件成功（37.244秒）。追加した未正規化比較ケースを含む汎用streamハーネスの単独再検査も成功。int/long longのC++ ASan/UBSanとLeanの出力一致、py_compile・diff --check成功。全体gateや独立kernel監査の代用とはしない。

### 2026-11-15 Ratio二項/スカラーwrapper

- 前回は進捗あり（比較・等値証明）。今回は四則それぞれのRatio/Ratio・Ratio/T・T/Ratioの12形について、任意Tの生成関数が複合代入のrunを呼び結果を射影することを証明。スカラー構築込みの追加仕事量は2、Ratio同士は1、非帰還もOption.bindで保持する。
- 同じ12形に整数有理数値の仕様を追加。前提からsome結果・仕事量の存在を示し、加減乗除と一致。scalar castはRat.divInt_oneで接続し、可換性を仮定して減算/除算の左右を入れ替えない。さらにゼロ除数の複合代入と3wrapper形のrun=noneを証明（assertで失敗する入力を成功扱いしない）。算術契約は22→50定理。fresh生成連結の直接Lean検査成功（警告なし）。
- 未完: 原本全Tへの整数表現対応・乗算等のcanonical不変条件・GCD/LCMの時間上界と領域のオーダー・公開header/TOML切替・statements再生成・全件gate/独立監査・push後CI20分計測。他の旧方式部品と取り下げ4部品等も残る。公開Ratioは引き続き旧3フィールド、pushなし。
- 検証: wrapper追加後のstream/model契約7テスト成功（37.809秒、ASan/UBSanとLean差分を含む）。最後に加えたゼロ除数4定理も含めた全50算術定理は直接Lean検査で成功。`git diff --check`成功。公開側の全件gate/独立kernel監査は未実施。

### 2026-11-15 Ratio正規化不変条件

- 前回は進捗あり（二項/スカラー全12形とゼロ除数）。今回 `RatioMath.Canonical n d := 0 < d ∧ Int.gcd n d = 1` を定義。normalizeの成立、canonical fieldsとの一致、normalize固定点、増減・加減・除算での保存を証明した。
- 乗算はLean標準Rat.mulの交差約分実装とのフィールド一致を証明し、canonicalな両入力から積のcanonical fieldsと不変条件保存を導出。Int.tdiv/edivの差はGCDによる除算の整除性で解消。未正規化のstream入力について保存を仮定していない。
- 生成モデルの前後置増減4形について、返値と更新されたreceiver両方のcanonical性、値、停止とexact ticksを接続。生成mul_assignについても値・canonical性を接続。数学層20→31定理、算術層50→55定理。shared module build成功（葉1.3秒、警告なし）。
- 未了: 全T/固定幅と数学Intの対応、GCD/LCM費用上界と時間・追加領域のオーダー、全API公開header/TOML/テストへの切替、statements再生成と全件gate/独立監査。その後に原本単位pushとCI20分確認。他の旧方式部品と取り下げ4部品等も残る。公開Ratioは旧3フィールドのまま、pushなし。
- 最終検証: 更新後のstream/model契約7件が成功。fresh全API生成に算術55定理＋stream契約を連結してLean検査、C++ ASan/UBSanとのdiffも同じ入口で成功。`py_compile`と`git diff --check`成功。最終spec/security監査や全件gateの成功とは扱わない。

### 2026-11-15 Ratio型別検査と除算の接続

- 前回は進捗あり（canonical不変条件と乗算）。今回はdiff_harnessの数値stream実現にshort/short intの16bit境界を追加。shortを32bit intと同一の抽出へ落とさず、範囲外の読取りは[-32768,32767]へ切詰めとfailで検査する。既存の正負範囲超過/EOF/不正/未正規化比較ケースをshort/int/long longで行う。char/signed charは文字抽出なので引き続き拒否。unsignedと幅混在も未対応。
- RatioMathへLCM共通分母の左右の除算が整除によりInt.tdiv/edivで一致する2定理を追加（数学層33定理）。GCDの対応と合わせ、Ratioの負数の丸め差を説明する。shared build成功（葉1.3秒、警告なし）。docs/translation.mdの古い「乗除算・比較・ラッパー未証明」の記述を現在の証明範囲へ修正。
- 未了: 全T/固定幅の数学モデル対応をこの有限差分検査で証明したとはしない。GCD/LCM費用の時間上界・追加領域、全API公開切替、全件gate/独立監査、push後CI20分が残る。公開Ratioは旧3フィールドでpushなし。
- 検証結果: short追加後のstream/model契約7件成功（46.913秒）。3型のC++ ASan/UBSanとLean差分一致、fresh生成との契約証明、py_compile、diff --check成功。追加したLCM2補題はshared module buildでも検査済み。

### 2026-11-15 Ratioの明示GCD/LCM候補

- 前回は進捗あり（shortの型別streamとLCM整除）。std::gcd/lcmには時間上界規定がないため、差し替え候補 `experiments/verification/number/ratio_numeric.hpp` にtemplateのEuclid/符号処理/LCMを用意した。公開部品ではなく、最終的にはRatioの非公開helperへまとめる。原本の公開APIは変えていない。現全API候補もstd版のままで、まだ差し替えていない。
- `tests/lean/ratio_numeric_contract.lean` は毎回生成したモデルについて、非負GCD・符号付きGCDが正しい値を返して停止し、仕事量がそれぞれt+2+gcdCost / t+3+gcdCost以下であることを証明。既存gcdCostはlog2(a*b)+最大2なので、STLの費用仮定に頼らない。whileモデルのfuel制約はb.toNat/natAbs<2^64として明示（標準の符号付き64bit値は範囲内）。mvcgenの実験的tactic警告のみ、証明の未解決goalなし。
- `tests/test_ratio_numeric_model.py` をsupport checksへ登録。生成モデルへ証明を連結してLeanで検査し、190入力×3関数×short/int/long longをPython math.gcd/lcmと照合。C++ ASan/UBSanとLeanの差分も検査する。0、負、互いに素、Fibonacci、short境界を含む（最小負数のabsやLCMオーバーフローは契約外として除外）。
- 次はLCMの正しさ・時間上界、helperの型一般対応とRatio内部への組込み、既存算術契約の費用式更新、追加領域オーダー、全API公開切替・全件gate/独立監査・push後CI20分。公開Ratioは旧3フィールド、push未実施。
- 最終検証: 符号付き証明追加後の2テストが10.032秒で成功。fresh生成との2証明、Python期待値、3型のC++ ASan/UBSanとLean一致、py_compile/diff --check成功。全件gate/独立kernel監査は未実施。

### 2026-11-15 Ratio LCM補助の証明

- 前回は進捗あり（明示Euclidと符号付きGCD）。今回 `RatioMath.lcm_magnitude_formula` を追加（数学層34定理）し、絶対値をGCDで割ってから掛ける式とInt.lcmが一致することを証明した。
- staging ratio_lcmは既に絶対値を取った後の呼出しをratio_gcd_nonnegativeへ変更し、重複した符号処理/入口tickを省いた。生成モデルの `ratio_lcm_signed` は0入力・正負4分岐を含めてInt.lcmとの一致、停止、t+3+gcdCost(|a|,|b|)上界を証明。GCD/LCMのSTL時間仮定を使わない。gcdCost≤2+log2(a*b)も明記した。whileのb.natAbs<fuel制約は維持。
- `tests/test_ratio_numeric_model.py` はfresh生成にRatioMathをimportしてLCM証明も検査する。190入力×3関数×3型のASan/UBSan・Python・Lean照合を継続。
- 次はこのhelperをRatioの非公開関数へ組込み、既存の算術/stream契約をfresh生成モデルへ接続して費用式を更新する。元template/APIを保持し、候補の本体同一テストは許可したGCD/LCM置換を明示して修正する必要がある。追加領域・全型対応、公開切替/全件gate/独立監査、push後CI20分は未完了。公開Ratioも全API候補もまだstd版のままでpushなし。
- 最終検証: LCMとlog上界を含めた更新後の2テスト成功。freshモデルとの4定理、190入力×3関数×3型のPython/C++ ASan/UBSan/Lean一致、py_compile、diff --check成功。mvcgenの実験警告と既存simp分岐のlinter警告は残るが、未解決goalなし。全件gate/独立kernel監査は未実施。

### 2026-11-15 Ratio全API Euclid候補の組込み

- 前回は進捗あり（明示LCMの証明）。`experiments/verification/number/ratio_euclid.hpp` に全APIを保持した別候補を作成し、3個のnumeric helperをRatioの非公開static関数へまとめた。std呼出しをこのhelperへ置換し、不要なnumeric includeを除いた以外は既存std版候補と一致することをテスト。既存std版は55算術契約の比較基準としてまだ残す。最終公開は1headerにまとめる。
- 翻訳器はDeclRefExprのstatic CXXMethodDeclを名前でなく宣言idで解決。別クラスの同名staticへの誤対応は拒否。std::numeric_limits::max等の既存契約は従来の明示ハンドラを通す（最初の再生成チェックでここを検出して修正）。同名自由関数とprivate staticのnative/Lean回帰、および別クラス参照を誤受理しない負例を追加。
- `tests/test_ratio_euclid_model.py` をsupport登録。fresh全クラス生成でprivate helperの4定理とstream2定理を接続。`tests/lean/ratio_euclid_contract.lean` にnormalize/2引数構築/単項マイナス/乗算の4仕様を追加。純粋モデルのフィールドに一致し、仕事量はそれぞれ4+gcdCost、5+gcdCost、6+gcdCost、7+2個のgcdCostで上から抑える。停止とhelperのfuel前提を含み、NumericCost仮定は不要。
- 検証: Euclid候補4テスト40.117秒、既存friend8テスト26.922秒、更新したstatic宣言identity回帰1テスト2.352秒すべて成功。単独include・既定型・自己除算と、short/int/long longの入出力/未正規化比較のASan/UBSanとLean差分も実行。登録50モデルの再生成一致、py_compile/diff --check成功。
- 次はEuclid版の加減・除算・比較・全wrapperのモデル/費用接続と型一般対応、追加領域上界。全API公開header/TOML/テスト切替とstd候補/一時helper整理、全件gate/独立監査、原本単位pushとCI20分測定が残る。公開Ratioは旧3フィールド、pushなし。他の旧方式部品と取り下げ4部品等の目標も維持する。

### 2026-11-15 Euclid版Ratioの残る演算

- 前回は進捗あり（全API Euclid候補とnormalize/構築/負号/乗算）。今回 `ratio_euclid_contract.lean` に加減・除算・比較の仕様を追加。結果は既存純粋モデルのフィールドに一致し、仕事量上界は加減8+GCD(d,e)+GCD(z,l)、除算11+GCD(n,m)+GCD(d,e)+GCD(z,w)、比較4+GCD(d,e)。GCD表記はgcdCostの評価値。途中のl/wを含むwhile燃料前提を明示し、成功を仮定せず停止を示す。
- 全12形の二項/左右scalarラッパーに任意Tのrun対応を追加（複合代入の状態・非帰還・費用を保持、追加tickは1/2）。scalar構築・前後置増減・単項plus・任意Tのフィールド等値・正規化済み等値の値・ゼロ除数4形の証明もEuclidモデルへ接続。Euclid算術契約は計32定理。fresh生成連結のLean検査成功（11.558秒、次に全テストでも再検査）。
- 全クラスを直接呼ぶ算術差分テストを追加。既存friendテストのFraction期待値を再利用し、入力用headerだけをEuclid全API候補へ差替える。これで全12形・複合代入・前後置・比較・自己除算を検査し、stream付きヘッダもそのまま生成する。
- 未了: これらを最終公開用Proofs/モデル/TOMLへ登録、C++型対応と追加領域オーダー、API全体の仕様catalog/両kernel監査、std候補/一時helper整理。公開Ratioは旧3フィールド、pushなし。全件再公開とCI20分目標は未達で、他の旧方式部品・取り下げ4部品も残る。
- 最終検証: Euclid全候補5テスト49.894秒、数値helper2テスト13.900秒で成功。32算術＋4helper＋2stream定理をfresh生成で検査。Fraction算術期待値、3型stream、helperのPython期待値とASan/UBSan/Lean差分が成功。py_compile/diff --check成功。最終仕様catalog/独立kernel監査や全件gateの成功とは扱わない。

### 2026-11-15 Ratioのbit数による仕事量上界

- 前回は進捗あり（Euclid算術32定理）。今回共有 `Proofs/Cpp/Lib/RatioCost.lean` を追加してProofs.lean/supportへ登録。各GCD引数≤2^bitsならgcdCost≤2+2*bitsを証明し、有限個のGCD費用の和が(overhead+2*calls)*(bits+1)以下になる一般補題も証明した。leaf build1.4秒成功。定数の費用インスタンスやSTLの未規定上界は使わない。
- Euclid候補の実演算に5個のbit上界定理を接続（算術32→37定理）。normalize≤6*(bits+1)、乗算≤11*(bits+1)、加減≤12*(bits+1)、除算≤17*(bits+1)。結果の純粋モデルとの一致と停止も同じ仕様に保持。bitsはGCDが読む入力・中間値の共通絶対値上界を表す。特に加減では共通分母l/分子z、除算ではz/wも含める。元入力だけのbit数へ多項式中間値評価を代入する証明はまだないため、入力のみの大きさによるオーダー完了とはしない。
- 検証: shared RatioCost build成功、5上界を含むfresh全API生成連結のLean検査成功（12.958秒）。今回C++本文/翻訳器は変更なし。追加領域上界、全型対応と公開用spec/catalog・両kernel監査、公開切替、全件gate、push後CI20分は未完了。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 Ratioの入力のみのbit上界

- 前回は進捗あり（中間値を含む共通bit上界）。RatioCostにLCM≤B²、除算/約分の積≤B²、共通分母の拡大項≤B³、加減の正規化前分子≤2B³を追加。Int.natAbs_ediv_le_natAbsを使うため、数学的な商の符号に依存せず成立する。2*(2^bits)^3=2^(3*bits+1)、(2^bits)^2≤2^(3*bits+1)も証明（RatioCost計9定理）。shared leaf build1.5秒成功。
- これにより、Euclid生成モデルの加減・除算の仕事量を元入力のbit上界だけへ換算。加減≤16*(bits+1)、除算≤23*(bits+1)。構築≤7*(bits+1)、単項負号≤8*(bits+1)、比較≤6*(bits+1)も追加。前回のnormalize/乗算の元入力上界と合わせ、数学Intモデルの主要演算はO(bits+1)を示した。while燃料/入力と途中値のC++範囲前提は残る（計算量関数に中間値の大きさは含めない）。wrapperは前回証明した追加1/2tickのrun対応で接続できる。
- fresh全API生成にhelper/stream/算術43定理を連結したLean検査成功。新しい数学補題を小さく分割して使い、上限の増加は行わない。今回C++/翻訳器の変更なし。inventory137とdiff --check成功。
- 未了: 追加領域オーダーと全型対応、最終仕様catalog/両kernel監査、全API公開切替・候補整理・全件gate、原本単位pushとCI20分測定。他の旧方式部品と取り下げ4部品も引き続き対象。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 Ratioの追加整数型の算術検査

- 前回は進捗あり（入力のみのbit上界）。全APIヘッダの差分driverが全stream具体化も要求していたため、明示的な呼出し選択 `Harness(..., calls={...})` を追加。未指定の既存動作は全件のまま。未知名/非公開staticの指定は拒否する。全クラスの翻訳は省略せず、driverが具体化する入口だけを選ぶ。
- `tests/test_ratio_integral_models.py` をsupport登録。signed char/char/short/int/long/long long/unsigned/unsigned long longの8型について、全12形の四則二項/左右scalar、複合代入の返値とreceiver更新、等値・比較をFraction期待値とnative ASan/UBSan/Leanで検査。正の小入力で全中間値を型範囲内に保ち、unsignedの折返し結果を数学的有理数の結果として扱わない。
- 選択検査の成功を型一般の証明や未対応stream契約の代用にしない。unsigned short/unsigned charは現翻訳器未対応、文字型とunsignedのstreamも別の契約が必要。公開Ratioは旧3フィールド、pushなし。領域評価/全型対応/最終監査/全API再公開/CI20分と他の旧方式・取り下げ部品の目標は継続。
- 検証結果: 追加整数型の2テスト56.916秒成功。既存の全stream入口を選択なしで使う汎用harness回帰1テスト29.770秒成功（short/int/long long）。py_compile/diff --checkとinventory137成功。今回数学モデル/証明ソースの変更はなく、全件gate/独立kernel監査は未実施。

### 2026-11-15 Ratioの全二項演算の値・入力bit上界

- 前回は進捗あり（8整数型の算術差分）。今回は既存のrun_of_triple/triple_of_runとwrapper run対応を使い、全12形（四則×Ratio同士/右scalar/左scalar）に、有理数値の一致・停止・元入力bit数による仕事量上界を同じ仕様へ接続。Euclid算術43→55定理。
- 上界は加減18*(bits+1)、乗算13*(bits+1)、除算25*(bits+1)で、複合代入の入力bit上界と追加1/2tickから導いた。scalarはRat.divInt a 1として埋め込み、左右の順序を保持。正しい有理数操作の非ゼロ分母/除数前提とwhile燃料の範囲を明示し、成功や費用を仮定にしていない。C++の入力/途中値が型範囲内という部品前提は引き続き必要。
- 検証: fresh Euclid全API生成にhelper4・stream2・算術55定理を連結したLean検査が14.234秒で成功。今回C++/翻訳器/ハーネス変更なし。inventory137、diff --check成功。
- 未了: 追加領域のモデル評価・型一般の対応、公開用モデル/証明/catalogの登録・両kernel監査、std版候補/一時helper整理と全API公開切替、全件gate、原本単位pushとCI20分測定。他の旧方式・取り下げ部品も目標のまま。公開Ratioは旧3フィールド、push未実施。

### 2026-11-15 ユークリッド法の論理データ領域

- 前回は進捗あり（全12形の値・入力bit上界）。現Mはwork counterだけで領域counterがないため、領域の成功を宣言せず、まず純粋モデルのpayloadを評価。`Proofs/Cpp/Lib/RatioSpace.lean`（8定理）を共有登録。Euclidのstep/stateAt、現在のa,bと一時剰余の3値frame、payloadBitsを定義した。履歴は保持しないモデルであり、Lean評価スタック/C++ヒープ/寿命監査ではない。
- 各入力≤2^bitsから、全反復でstateの両値も≤2^bitsを証明。任意kのframeは3payload、payloadBits≤3*(bits+1)。整数非負状態のemod更新とNat stepの一致、C++のtmodから同じstepへの一致も証明した。bitsは数値のlog2(value+1)合計で、0のpayloadは0bitとする。
- `ratio_euclid_contract.lean` に生成private numeric_gcd_nonnegativeそのものがbody反復と等しい定理（rfl）と、非零bodyのrun/純粋step/frame bit上界を接続する定理を追加（Euclid算術55→57定理）。sourceのstate遷移と無関係な定数だけをspaceと定義したものではない。
- 検証: shared module build成功（葉1.2秒）、fresh全API生成との57算術＋helper/stream契約Lean検査14.390秒成功、inventory137とdiff --check成功。今回C++/翻訳器の変更なし。
- 未了: このループpayloadに呼出し側の固定個数の値を合成するRatio全体の論理領域上界、全型対応、最終公開モデル/証明/catalogと両kernel監査、全API公開切替・全件gate・原本単位push・CI20分測定。他の旧方式/取り下げ部品の目標も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 呼出し側payloadの合成とLCM

- 前回は進捗あり（Euclidの3値frameと生成ループ対応）。RatioSpaceへpayloadBits_append/context_bits/with_contextを追加。任意の固定contextを保ったままEuclidを任意回反復しても、値の数はcontext.length+3、ビット量は(context.length+3)*(bits+1)以下になる。
- LCMの純粋モデルはEuclid中にa,bの2値を保持するcontext、最後の拡大段階に[a,b,gcd,a/gcd,a/gcd*b]の5値を保持するモデルとした。a>0かつ両入力≤2^bitsなら、両段階のpayload peak≤10*(bits+1)を証明。これは論理的な値の保持モデルで、C++ヒープやLean評価スタックを計測したものではない。共通RatioSpaceは8→14定理。
- fresh Euclid版で正のLCM入力について、numeric_lcmがa,bを保持してnumeric_gcd_nonnegativeを呼び、最後にa/g*bを返す計算形と一致することを証明。5値ループcontextの上界へ接続する証明も追加（算術57→59定理）。Ratio全クラスの領域完了とはしていない。
- shared module leaf build1.6秒成功。今回C++/翻訳器変更なし。未了: 上位Ratioの固定個数の値との合成・型一般対応・公開用証明/model/catalog登録と両kernel監査・候補整理/全API公開切替・全件gate・原本単位pushとCI20分。公開Ratioは旧3フィールド、pushなし。他の旧方式/取り下げ部品の目標も維持。
- 最終検証: fresh全API生成との算術59定理＋helper/stream契約検査成功。inventory137・diff --check成功。全件gate/独立kernel監査は未実施。

### 2026-11-15 正規化の符号付きpayload

- 前回は進捗あり（固定context合成/LCM）。RatioSpaceにsignedPayloadBits（各Intの符号1bit+natAbsのpayload）とsigned_context_bitsを追加。正規化の保持fields/符号付きGCD引数をnormalizeContext=[n,d,n,d]とし、GCD後は[n,d,g,n/g,d/g]、ゼロ分子では[0,1]を保持する純粋モデルとした。
- 入力natAbs≤2^bitsから、GCD中のcontext+3値frame≤11*(bits+1)、終了後≤10*(bits+1)、両段階のmax≤11*(bits+1)を証明。ゼロ・負数もspaceモデルで扱い、gcd/商の絶対値が元入力より増えないことを使う。RatioSpaceは14→18定理。C++実メモリ量/寿命を再導入したものではない。
- fresh Euclid版で非ゼロ分子のnormalizeの計算形（条件付き符号変更→numeric_gcd→両field除算）との一致を証明し、payload上界の定理も追加（Euclid契約59→61）。全クラスの呼出し/stream外部状態を含む領域完了とはしていない。
- 検証: shared module build1.7秒成功。fresh全API生成との61契約＋helper/stream検査14.004秒成功、inventory137・diff --check成功。今回C++/翻訳器変更なし。
- 未了: 上位四則/各wrapperの固定保持値との合成、型一般対応、公開モデル/証明/catalog登録と両kernel監査、候補整理/全API公開切替・全件gate、原本単位pushとCI20分測定。他の旧方式・取り下げ部品も目標のまま。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 四則とラッパーの論理領域

- 前回は進捗あり（符号付きnormalize payload）。`RatioArithmeticSpace.lean` を追加してProofs.lean/support登録。四則の全名前付き値を8値の固定contextとして同時に保持する保守的なenvelopeを定義し、LCM/GCD/normalizeの各callee frameのmaxを加えた。実際の寿命やC++ヒープを記号実行するモデルではない。
- RatioCostにgcd_sizeを追加（計10定理）。既存のB²/2B³上界から全保持値≤2^(3*bits+1)を示し、四則のpayload peak≤81*(bits+1)を証明。ラッパー側の元の4フィールドを合成する一般補題と加減/乗除wrapperの≤89*(bits+1)も証明。ArithmeticSpaceは8定理、leaf build1.7秒成功。
- fresh全APIで加減・乗除の計算形（LCMまたは2GCD→必要ならnormalize→返値/更新receiver）との一致をrflで証明し、各payload上界も接続。Euclid契約61→69定理。fresh検査14.144秒成功。ラッパーのsource run対応は既存12形の定理にあり、今回のwrapper領域は純粋モデルの保持値合成として証明した。
- docs/ratio.mdを履歴の追記形式から、現在の公開旧API/全API候補/前提/証明・検査範囲/残件の仕様へ整理。未完の型一般対応や最終監査を隠さず記載。
- 検証: 共通moduleビルド、fresh69契約＋helper/stream、inventory137、diff --check成功。今回C++/翻訳器の変更なし。未了: 全型と領域の全API対応、公開用model/proof/catalog・両kernel監査、候補整理/公開切替、全件gate、原本単位pushとCI20分。他の旧方式/取り下げ部品も目標のまま。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 全API Ratio候補の公理・両kernel監査

- 前回は進捗あり（四則/wrapperの論理領域）。今回 `tools/audit_ratio_candidate.py` を追加。公開中の非template cp.Ratioと衝突しないよう、全API候補を再生成し、helper4/stream2/算術69のソースを独立module `Proofs.RatioCandidateAudit` に合成する。共通Proofsソースは再帰的にscreenしてLakeでbuild、候補もscreenして再compileする。
- source/public catalogの全件gateの代わりではない開発用監査。既存InspectEnvironment/audit_dependencies/audit_axiom_definitions/audit_mathlib_coverage/leanchecker/lean4export/nanodaを再利用。入力header・証明・common module・policy・manifest/toolchainのSHA256を記録し、終了時に不変を確認する。Proofs namespaceのmodule探索にはscratchのCpp symlink viewを明示し、想定外のviewは拒否する。
- 実行結果: 公理依存/source監査5430宣言成功、`leanchecker --fresh Proofs.RatioCandidateAudit`成功、nanoda「Checked 5637 declarations with no errors」。environment上の候補430 theoremにはコンパイラ生成補助も含まれる（手書き契約数とは異なる）。project輸出照合900宣言で、全件監査と同じdirect-export probeによりstateAt/loopFuel/uniqueListの `_unsafe_rec` 3個は輸出器自身が扱わない補助宣言と確認し記録。他の輸出可能rootの欠落は拒否する。
- ローカル証跡: `.cache/wip/ratio_candidate_audit/result.json`（全入力hash・宣言名・export hash・省略された内部補助・独立kernel結果）、同directoryのenvironment/proofs.ndjson、`.cache/wip/ratio_restore/audit.log`。最終resultと現在の全入力hash一致を再確認、inventory137、py_compile/diff --check成功。
- 次: 型一般/領域の全API対応を仕上げ、公開用model/proof/catalogへ登録・候補整理/公開切替し、全件gateと最終spec監査/両kernelを実施。その後に原本単位pushとCI20分測定。今回の候補監査成功を全部品の再公開や公開catalog監査の成功とはしない。公開Ratioは旧3フィールド、pushなし。他の旧方式/取り下げ部品も目標のまま。

### 2026-11-15 符号なしGCD・正規化の型対応

- 前回は進捗あり（候補の両kernel監査）。`Proofs/Cpp/Lib/UnsignedMagnitude.lean` を共有登録。自然数への解釈・ゼロiff・剰余・fuel範囲・0未満でないことのインターフェースを定義し、UInt8/16/32/64の具体instanceを証明。さらにUnsignedDivisionで単位元と除算の自然数対応を同じ4幅で証明した。法則はclassの明示的な前提で、具体instanceに未証明公理は置いていない。
- `tests/lean/ratio_unsigned_contract.lean`（11定理）をfresh全API候補へ追加。generic lawful unsigned型のEuclid本体/符号wrapperの値と停止・gcdCost上界、4幅のGCD具体化、正規化の自然数pair結果、数学Intモデルとの一致、分母非零ならRat canonical fieldsとの一致、2引数構築、入力bit数による正規化の仕事量≤6*(bits+1)を証明した。正規化自身には余分な非overflow前提を置かず、除算/剰余が値を拡大しない性質で扱う。
- RatioMathへnormalize_nat_pairを追加（数学層35定理）し、NatのGCD/商を使う結果から既存Intの正規化モデルへ接続。符号なし四則・比較・入出力全体の型対応完了とはしない。UInt8/16のLean instance証明とC++のunsigned char/shortの直接binding対応は別であり、後者は未完了。
- `tests/test_ratio_integral_models.py` にunsigned32/64の最大値近傍8組ずつの正規化を追加。Fraction期待値とC++ ASan/UBSan/Leanの一致。既存8型の算術を含む全3テスト65.317秒成功。helperを共通化し、既存ケースの期待値や選択範囲は維持した。
- 候補監査toolは新module/契約のscreen・build・入力hash・輸出へ拡張。最終監査結果: 公理依存5685宣言成功、leanchecker --fresh成功、nanoda「Checked 5888 declarations with no errors」。候補481 theoremには生成補助を含む。既存と同じ3内部補助のdirect-export probe確認以外の省略なし。result.jsonと現在の全入力hash一致を再確認した。inventory137、py_compile/diff --check成功。
- 次はLCMと四則の型対応（乗算/減算の範囲・小幅整数の昇格の扱いを含む）、領域の全API対応、公開用model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査。その後に原本単位pushとCI20分測定。他の旧方式/取り下げ部品の目標も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なしLCMと乗算の表現範囲

- 前回は進捗あり（unsigned GCD/normalize/構築）。UnsignedMagnitudeへUnsignedProductを追加。capacity・各値の範囲・積がcapacity未満なら自然数の積に一致する法則を定義し、UInt8/16/32/64の具体instanceをUInt.toNat_mulとmod_eq_of_ltから証明した。未証明公理や無条件の積の非overflow仮定は置かない。
- RatioMathへlcm_nat_formulaを追加（数学層36定理）。`ratio_unsigned_lcm` はNat.lcm(mag a,mag b)<capacityという標準LCMと同じ表現可能性の前提から、生成helperが正しい自然数LCMを返して停止し、仕事量≤t+3+gcdCostを証明する。ゼロ分岐は別扱いし、非零では既存generic Euclidのrun結果を合成している。
- unsigned契約は11→18定理。LCMの入力bit数上界≤5*(bits+1)、Int.lcmとの一致、4幅の具体化を追加。四則全体や小幅unsignedの直接C++bindingへの対応完了とはしていない。
- `test_unsigned_lcm_boundary_arithmetic` を追加。unsigned32/64それぞれ3組で、分母の積はoverflowするがLCMと結果分子は表現可能な加算を公開APIから検査。Fraction期待値、C++ ASan/UBSan、Leanが一致（新規target test1件12.600秒成功）。既存ケースの本体/範囲は変更していない。今回C++ header/翻訳器の変更なし。
- 候補監査の最終結果: source/公理依存5733宣言、leanchecker --fresh成功、nanoda「Checked 5936 declarations with no errors」。候補491 theoremは生成補助を含む。既存3内部補助の直接輸出probe以外に省略なし。result.jsonと現在の全入力hash一致を再確認。inventory137、py_compile/diff --check成功。
- 次は四則の型対応（加減の範囲・整数昇格を含む）、領域の全API接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査。その後に原本単位pushとCI20分測定。他の旧方式/取り下げ部品の目標も維持。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なし乗算の状態・値の対応

- 前回は進捗あり（unsigned LCM）。ratio_unsigned_contractへgeneric unsigned乗算の2定理を追加（18→20）。交差約分後の分子・分母の積がcapacity未満という条件から、生成mul_assignの返値/更新receiver一致、両フィールドの自然数式、停止、仕事量≤t+7+gcdCost(n,e)+gcdCost(m,d)を示す。新しい費用仮定は置かず、2回の既存GCDのrunを合成した。
- RatioMathへmul_nat_pairを追加（数学層37定理）し、非ゼロ分母の条件の下でunsigned結果をIntの純粋乗算モデル、有理数の積へ接続した。積が表現範囲に収まらない場合の数学的な積の正しさは主張せず、別の入力へ結果をすり替えていない。Cpp本文/翻訳器は今回変更なし。
- test_unsigned_cross_cancel_boundary追加。unsigned32/64の各4組で、約分前の積はoverflowするが約分後は収まる分数を公開乗算APIで検査。Fraction、C++ ASan/UBSan、Leanが一致（新規target1テスト12.331秒成功）。既存ケースの内容は維持した。
- 最終候補監査: source/公理依存5746宣言、leanchecker --fresh成功、nanoda「Checked 5949 declarations with no errors」。候補496 theoremには生成補助を含む。既存3内部補助のdirect-export probe以外に省略なし。result.jsonと現在の全入力hash一致を再確認。inventory137、py_compile/diff --check成功。
- 未了: 加減・除算・比較などの型対応（小幅整数の昇格を含む）、全APIの領域/型接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分。他の旧方式/取り下げ部品も目標のまま。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なし除算の型対応

- 前回は進捗あり（unsigned乗算）。ratio_unsigned_contractへ除算の2定理を追加（20→22）。除数の分子非零と交差約分後の分子/分母の積がcapacity未満という条件から、2GCD→一時値計算→normalizeをrunとして合成。返値と更新receiverが一致し、フィールドが既存Intの純粋divモデルと一致すること、停止とt+11+3個のgcdCost上界を証明した。新しいコスト仮定はない。
- RatioMathへdiv_nat_pairを追加（数学層38定理）。有効な分母と非零除数では、結果の有理数値が商に一致することも接続した。rawデータのLeanモデル仕様と、C++/有理数操作の有効入力の前提は区別する。Cpp本文/翻訳器は今回変更なし。
- test_unsigned_division_cross_cancel_and_alias追加。unsigned32/64の各4組で約分前の積が大きい除算を検査し、自己参照の複合除算でも返値・receiverの双方が1になることを確認。Fraction/C++ ASan/UBSan/Leanが一致（新規target1テスト13.020秒成功）。既存ケースの内容は維持。
- 最終候補監査: source/公理依存5752宣言、leanchecker --fresh成功、nanoda「Checked 5955 declarations with no errors」。候補500 theoremは生成補助込み。既存3内部補助のdirect-export probe以外の省略なし。result.jsonと現在の全入力hash一致を再確認。inventory137、py_compile/diff --check成功。
- 次は加減・比較などの型対応（小幅整数の昇格を含む）、全APIの型/領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定。他の旧方式/取り下げ部品の目標も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なし加減算の型対応

- UnsignedMagnitudeへUnsignedAddSubを追加。加算の和がcapacity未満、減算の右辺が左辺以下という条件で自然数演算と一致する法則をUInt8/16/32/64に対して証明した。具体型のcapacityはrewrite前に指数まで明示し、定義展開への依存を避けた。
- RatioMathへadd_nat_pair/sub_nat_pairを追加（数学層40定理）。unsigned契約は22→26定理。LCM・スケール後の積・加算結果の表現可能性、減算の非underflowを前提に、生成add_assign/sub_assignの返値と更新receiver、Intモデルのフィールド、有理数値、停止、仕事量≤t+8+gcdCost(d,e)+gcdCost(z,l)を証明した。既存LCM/normalizeのrunを合成し、新しいコスト仮定は追加していない。
- fresh候補proofテスト1件14.336秒成功。test_unsigned_add_subtract_boundariesを追加し、unsigned32/64の各6組（最大値ちょうどの和、ゼロになる差、大きな共通分母）と自己参照の複合減算について、Fraction/C++ ASan/UBSan/Leanで返値・receiverを検査。新規target1件13.273秒成功。Cpp本文/翻訳器の変更は今回なし。
- 最終候補監査: source/公理依存5825宣言、leanchecker --fresh成功、nanoda「Checked 6028 declarations with no errors」。候補510 theoremは生成補助込み。既存3内部補助のdirect-export probe以外に省略なし。result.jsonと現在の全入力hash一致を再確認。ログは.cache/wip/ratio_restore/unsigned_add_sub_audit.log。inventory137、py_compile/diff --check成功。
- 比較などの型対応、小幅整数の昇格、全APIの型/領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定が残る。他の旧方式/取り下げ部品の移行も継続対象。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なし比較の型対応

- 前回は進捗あり（符号なし加減算と独立監査）。UnsignedOrderで型のLTとmagnitude上の自然数LTの一致を述べ、UInt8/16/32/64の具体instanceを証明した。RatioMathへcompare_nat_ltを追加（数学層41定理）。
- unsigned契約26→29定理。分母のGCDで除した後の2積がcapacity未満なら、生成op_cmpのOrderingが自然数の比較に一致する。非ゼロ分母ではRat値の順序に一致し、停止・仕事量≤t+4+gcdCost(d,e)、入力分母≤2^bitsなら≤t+6*(bits+1)を証明した。
- test_unsigned_comparison_after_denominator_cancellationを追加。unsigned32/64の各5組で、GCDによる分母約分前だけ積が大きくなる比較、大小の両方向、同値、ゼロ、自己比較をFraction/C++ ASan/UBSan/Leanで検査。target1件13.564秒成功。fresh候補proofテスト1件15.148秒成功（bit上界追加前）。その後のbit上界を含む候補全体は監査ツールでfreshコンパイル成功。Cpp本文/翻訳器の変更は今回なし。
- 最終候補監査: source/公理依存5853宣言、候補517 theorem（生成補助込み）、leanchecker --fresh成功、nanoda「Checked 6056 declarations with no errors」。既存3内部補助のdirect-export probe以外に省略なし。result.jsonの全入力hashを現在のファイルと照合済み。ログは.cache/wip/ratio_restore/unsigned_compare_audit.log。inventory137、py_compile、git diff --checkも成功。
- 小幅整数の昇格、単項/増減や入出力を含む全APIの型/領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定が残る。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 前置・後置増減の値の対応

- 前回は進捗あり（符号なし比較と独立監査）。符号なし契約に増減の値の補題2本と前置/後置のsource仕様4本を追加（29→35定理）。和がcapacity未満、差が非負、分母非零という前提から有理数値が±1変化し、前置は新値、後置は旧値を返す。更新receiverも同時に示し、仕事量は前置t+1・後置t+2と厳密に一致する。
- Int契約にも前置/後置の値と更新状態を扱う4仕様を追加（69→73定理）。新しい算術仮定は置かず、既存のgeneric source runとRatioMathの増減値の定理を合成した。C++本文・翻訳器・共通数値法則は今回は変更なし。
- fresh候補proofテスト1件14.603秒成功。test_integral_prefix_postfix_boundariesを追加。8整数型で最大値付近・分数・ゼロになる差、さらに符号付き型では負数・ゼロからの減算を前置/後置の両方で検査。返値と更新receiverをそれぞれFraction/C++ ASan/UBSan/Leanで照合し、target1件45.630秒成功。charの負数は処理系の符号に依存するためケースに含めない。
- 最終候補監査: source/公理依存5865宣言、候補529 theorem（生成補助込み）、leanchecker --fresh成功、nanoda「Checked 6068 declarations with no errors」。既存3内部補助のdirect-export probe以外に省略なし。result.jsonの全入力hashを現在のファイルと照合済み。ログは.cache/wip/ratio_restore/increment_decrement_audit.log。inventory137、py_compile、git diff --checkも成功。
- 小幅整数の昇格、単項演算/入出力など残るAPIの型対応、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定が残る。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 単項演算とスカラー操作の論理領域

- 前回は進捗あり（増減の値と独立監査）。RatioArithmeticSpaceに7定理を追加（8→15）。コピー・等値の整数payload≤8*(bits+1)、前置/後置の保守的なsnapshot込み≤24*(bits+1)、構築と単項負号≤19*(bits+1)、比較≤39*(bits+1)を証明した。比較はoriginal4フィールド・GCD wrapperの2引数・GCD結果・2積をcontextに含め、反復の3payloadを加算する。実行履歴/heap/lifetimeの証明ではない。
- Int契約73→83定理。単項正号の値・正規化を経由する単項負号の有理数値と入力bit仕事量を接続。比較と単項負号のsource式、およびコピー/等値/増減/構築/負号/比較の領域モデルの仕様を追加。領域上界はInt層で、unsignedなど各具体型への全接続が済んだとはしない。
- unsigned契約35→41定理。単項正号の値と1tick、数学的負号が表現可能なゼロの正規形0/1と3tick、4幅の具体zero-negation仕様を追加。一般のNeg Tのゼロ法則を無条件に仮定せず、4幅ではUIntの具体定理から導いた。
- test_integral_unary_boundaries追加。8整数型の単項正号と、符号付き5型/符号なしゼロの負号で、Fraction期待値・C++ ASan/UBSan・Leanの値およびreceiver不変を照合（target1件43.290秒成功）。charの非零負号は処理系の符号に依存するため含めない。fresh proof target1件13.888秒成功後、構築/等値の領域2仕様を追加し、監査ツールで全候補fresh compile成功。C++本文・翻訳器は今回変更なし。
- 最終候補監査: source/公理依存5948宣言、候補545 theorem（生成補助込み）、leanchecker --fresh成功、nanoda「Checked 6153 declarations with no errors」。既存3内部補助のdirect-export probe以外に省略なし。result.jsonの全入力hashを現在のファイルと照合済み。ログは.cache/wip/ratio_restore/unary_scalar_space_audit.log。inventory137、py_compile、git diff --checkも成功。
- 残件は小幅整数の昇格・文字/符号なしstream等の具体型対応、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 入出力の状態・仕事量・論理領域の合成

- 前回は進捗あり（単項演算/スカラー領域と独立監査）。stream契約2→10定理。抽出2read、整数形出力1write、分数形出力3writeの正常終了run式を証明し、それぞれの結果・最終stream状態・返すstreamの一致を示した。抽出は原本どおり生のn,dで、normalizeを追加しない。
- 各stream操作のrun/仕事量の契約を仮定して、Ratio側の1tickと呼出し先の仕事量の合計を上界にするHoare仕様を3本追加。入出力の定数時間やstream内部の無条件正常終了は仮定していない。EOF/failbitの処理はread/writeの契約へ保持する。
- Int層の固定保持値とstream操作ピークの最大を合成する領域2仕様も追加。≤8*(bits+1)+maxCalleePeakで、stream内部bufferの領域はcallee側の契約に含める。文字型/unsignedの具体stream解釈、全型の領域接続完了とはしない。
- test_ratio_stream_model.pyの7テスト全件44.582秒成功。既存の単独include/default、別headerのoperator共存、異なる具象型の拒否、3型のstream差分、EOF/fail/非正規化ケースを維持。新仕様で領域共通補題を使うためfresh proofのimportにRatioArithmeticSpaceを追加。C++本文/翻訳器の変更なし。fresh Euclid proof targetも仕事量仕様まで成功し、領域2仕様はstd候補の全件テストでcompileを確認した。
- 最終候補監査: source/公理依存5960宣言、候補556 theorem（生成補助込み）、leanchecker --fresh成功、nanoda「Checked 6165 declarations with no errors」。既存3内部補助のdirect-export probe以外に省略なし。result.jsonの全入力hashを現在のファイルと照合済み。ログは.cache/wip/ratio_restore/stream_work_audit.log。inventory137、py_compile、git diff --checkも成功。
- 残件は小幅整数の昇格・文字/符号なしstream等の具体型対応、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 符号なし数値streamの具体差分モデル

- 前回は進捗あり（入出力の一般的な状態・仕事量・領域仕様と独立監査）。diff_harnessの既定10進streamへUInt32/UInt64のread/writeを追加。符号なしでは絶対値≤型の最大値の負数を幅付きに変換し、絶対値が超えると最大値とfailbitにする。先行fail/EOFで旧値を保持し、出力は符号なし10進表現を用いる。ローカルlibstdc++の_M_extract_intと、実際のC++呼出しで動作を確認した。
- signed16/32/64の既存実現を専用template文字列に分け、共通のtoken/stream型部分を共有した。幅とsignednessで具象モデルを選び、異なる幅/符号の混在や文字型を拒否する。型の制約をC++ヘッダへ追加したのではなく、未対応の差分driverが誤った契約で動くことを防ぐ検査である。算術のみのcalls選択も維持した。
- test_unsigned_numeric_stream_boundaries追加。Euclid候補のunsigned32/64各15ケースで、最大値前後、負の最大値前後、-1、分母側overflow、EOF/fail保持、非正規化2/4とcanonical1/2のfield不等/比較等をASan/UBSan C++・Lean・独立の期待値と照合。target1件13.343秒成功。その後Boolのoverflow判定を明示し、既存7+新規2=9テストを全件59.386秒で成功確認。mixed model拒否の新規テストも含む。inventory137、py_compile、git diff --check成功。
- C++本文・翻訳器・Lean証明は今回は変更なし。前回の候補監査（leanchecker --fresh、nanoda6165宣言）の入力hashが現在も一致することを確認済み。具体streamの実現は差分テストの対象であり、標準I/O実装の形式証明や全書式のparser検証とは扱わない。
- 残件は文字型stream・小幅整数の昇格などの具体型対応、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 char/signed char streamの具体差分モデル

- 前回は進捗あり（符号なし数値stream）。diff_harnessへ文字用read/writeを追加し、char/signed charをIntの数値I/Oへ置換せず文字モデルへ具体化した。既存プロトコルのcanonical token表記を空白で結んだASCII列を用い、空白を飛ばして1文字を抽出する。文字xは数値modelでは不正tokenだが文字modelでは通常の文字になる。
- 文字読取り成功直後に末尾でもEOFを立てず、次の抽出で空列を検出したときEOF/failを立てる。先行fail/EOFでは旧field値を保持。挿入は下位8bitのbyteであり、整数の10進表記ではない。文字/数値は同じInt carrierでもstream契約が異なるため、driverでモデル種別を保持して混在を拒否する。
- test_character_stream_extraction_and_insertion追加。2型×12入力ケースで2tokenの2/4と1tokenの24、末尾/余剰文字、-1の2文字抽出、x、空入力、EOF・fail、raw50/52とcanonical25/26の比較を、独立期待値/ASan/UBSan C++/Leanで照合。出力のみのNUL・1・47・127、signed charの-1→255も検査。target1件13.699秒成功。全streamテスト10件76.795秒成功。bool/128bit等の未対応numeric拒否と、charを含む混在拒否も維持した。
- C++本文・翻訳器・Lean証明は今回変更なし。既存の候補監査（leanchecker --fresh、nanoda6165宣言）の入力hashが現在も一致することを確認済み。inventory137、py_compile、git diff --check成功。今回の文字入力はASCIIプロトコルに限り、128以上の入力byteをsigned/unsignedへ解釈する全parserの証明とはしない。
- 残件は小幅整数の昇格・unsigned char/short等の具体型対応、文字入力の全バイト等、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査、原本単位pushとCI20分測定。他の旧方式/取り下げ部品の移行も継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 文字streamのraw byte入力と符号の検査

- 前回は進捗あり（ASCIIのchar/signed char stream）。文字用driverに `bytes <count> <0..255>...` を追加。numeric driverでは有効化せず、C++/Leanの両側でbyteの範囲とcanonical表記を検査する。C++側は8bit byteと対象文字型がsignedであることをstatic_assertし、対応しない処理系で誤った契約を黙って使わない。公開C++ヘッダのAPIにこの制約を追加したものではない。
- 文字readの空白処理をCロケールの6種類（9/10/11/12/13/32）に拡張し、128以上の入力byteを負のInt値へ解釈する。EOF/failの扱いとbyte出力を保持する。
- test_character_stream_all_input_bytes追加。2型で全256byteを先頭に置くケースと、空入力・空白のみ・NUL・負の分母・末尾/残余文字の8ケースを期待値/C++ ASan/UBSan/Leanで比較。単独target1件14.030秒成功。canonical byteのC++側検査を揃えた後、全stream11テスト93.422秒成功。
- その後、byteの再出力だけでは符号誤りが観測できないため、最初の256ケースへゼロとの大小比較を追加。負値/ゼロ/正値のOrderingをC++/Leanと期待値で検証し、target1件13.913秒成功。この追加後の全件再実行は行わず、変更対象の新規targetを検証した。
- 入力/途中値の型範囲という部品の前提を維持し、絶対値は実装で計算する場合に含めるとdocs/ratio.mdを明確化。streamから得た-128に対して、分子の絶対値を使わない比較まで不必要に除外しない。これは原本C++の不具合修正ではないのでfixes.mdには追記しない。
- C++本文・翻訳器・Lean証明は今回変更なし。既存の候補監査（leanchecker --fresh、nanoda6165宣言）の全入力hashが現在も一致することを確認済み。inventory137、py_compile、git diff --check成功。全256byteを試す有限テストで、全byte列・全書式/ロケールのparserを証明したとはしない。標準操作の一般契約は既存のStreamRead/Writeで引き続きパラメータ化している。
- 次は小幅整数の昇格・unsigned char/shortのbindingを優先し、全APIの領域接続、公開model/proof/catalog登録・候補整理/公開切替・全件gate・最終公開監査へ進む。全書式/ロケールの具体parser実装自体を再公開の追加要件にしない。原本単位pushとCI20分測定、他の旧方式/取り下げ部品の移行も未了。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 小幅unsignedテンプレートbindingと整数昇格

- 前回は進捗あり（全byte入力と符号検査）。diff_harnessへunsigned char/unsigned short（unsigned short int含む）のtemplate instance bindingを追加。Cpp演算のintへの昇格を保存するためIntを用い、演算子ごとのUInt8/16折返しにはしない。入力と格納値を含む途中値の型範囲という既存の非折返し部品の前提を維持する。
- 宣言/キャストの一般翻訳は拡張していない。instance_typeは差分driverのtemplate置換だけに使い、lean_translate.parse_typeの具体unsigned char/short拒否は維持する。直接書かれた小幅unsignedの戻り値/引数などを誤ったキャスト意味論で受理しない拒否テストも追加した。
- test_narrow_unsigned_template_promotionsで2型の12二項/スカラーAPI・複合代入・Eq/比較をFraction/C++ ASan/UBSan/Leanと照合。さらに128/1と1/2（16bitでは32768/1と1/2）を比較し、途中のintの積256/65536をTへ折り返す誤りならOrderingが逆転するケースを検査。2つの新targetテスト13.737秒成功。
- unsigned charはInt carrierの文字read/write、unsigned shortはInt carrierの16bit符号なし数値read/writeへ具体化。符号付き/符号なしの文字を混在させず、C++static_assertでsignednessを照合する。unsigned shortはローカルnum_getが直接unsigned shortを抽出することも確認した。negative tokenの幅変換/overflow、全256byte入力、符号を見る比較、ASCIIとbyte出力の既存テストへ2型を追加。stream全11テスト108.809秒成功。
- 公開C++/候補C++・翻訳器・Lean証明は今回は変更なし。既存候補監査（leanchecker --fresh、nanoda6165宣言）の全入力hash一致を確認済み。inventory137、py_compile、git diff --check成功。候補全体の両kernel成功と、具体bindingの差分成功を区別して記録する。
- 次はRatioの公開用model/proof/catalog整理・登録に必要な全APIの領域/型の接続と残件を照合し、候補整理/公開切替・全件gate・最終公開監査へ進む。具体unsigned char/short宣言・キャストの一般翻訳は未対応だが、Tを使う今回の候補に現れない構文までRatio再公開の追加要件にしない。全137原本の目標、原本単位pushとCI20分測定は継続。公開Ratioは旧3フィールド、pushなし。

### 2026-11-15 Ratioの公開側へ全APIを統合

- 前回は進捗あり（小幅unsigned binding）。library/number/ratio.hppをEuclid候補と同じ原本全APIのRatio<T>へ置換。1クラス・既定型・全構築/演算/比較/入出力を維持し、旧固定型3フィールドAPIを撤去した。metadataをC++20/ClassTemplateDecl:Ratio/新hashへ更新。公開作業ツリーの変更であり、push/release更新はまだ行っていない。
- 公開Gen/Ratio.leanをC++から再生成し、4つのfresh契約（numeric/stream/Euclid/unsigned）をnamespace Proofs.Cpp.RatioでProofs/Cpp/Ratio.leanへ統合。既存共通RatioMath/Cost/Space/ArithmeticSpace/UnsignedMagnitudeをimportする。公開proof module単体build成功、全体Lake1553 jobs成功。移行用の候補/証明断片はまだ重複しており、整理が残る。
- tests/ratio.cppは10整数型で全12二項/スカラー形・複合代入・前後置増減・単項・比較/Eq・自己除算・返す参照の同一性・非正規化streamを検査する形へ更新。期待の有理数表記は独立のstd::gcd正規化で作る。tests/diff/ratio.pyも全API共通の非overflowケースへ変更し、metadataに10整数型を登録（longも含む）。
- check_public --mode cpp --component ratio成功（native sanitizer/template-first include）、bridgeも10型で成功（66.974秒）。公開モジュール/metadata/生成caseでの結果で、候補だけの検査ではない。inventory137とdiff --check成功。
- regenerate_statements.py成功。roots3824→4579、定義閉包7000→7998、削除175、既存の同名宣言の変更なし。追加rootはRatio540・既に作業ツリーで移行済みのTreeFullDp283・Gen16・rangeDown1・TreeDpAlg.CM1、旧RatioCall/TreeFullDpCallのroot86件を置換した。カタログは今回より前の未反映TreeFullDp移行も現在のregistryに従って取り込む。無関係な証明の弱化を--accept-changedで受け入れたものではない。
- 公開側の全体最終監査は初回にprime付きroot名を拒否して停止し、監査側を修正して再実行した。再実行は両kernelまで成功（後掲）。候補側6165宣言の証跡とは別の公開全体の結果である。
- 残件: 公開全体監査結果の確認、候補/証明断片の整理と必要な全API領域/型の再点検、全件gate、原本単位pushとそのCI20分測定。他の137原本の移行目標は維持。公開側headerは旧3フィールドではなく原本API復元版になった。次セッションで旧状態と取り違えない。

### 2026-11-15 公開全体監査で見つかったprime付きroot拒否を修正

- 公開全体監査の初回は、source/公理/固定仕様の照合を通過後、既存TreeFullDpの5補題（kid_facts', range'_filter_gt/lt, V_dp', i3_vc'）の名前をASCII root規則が拒否して終了した。証明や仕様を変えていない。実際に失敗した監査ログは.cache/wip/ratio_restore/public_full_audit.log。
- check_proof_security.pyにproject_export_namesを追加してprimeを許容。subprocessのargvをlean4exportのname-literal parserへ渡す経路で、shellへの文字列展開は行わない。不正な空白/区切りを含む公開名の拒否、全safe rootの輸出coverage、exporter自身が省く内部補助のdirect probeは維持。候補監査ツールも同じ選択関数を利用する。
- test_proof_security.pyでprime付き定義/定理をcompileし、lean4export後の宣言集合に両方残るintegration testと、不正名拒否を追加。security全21テスト19.598秒成功。公開支援全27テスト3.514秒成功。レッスンにも追記した。
- 修正後の全公開auditは正常終了（.cache/wip/ratio_restore/public_full_audit_prime.log、session90288は終了済み）。公理/固定仕様/定義閉包46245宣言の照合、110変更moduleを含むProofs prefixのkernel再生、7591 rootからの輸出coverage、nanoda「Checked 43915 declarations with no errors」が成功。190内部補助はexporter自身が省くことをdirect probeで確認した。public checks passed for 56 component(s): audit。
- 全56部品のcppモード成功（現在の入力fingerprintに対応するcacheを含む）。全56部品のbridgeモードも成功（.cache/wip/ratio_restore/public_all_cpp.log、public_all_bridge.log）。これを全件gate成功や冷えたCI20分の実測とはしない。
- 未整理の旧Ratio検証はProofs/RatioCall.lean（445行）とProofs/Generated/Ratio.lean（11行）。参照はProofs.lean、support.tomlと旧RatioCall自身だけで、公開registry/canonical specのrootからは外れた。生きている監査の入力を変更しないため、完了後にこれらの旧登録/importとファイルを整理する。候補/証明断片の重複整理、全API型/領域の点検、全件gate、原本単位push・CI20分も未了。

### 2026-11-15 公開全体監査の成功と次の作業

- 全56公開部品のcpp・bridge・auditの各モードが現在のtreeで成功。公開支援27件とsecurity21件も成功。全件gate（全supportチェックを含むall/tests）やCI push後20分を達成したとはしない。
- 環境情報・正確なphase timing・入力hashはgitignore対象benchmarks/local/ratio_republication_20261115/audit.jsonに保存した。依存/プロジェクトcacheがあるローカル監査であり、冷えたCIやpushからの計測ではない。測定値をtracked資料へ転載しない。
- 次は旧RatioCall/Generated.Ratioの登録・import・ファイル削除、移行用候補/証明断片の重複整理を行う。必要なsource/frontend検査は保持し、wide boundary等のCppテストが公開headerを検査するように整理する。整理後は入力が変わるため全体監査を再確認する。
- 監査phaseから、宣言を持たないaggregate Proofs moduleのimport変更だけでProofs prefix全体を再生している可能性が分かった。CI20分へ向けた候補として、実際の所有宣言と読み込まれたmoduleを確認して安全にtargetを減らせるか調べる。検査済みcacheの範囲や独立kernel全coverageを弱めて省略しない。
- Ratioの原本APIは公開側treeで復元済みだが、原本単位push・release更新は未実施。他の未移行/取り下げ部品と137原本の目標を維持し、未了のgoalをcompleteにしない。

### 2026-11-15 Ratio旧検証の削除と正本への集約

- 前回は進捗あり（公開全56部品cpp/bridge/audit）。Proofs/RatioCall.lean、Proofs/Generated/Ratio.lean、対応するProofs.lean importとsupport登録を削除。依存検索で他の参照がないことを確認し、inventory137も成功。旧方式専用のRatio証明456行を残さない。
- experiments/verification/number/ratio_euclid.hppを削除し、integral/stream/Euclid検査はlibrary/number/ratio.hppを直接参照。std関数版とfree helperはfrontend比較用fixtureとしてtests/fixtures/ratio_reference.hpp、ratio_numeric.hppへ移動した。元のAPI/本体差分を検査するテストは維持。
- 公開証明の重複だったtests/lean/ratio_euclid_contract.leanとratio_unsigned_contract.leanを削除。fresh検査はProofs/Cpp/Ratio.leanからmodel importだけを除いてfresh翻訳モデルと組み合わせる。numeric/stream/std arithmeticのfixture契約は、それぞれ別の標準関数/free helperモデルのfrontend検査に必要なので保持する。
- tools/audit_ratio_candidate.pyはtools/audit_ratio.pyへ改称し、公開header/model/metadataと公開対応証明を入力にする。modelのfresh一致、共通source監査、両kernel、入力hash照合を実行。新scopeの結果は.cache/wip/ratio_audit/result.json、nanoda6165宣言成功。過去のcandidate証跡は.cacheに保持して混同しない。
- 公開sourceを直接用いるEuclid5テスト、numeric fixture2テスト、integral12テスト、stream11テストが全件成功。Source/frontend/parserで対応を広げたのではなく、検査対象と正本を統一した。従来の境界値・Fraction期待値・全byte・aliasの検査を削っていない。

### 2026-11-15 空の集約moduleの再生と全体監査

- check_proof_security.pyにreplay_required_modulesを追加。screened buildのListModulesに存在し、InspectEnvironmentで所有宣言がないmoduleだけ、変更後のカーネル再生prefixから外す。未観測moduleや所有宣言のあるmoduleは維持。Mathlib基準変更時の--fresh全再生、固定仕様/公理照合、全safe rootの輸出coverage、nanoda全再検証は変えない。
- 実際に空のimport集約と子の定理moduleをcompileし、ListModules/InspectEnvironmentから子だけを再生対象と判定するintegration testを追加。未観測や宣言ありの場合のunit testも含め、security全23テスト成功。fixtureの実行cwdはscratchとし、既存Proofsパッケージの探索先にshadowされないようにした。
- 整理後の全56公開部品audit成功（.cache/wip/ratio_restore/public_cleanup_full_audit.log）。source/公理/固定仕様46180宣言、34225 project宣言を7588 rootsで輸出、exporter自身が省く190内部補助のdirect probe、nanoda43865宣言が成功。今回の変更は空のProofs集約だけだったため、既に検査済みでhashが同じ実宣言の再生は不要と判定した。
- 環境と正確なphase timingはgitignore対象benchmarks/local/ratio_republication_20261115/cleanup_audit.jsonに保存。warmなローカル結果であり、push後のCI20分の実測ではない。
- 全件gateを実行中: check_public.py --mode all --jobs4 --timeout-seconds7200、.cache/wip/ratio_restore/public_cleanup_full_gate.log、exec session39630。現在のsource/metadataを固定して共有検査も確認している。まだ全件gate成功とはしない。次セッションは同じhandleをpollし、観測が途切れただけで再起動しない。
- mainはorigin/mainより85 local commits進んだ既存状態で、今回の未commit変更が重なっている。pushは原本1ファイル単位、全件gateと差分確認後の手動承認が必要（docs/agent/git_workflow.md、.codex/rules/git-push.rules）。途中でまとめてpushせず、既存commit/ユーザー作業を尊重する。現時点でpush/commitは行っていない。
- Ratioの公開側復元は進んだが、全件gate、移植単位完了の型/領域/登録最終点検、push・release・CI20分確認と、他の未移行/取り下げ部品を含む137原本の目標は未完了。

### 2026-11-15 全件gateの継続確認と配布物/API点検

- exec session39630の全件gateは同じprocessで継続中。観測の途切れを理由に再起動していない。Ratio検査群、nested/template/frontend、旧frameworkの共有検査が順に通過し、これまで報告された失敗はない。未完了のためall gate成功とはしない。ログは.cache/wip/ratio_restore/public_cleanup_full_gate.log。
- 全56hppだけのarchiveをbenchmarks/local/ratio_republication_20261115/library-hpp.zipへ生成し、check_header_package.pyでarchive内容の一致と、そのheaderだけによるcompileが成功。gitignore対象であることを確認済み。外部releaseへは未反映。
- actual Translatorの公開call28項目を列挙し、登録diff generatorが28項目全てを呼ぶことと、検査済み環境のtheorem type_dependenciesに全項目が現れることを確認した。これは宣言coverageであって、単なる名前出現を仕様レビューや全型証明の代用にはしない。詳細はlocalのpublic_api_declarations.json/public_api_theorem_mentions.json。
- CI workflowは16 shard＋audit＋release構成。現行planと、nested_templates(10 methods)/ratio_integral(12)/ratio_stream(11)をmethod分割する案を、local current_shard_plan.txt/split_methods_proposal.jsonへ保存した。進行中gateを固定するためtracked CI設定には適用していない。local実測をCI実測のweightsへ混ぜない。新planの評価と、push後の実CI20分確認は引き続き必要。
- CI・git設定はread-onlyで確認。mainの既存85 local commitsをまとめて送ってよいとは判断していない。Ratio原本単位の完了点検、全件gate終了、差分・secret/配布物点検を先に済ませ、必要なpush承認は具体的な対象が揃った段階で行う。現時点でcommit/pushはしていない。

### 2026-11-15 全件gate成功とCIのメソッド分配

- 整理後の全件gateは正常終了した（.cache/wip/ratio_restore/public_cleanup_full_gate.log、session39630終了0）。全56登録部品と全共有検査が成功し、入力fingerprint一致の全体proof-security成功を含む。全137原本の移行完了やpush後CI20分の達成とは区別する。
- tools/ci_weights.jsonのsplit_methodsへnested_templates、ratio_integral_models、ratio_stream_modelを追加。既存のCI実測weightは変更せず、検査単位だけを細かくした。支援27テストとworkflow16分割の検査は成功。分割4ファイルの全73methodはunittest discoveryと計画が完全一致し、重複なし。計画は312tasks。ローカル計画の数値はbenchmarks/local/ratio_republication_20261115/split_shard_plan.txtにのみ保存。
- 分配変更後の全件gateを実行中: .cache/wip/ratio_restore/public_split_full_gate.log、exec session86152。対象source/登録/docsは固定中。次は同じhandleをpollする。完了前に成功と扱わない。
- docs/ratio.md、docs/experiments_status.mdには公開監査・整理・全件gateが未了という古い記述が残る。gate完了後、成功した検査と残る型/領域接続レビュー・原本単位push・CI計測を区別して更新する。pushなし。

### 2026-11-15 分配変更後の全件gate成功

- session86152は正常終了0。public_split_full_gate.logの312task全件成功、現在の入力fingerprintでproof-security成功cacheを確認し、public checks passed for 56 component(s): all。未実行taskは残っていない。新しいsplit method33件は実行され、残りは必要に応じて既検証cacheを利用した。全件のfresh実行や冷えたCI20分とは主張しない。
- docs/ratio.mdとexperiments_status.mdの古い未完了記述を更新。公開model/proof/catalog・旧検証整理・全体監査・全件gateは完了、全APIの型/領域対応の最終点検と原本単位push/release・CI計測を残件として明示した。
- 本セッションではgitのcommit/pushは行っていない。mainの既存85 ahead commitsを無条件にpushしない。次はRatioのAPI/前提/論理payloadの対応を具体的に点検し、原本1ファイルの完了条件を満たしてからgit workflowに従う。全137原本の移行目標は継続中。

### 2026-11-15 Ratio全APIの対応点検と構築仕様の補完

- 前回は進捗あり（312検査成功とCI分配変更）。新方式では非折返し型の演算を、型範囲の前提のもと数学整数で扱う。具体C++整数型全てへの追加証明を完了条件として増やさず、元のtemplate/APIを保ってInt層と純粋領域モデルの対応を点検した。docs/ratio.mdへ公開28入口すべての実行/値/仕事量/論理payloadの証明対応表を追加。12二項形は既存のrun/value定理と共通wrapper envelope、streamは既存のrun/work/payloadと呼出し先契約へ接続する。
- 1引数構築についてratio_euclid_init_scalar_value_payloadを追加。生成init_Tの返却fields、Rat値=n、1 tickでの停止、入力とコピー保持値の8*(bits+1)上界を同時に示す。fuel前提は不要。既存のstaging/candidateというproof内の古いコメントも整理。公開proof buildとfresh単体compile成功。測定手順・条件・入力hashはignoredのbenchmarks/local/ratio_republication_20261115/scalar_certificate_build.jsonに保存した。
- カタログ再生成はroots4579→4580、closure7998→8000、削除0、changed existing=[]。既存命題の変更を一括受容していない。追加後の全件gateはexec session74906、.cache/wip/ratio_restore/public_scalar_full_gate.logで実行中。共有検査完了、Ratio moduleのleanchecker再生成功、nanoda全体検査待ち。次は同じhandleをpollする。
- 次の旧方式Groupをread-onlyで調査。原本の3クラスをそのままcpへ包んだprototypeは、依存式からの暗黙構築・既定の委譲構築・recordのbrace returnが現翻訳器の不足だった。公開/変換器を変えず、.cache/wip/group_restore/lean_translate.pyに試作した。元の3クラス全体を翻訳してLean compile成功、26呼出しのC++ ASan/UBSan/Lean/独立期待値が一致（cases.txt/result.txt/Driver.lean等）。これは公開移行完了ではない。prototypeのROOTはimport後にリポジトリrootへ明示設定する。
- Groupの公開移行で残る点: namespace qualified cp::opも現公開APIとして維持すること（同じsignatureのhidden friendとのmodel名区別が必要）、default Tを原本llと同型に保つこと、frontendの負例/副作用/構築順を検査すること、group旧Call/Generated専用の登録・テストを整理すること、純粋モデルで群・合成の法則/停止/時間・論理領域を示すこと。library3旧版の別APIは別の原本として未解決台帳から落とさない。gate実行中なのでtracked frontendやGroupには変更していない。
- 変更/未追跡52ファイルを秘密鍵・GitHub token・AWS access key・代入済みsecretのパターンで検査し検出0。完全な機密監査やstage済み差分レビューの代わりにはしない。git操作はread-only、commit/pushなし。既存85 ahead commitsの原本単位での公開整理は未了。

### 2026-11-15 Ratioの移植単位検証完了

- session74906は終了0。public_scalar_full_gate.logで全312検査成功、変更したRatio moduleのleanchecker再生成功、root coverage/probeを含むnanoda43867宣言成功、全56部品all gate成功を確認した。新しい構築定理も最終公開全体監査に含まれる。
- docs/ratio.mdの全28入口対応表で型/領域の最終点検を完了し、experiments_status.mdを「移植済（新方式、未push）」へ更新。現在の公開sourceで解消したRatioのAPI縮小は違反一覧から外した。残る具体型全てへの別証明や、実装に現れない小幅unsigned構文を新方式の追加完了条件にしない。
- fixes.mdのRatio2行が誤って付記後に置かれていたため、実際の修正表の末尾へ移動し、再発防止欄を現在の公開証明に更新した。新しい原本バグの追加記録ではない。
- Ratioの原本単位の移植・ローカル検証は完了。push/release更新・実CI20分は未完了。既存85 ahead commitsの公開順序を原本単位に保つ必要があり、一括pushしない。Groupはまだignored scratchの試作だけ。

### 2026-11-15 Ratioを保存しGroupの新方式移行へ着手

- Ratio移植はローカルcommit `0702be8301168d62808ef6bd483ddb872c15fbe9` に保存済み。51ファイル。commit直後はclean、mainはorigin/mainより86 aheadだった。全件gate・両kernelの最終成功は上記public_scalar_full_gate.log。pushはしていない。既存の大量の未push履歴を原本単位で公開する順序の整理は残る。
- Groupに必要なfrontendを実装: 依存式の型を求めてから一度だけ評価する暗黙1引数構築、constructorを実行するrecordのbrace返却、空の既定構築から同classの引数なしstatic factory結果への委譲コピー、同一署名のhidden friend/qualified template双方の別モデル名。委譲は原本の形式だけに限定し、非空body/引数付き構築/他factory/独自copy/dtor/継承/非scalarコピーは受理しない。既存50 lean_model全件の生成本文は完全一致。
- experiments/verification/algebraic_structure/group.hppを候補として追加。原本3クラスのT/default/全member/hidden friendを保持し、既存公開のqualified cp::opも維持。defaultのllは同じstd::int64_tへ修飾し、int/long longにだけ依存する旧frontend witness/明示具体化は候補には置かない。既存tests/group.cppを候補includeへ差し替えたnative ASan/UBSan suiteとdefault型のstatic_assert成功。公開libraryのGroupはまだ旧方式であり候補へ切り替えていない。
- GroupMath.lean（候補）で加法/乗法の結合律・単位元・逆元、アフィン合成/結合律/単位元/逆元を純粋値で証明。一般の逆元はAddGroup/DivisionRing/Field等の条件付きであり、整数を体としない。整数用affineIntInvをInt.tdivで別定義し、傾き±1について逆元の法則を示した。affineEnvelopeは9scalar cellsの保守的モデル。全APIの領域対応はまだ残る。
- GroupContracts.leanはfresh翻訳とGroupMathへ連結する開発fragment。原本20入口＋qualified op3入口の全23入口について返すfield・停止・定数tick（1/2/3）を証明。GroupMulは実際のconstructor assertの条件を持つ。さらにaffine_integer_inverseはDiv Int=Int.tdivを明示し、非単位元でもC++の切捨てfieldと2tickに一致する。23定理+整数用1定理で、公開登録や両kernel全体監査はまだしていない。
- 追加検査tests/test_lean_model_construction.pyは最新9テスト成功。全3クラスとhidden/qualified、異なるhidden/qualified本体、変換引数の1回評価とwork、brace返却がconstructorを実行すること、拒否例、fresh候補+純粋モデル+24対応定理を確認する。supportへ登録した。imported TestCase自体を再発見しないようfriend helperはmoduleとしてimportする。
- 新しく見つけた検査側の実不一致: generic T=IntのDiv/ModをLean標準で具体化していた。符号全組60呼出しで修正前のC++/Lean不一致を再現（template_division_before.log）。diff_harnessのInt carrierのcall-siteだけInt.tdiv/tmodへ明示bindingし、non-template Cpp.tdiv/tmodとUInt32/64を維持した。GroupAffine(2,3).inv()のb=-1も回帰に含む。元C++バグではなくfixes.mdには追加しない。数学Intで標準除算を使うRatio等は、正確な約数による除算という既存条件を維持する。
- binding修正後の検証: 全56部品bridge成功（public_bridge_after_binding.log、session79910終了0）、RatioIntegral12テスト成功（ratio_integral_after_binding.log、session18634終了0）、RatioStream11テスト成功（ratio_stream_after_binding.log、32798終了0）、friend8テスト成功（friend_after_binding.log、90234終了0）、construction最新9テスト成功（construction_tests.log、50636終了0）。public support27件、inventory137、workflow16、diff --checkも成功。binding/frontend変更後の全件all gate・最終監査はまだであり、Ratio commit時の全件成功と区別する。
- 次: Groupの全APIの論理領域・整数切捨て仕様と前提を完結し、候補の公開登録/metadata・diff generator・生成model・canonical proofへ統合する。旧GroupCall/Generated.Groupと専用登録/検査の依存を確認して整理し、catalog再生成・両kernel・全件gate・build増分を確認する。library3旧版の異なるpublic-field/Mapping APIの未解消台帳は維持する。frontend整備だけではpushしない。

### 2026-11-16 Groupを公開側へ切替・全件gate実行中

- 前回は進捗あり（Ratio保存とGroup候補）。HEADはec0b830、mainはorigin/mainより87 aheadのまま。今回の変更は未commit、pushなし。全137原本の目標と、原本単位push・CI20分の実測は継続する。
- library/algebraic_structure/group.hppを原本全3クラス＋既存qualified opの候補へ切替。元のT・全member・hidden friend・委譲/暗黙/brace構築・const参照applyを保持し、default llは同型std::int64_t、旧witness/明示具体化は不要になった。元のfield/signature/token bodyと3hidden friendが一致する機械比較も成功（original_api_review.json）。metadataはlean_model、CPP17、公開宣言6、diff10整数型。単体native ASan/UBSan/template先行includeと10型bridge成功。native default型static_assertも追加した。
- 正本はProofs/Cpp/Gen/Group.lean、Proofs/Cpp/Lib/GroupMath.lean、Proofs/Cpp/Group.lean。原本20＋qualified3の全23入口のfields/正常停止/1〜3tickと、整数用Int.tdivの追加対応、モデルの群の法則/アフィン合成/逆元/論理領域を公開rootへ接続。Frameは最大10scalar cells、factory+ctorの保守的な8を含め18以下。Tの内部表現・実heap/lifetimeは対象外。Field等の条件付き法則をFloatや整数全体へ無条件に適用しない。docs/group.mdを新方式へ改訂し、library3別APIの未解消差は維持。
- 旧GroupCall2522行とGenerated/Group66行を撤去。現在の他の公開部品からの依存17件と残すfrontend fixtureを調べ、必要な共通補題のみ533行のProofs/LegacyScalarCallCore.leanへ抽出した。互換namespace GroupCall/GroupCallIntは保つが、GroupInstanceやGroup専用プログラム/部品証明は含まない。MonoidCall等の4importを変更。全体Lake build成功。remaining5旧方式部品を移すまで共通基盤として保持する。
- library3回帰が旧GroupのNProgramと比較していた部分は、test-onlyのtests/lean/scalar_reference_programs.lean（14参照program）へ分離。original_record_applyは独立copy/zero参照、original_mixed_add_sumはMonoidCallCoreの一般ctor/e定理を直接用いる。Group専用kernel testは新Proofs.Cpp.Groupのconstructor/op/law/spaceへ、apply testは新生成モデルの任意入力・初期tickと等値入力/順序変更の観測へ移行。元CPPのconst参照/コピー検査はnativeに保持。experiments/verificationのGroup3候補重複は削除。
- カタログはroots4580→4389、closure8000→7855。初回はws2定義の変更を拒否した。旧/新envの全recordを比較し、型・本体・levels・dependencies・unsafeは完全一致で所有moduleだけGroupCall→LegacyScalarCallCoreと確認してから--accept-changedで更新した。他の既存命題/定義の変更なし。正確な2recordとreviewはcatalog_module_move_rows.json/catalog_module_move_review.json（.cache/wip/group_restore）。一時の巨大な全env診断dumpはレビュー後に削除した。
- 関連検査: construction9、scalar_delegation8（独立kernel含む）、新apply1、library3原本templates8が成功。nested_templates10は最初2件失敗（新generic e証明のunused simp s64警告、撤去した比較補題のexport root残り）。警告の原因と古いroot2件を直し、失敗した2methodの再実行は独立kernel3674/3874宣言を含め成功。他8methodは初回で成功。全件gateでは10methodすべて改めて確認中。検査を緩めたり上限を増やしていない。
- ビルド差分を1CPU/LEAN_NUM_THREADS=1で、前提oleanを既にbuildした条件下で測定。beforeはHEADの旧model/proof（import先だけ隔離modelへ変更）、afterは新Gen/Math/proof/共通coreの4target。全6compile成功、対象compiler作業量は減った。数値/CPU/方法/制約/原本hashはignoredのbenchmarks/local/group_migration_20261115/build_delta.jsonとmeasure_build.pyに保存。冷えた全ビルド・依存client再コンパイル・実CI20分の測定ではない。
- 現在の56hppだけのZIPとmanifestを同じignored benchmark directoryへ保存。check_header_package.pyでarchive内容一致と各header単体/全header同時のcompileが成功（package_check.log）。元137ソースのinventory/hash、workflow16、diff --checkも成功。
- 全件gateはexec session78479で継続中: .cache/wip/group_restore/public_full_gate.log、check_public.py --mode all --jobs4 --timeout-seconds7200。現在のsource/metadataを固定した。共有検査が順に成功し、ここまでfailureなし。まだ最終auditの成功とはしない。次はこの同じhandleをpollし、観測が途切れただけで再実行しない。終了後に失敗対応または両kernel/全件成功の確認、staged差分・機密点検とlocal保存を行う。
- 新方式は登録56中51。残る旧方式はmonoid/monoid_lazy/modint/dynamic_modint/rolling_hash。元137原本と取り下げ部品・API違反は全体目標に残る。次Monoidの隔離probeのみ.cache/wip/monoid_restoreへ保存した。実frontendはlocal using std::min/maxをまだ扱えず、そのusingだけin-memoryでskipしたprobeでは次にUnresolvedLookupExpr（依存型のconstexpr/numeric_limits関連）が不足と分かった。tracked Monoid/frontendはgate中に変更していない。元のfloating infinity/lowest分岐や汎用Tを削って移行しない。

- 同じsession78479の直近観測では313件中291件成功、残るgeneric family共有検査を実行中。failureなし。最終proof-securityは未完了。sourceは固定し続け、handoffのみ追記した。変更/未追跡ソースの秘密鍵・GitHub token・AWS keyパターン検査は検出0。stage済み差分点検とcommitはgate終了後に行う。

### 2026-11-16 Group切替後の全件gate成功

- 同じsession78479が正常終了0。public_full_gate.logは全313検査、source/公理/固定仕様46286宣言の照合、7640rootsからの輸出coverage、14変更moduleのleanchecker再生、exporter自身が省く190内部補助のdirect probe、nanoda43972宣言が成功し、全56部品all gate成功で終わった。未完了processは残っていない。空の集約Proofsのみ再生prefixから除外する既存の安全なcache判定を用いた。冷えたCI・実push後20分の測定ではない。
- docs/group.md・experiments_status.mdをこの結果へ更新。source/API/純粋モデル/全23入口・群の法則・領域の対応、旧専用検証整理、catalog/両kernel/配布header検査を確認済み。浮動小数丸め誤差とlibrary3別APIの残件を証明済みとして扱わない。
- 次のMonoidに向け、標準draftのnumeric.limits.membersとmeta.unary.catを確認した。隔離native probe numeric_limits_contract.cppは8整数型のbounds、doubleの±infinity、単項minusを持たずdefault値7のNoNeg型でもeが使えることをASan/UBSan付きで確認した。Cppmaster/std traitsの分岐を削らず、不要なNeg T制約やunspecializedの0仮定を導入しない。ignoredの.cache/wip/monoid_restore/next_steps.mdにsource linksと設計上の注意を保存。実frontend/Monoidはまだ未変更。

- stage済みのdiff --checkで新規共通core末尾の空行が見つかったため、その1行だけを削除した（現在532行）。通常projectで再buildしsource audit成功。監査済みscratch版と再build版の保持helper閉包をlean4exportで輸出し、全バイト同一と確認した（eof_cleanup_review.json）。oleanにはメタデータ差があったがkernel式/証明は同一。全件gate後にアルゴリズム/命題/計算定義を変えていない。

### 2026-11-16 Monoid前提: 局所usingと標準min/maxの識別

- Group全体移行はlocal commit `0555ac14bccda589cba81a7e83bbf310fb44d3b4` に保存済み。pushなし。全体目標は継続中で、登録51/56の新方式化と元137原本の全移植・再公開は別である。
- lean_translate.pyで関数内のUsingDeclはstd::min/maxだけ受理し、ブロックスコープに記録する。依存呼出しはlookup候補がUsingShadowDeclのみの場合に標準演算へ対応させる。従来の関数名だけでのmin/max置換をやめ、ユーザー定義の同名・引数なし関数を通常呼出しとして翻訳する。標準min/maxの明示的template引数は未対応として拒否し、同名ユーザー関数への誤対応を防ぐ。
- construction12テストが成功。ASan/UBSan C++とLeanの差分で標準/ユーザー関数、局所usingのスコープ、非テンプレート呼出しを確認し、unsupported using/明示template引数の負例を追加した。登録済みlean_model全51部品をfresh生成し、保存モデルと全文一致。Proofs/C++master/TOMLの変更なし。Group後の全件gateをこのfrontend変更後に実行したとはしない。
- docs/translation.mdに対応範囲と一次資料を追記。ADLで独自動作に差し替える型について標準min/max契約への対応を証明したとはしない。Monoidの依存型traits/numeric_limits、公開field観測、純粋数学証明は引き続き未完了で、部品移植完了・push可能とは扱わない。
- 既存friend翻訳8テストも成功。Monoid候補の実翻訳はUsingDeclを通過し、次の未対応expression UnresolvedLookupExpr（依存traits）で拒否されることを再確認。git diff --check成功。今回のfrontend/テスト/翻訳仕様/handoffの4ファイルは未commit、稼働中の検査processなし。次はtraitsとnumeric_limitsの契約・型ごとの具体化を実装する。

### 2026-11-16 Monoidの型ごとの数値traits・全入口候補

- 前ターンはprogress（UsingDecl対応・誤った同名min/max置換の修正・20テスト・51生成物照合）。その変更に続けて作業した。公開のMonoid header/TOML/旧証明はまだ変更していない。目標は引き続き137原本の全移植・再公開と実push後CI20分であり、登録51/56で完了とはしない。
- Cpp.Preludeにデータclass NumericTraits (tag : String) (T : Type)を追加。isFloatingPoint/hasInfinityとmin/max/lowest/±infinityの値を保持し、公理・全Int共通instanceは置かない。tagはC++型パラメータ名なので、T=int/U=long longを同じLean Intにしても別packetを渡せる。LP64の整数10型はdriverが具体packetを束縛する。cppのT型や関数を有限型に制限したものではない。
- 直接のif constexpr(std::is_floating_point_v<T>)をBool分岐として残し、then内の直接の負のinfinityだけpacketのnegativeInfinityへ対応させる。非浮動小数で破棄される枝のためにNeg Tを要求しない。他の文脈の単項minusは通常のNeg Tを維持する。任意のconstexpr式の分岐消去を一般に実装したものではない。
- decl/参照のtraitsとdependent numeric_limits min/max/lowest/infinityを翻訳し、e→default構築にも要件が伝播する。両枝returnの末尾へ不要なfailureを出していた点は、構文的なalways_returnsで直した。登録済み51モデルはfresh生成して全件一致を確認済み（public_fields情報追加直前）。
- ClassInfoはC++のpublic/private/protectedを記録。差分driverにfield Class.field indexを追加した。スカラー/vector/pairだけ観測し、非公開fieldとrecordを含むfieldのコマンドは生成しない。公開APIへgetterを足さずにMonoid.xを比較できる。CPPdriverは従来どおり元small_templateを先にincludeする。
- constructionの整数10型bounds比較、T/U同carrierの異なるbounds、NoNeg（default値7・Negなし）、doubleの±infinity、浮動小数packetの有限fallback、guard外minusの回帰を追加。浮動小数の演算一般の誤差を証明済みとは扱わない。nativeはASan/UBSan付き。最初のbounds比較は値がすべて一致したが生成Leanのdead-code warningで失敗し、末尾failure修正後に成功した。検査の警告出力を除外して通してはいない。
- 未公開の全3クラス候補をexperiments/verification/algebraic_structure/monoid.hppへ保存。元のhidden friend・qualified op・public x・value/default ctor・e・floating分岐を保持し、既定型は原本llと同じstd::int64_tへ戻した。型だけの旧witness/明示具体化は候補から除いた。候補全15入口の値・停止・work=1/2/3の証明はtests/lean/monoid_model_contract.leanにあり、fresh候補翻訳と結合してcompileするtestを追加した。
- 純粋モデルProofs/Cpp/Lib/MonoidMath.leanをsupport/Proofs.leanへ登録。Mulの結合則/単位元、Max/Minの結合則・範囲条件付き単位元・値選択/上下界・範囲の閉包、全operation frame≤4とnested callee≤4の領域上界≤8を証明しbuild成功。T演算の費用/表現サイズは別契約、C++heap/寿命/Leanstackを数えるモデルではない。
- 候補の全3クラス・hidden/qualified両opの差分は整数10型で成功（ignored verify_candidate.py）。再現用tests/diff/monoid.pyを追加し、候補int/long long/unsigned long longに対して極値のidentityと全組のopをCPP/Lean/独立期待値で比較するtestも成功した。ケース最大積121はsigned charにも収まる。
- 関連unittest discover test_lean_model_*.pyは26件成功（frontend_tests.log）。その開始後に追加した候補全組差分1件も成功し、現時点の19 construction+8 friendをカバーする。registry全56と編集proof-source監査、diff --checkも成功。全件all gate/両kernel再監査済みとはしない。
- 登録全56のbridgeを同じexec session81154で継続中（bridge_frontend.log、jobs2、timeout1800）。最後の観測はfenwick_tree開始、ここまでfailureなし。観測の切れだけで再起動しない。終了後にこの段落へ結果を追記する。
- 次の切替では旧MonoidCall(769行)/MonoidCallCore(294)/MonoidCallCoreInt(292)/Generated.Monoidを整理する必要がある。Coreのmul_execは部品固有Generated.Monoidに依存するが、ctor/const/refs/e等の共通補題はLegacyScalarCallCore・IntervalCall・ScalarRefs・MonoidLazyCall等が使う。既存test_original_template_classes/test_nested_templatesとtests/lean/original_nested_max.leanが旧MonoidInstance/MonoidCallへ比較する箇所を持つ。共有部分を必要分だけ保ち、テスト固有参照モデルを分離してから専用生成物を消す。元CPP変更によるbugfixではないのでfixes.mdには追記していない。
- 同じbridge session81154が正常終了0。全56件が成功し、末尾はpublic checks passed for 56 component(s): bridge。稼働中bridgeはない。候補31root（15入口+12純粋定理+traits4定義）の独立kernelを別のsession37070で実行中（candidate_kernel.log）。
- 同じcandidate kernel session37070も正常終了0。31rootの閉包1889宣言がnanodaでエラーなし。今回の候補単位の確認であり、全プロジェクトのleanchecker再生・固定仕様catalog更新・全件all gateを代替しない。新規定理/定義はcomponent切替時に固定仕様へ反映する。未完了processはない。

### 2026-11-16 Monoid公開側切替と旧専用証明撤去（全件gate中）

- 前ターンはprogress。全入口候補/traits/field観測をlocal WIP 447fc938b16f99599de0e7937c95219d831a95e8へ保存済みで、そこから作業を続けた。現在は未commitの移行変更がある。全体目標は137原本の全移植・再公開と実push後CI20分であり、登録済み全件の移行だけでは完了にならない。
- 公開monoid.hppを全3クラス候補へ切替。任意T、public x、暗黙value/default/e、hidden friend/qualified opを保持。既定型は原本ll=int64_tと同じstd::int64_tへ戻し、native static_assert3本を追加。型だけの有限witnessと明示具体化を撤去。旧原本のfield/全method署名・body/hidden friend bodyの比較も成功（パラメータ名とstd修飾・local usingのみ正規化、original_api_review.json）。初期化の意味と停止は生成対応証明/native検査で別に確認する。
- 登録はlean_model/Proofs.Cpp.Monoidへ切替。新Gen.MonoidとCpp.Monoidを追加し、全15入口の返り値・正常停止・work1/2/3、およびMonoidMath12定理の公開root wrapperを接続。3クラス・6公開宣言・1hpp/1TOML/1文書を維持し、差分は10整数型の各468出力が一致した（public_bridge.log）。cpp/テンプレート先行includeも成功（public_cpp.log、static_assert追加前の対象実行。新assertも全件gateが検査する）。
- Proofs/MonoidCall.leanとGenerated/Monoid.leanを撤去。Core/CoreIntから部品固有mul_execとGenerated.Monoid importを削除し、共有のconst/ctor/ref/e等の補題だけ残した。旧MonoidCall/Int互換namespaceの一般wrapperはLegacyMonoidCallCore.leanへ移し、IntervalCallのimportを更新。元の声明を弱めてはいない。
- 旧frontendの既存テストが必要とする閉じたNProgram参照11本をtests/lean/monoid_reference_programs.leanへ移し、残る入れ子Maxテスト用の参照証明だけmonoid_reference_calls.leanへ分離した。public Proofsから参照/依存しない。テスト内のMonoidInstance比較をこの独立参照へ向けた。未公開候補headerと重複contract fixtureは撤去し、構築回帰は公開masterからfresh生成して正本証明を読む。
- 元クラス8テスト成功。nested_templates10は最初9成功/1失敗。テスト外namespaceへの証明移動でopen Proofsを落としたことと、不要なsimp引数・非推奨補題名を修正。失敗したtest_original_nested_maxだけの再実行は独立kernel3659宣言とnativeを含め成功（nested_max_retry2.log）。検査の警告やエラーを除外していない。construction19も成功。全件gateがnested10件すべてを改めて確認する。
- 固定仕様catalogはroots4389→4356、closure7855→7825、削除112、既存宣言のhash変更0で更新成功（catalog.log）。--accept-changedは不要で使っていない。移動したhelperが旧rootの型閉包に残らないため、既存声明のmodule移動による変更もない。
- 暖まった前提oleanの下、1CPU/LEAN_NUM_THREADS1で旧4targetと新6targetを各1回fresh compileし、全10件成功。対象コンパイラ作業量は増加した。新側は純粋法則/全15入口/共有coreを含めて測っており、減少やCI20分達成を主張しない。方法・環境・値・source hashはignored benchmarks/local/monoid_migration_20261116/measure_build.pyとbuild_delta.jsonだけへ保存。冷えた全build・client再build・実push後CIの測定ではない。
- 現在の公開56hppだけをZIP化し、全ファイル一致・各header単体/同時includeのcompile成功（package.log）。archive/manifestは同じignored benchmark directory。docs/monoid.mdと台帳を新方式の範囲・未完了gate・浮動小数一般誤差の残件へ更新した。traitsの未選択fieldには任意値を渡せることを翻訳表へ明記し、has_infinity等のない非浮動小数の特殊化へC++側の宣言を追加要求しない。
- 全件gateはexec session20664で実行中: .cache/wip/monoid_restore/public_full_gate.log、check_public.py --mode all --jobs4 --timeout-seconds7200。入力を固定し、以後handoffだけ追記する。同じhandleの実終了コードを確認するまで再起動しない。完了後は失敗対応またはsource/公理/固定仕様/leanchecker/nanodaの結果、全56部品の成功を確認してからdocsの検証完了状態・差分/機密点検・local commitを行う。pushなし、CI/releaseの実確認も未実施。

- gate待機中の次作業調査で、元experiments/library/cpp/modint/modint.hppの2件をASan/UBSan付きで再現した（.cache/wip/modint_restore/original_boundaries.cpp/out、boundaries_review.json）。ModInt<7>(-7).get()とset(-14)が7（期待0）、素数m=4294967291で(m-1)+(m-1)が4294967284（期待4294967289）。前者はpublic modint.hppの既存コメントにも記載されているが、原本は未修正。後者はuint32_t加算のwrapで比較判定を誤る。ここでは前提に吸収せず、次のModInt原本全体移植で修正と専用回帰・docs/agent/fixes.mdへの記録を行う。現在はMonoid gate入力を固定しており、その原本/公開コードや台帳はまだ触っていない。元のmodint constructor/setのsigned/unsigned member template、SFINAE、非型法parameter、負のpow、stream等も復元対象で、既存の縮小public APIを移行完了基準にしない。
- 次ModInt原本のfirst unsupportedは実際にはclass member FunctionTemplateDecl（frontend_requirements.json）。非型法parameter・SFINAE・member templateの全体対応が必要で、最初の診断だけを全不足項目とはしない。大きな法4294967291は平方根までの試し割りでも素数と確認した。原本の素数前提から外れた例ではない。
- 直近の同じ全件gate session20664は164件成功/失敗marker0。template_class_layoutのrecord/compose一般回帰を継続中。実終了はまだ確認していない。登録のlean_modelは52/56（Monoidはこのgate待ち）、残る旧登録はmonoid_lazy/modint/dynamic_modint/rolling_hash。今回の切替変更は未commitで、直前のWIP HEADは447fc93。稼働中の検査はこのgateだけで、子テストを別途再起動しない。

### 2026-11-16 全件gate継続と次ModInt修正候補

- 同じgate exec session20664をこのターンでもpollし、liveと確認。直近256件成功/失敗marker0。共有template/旧変換器の回帰を継続しており、最終両kernelはまだ未確認。再起動していない。Monoid関連の正本・証明・metadata・テストは固定したまま、handoff以外のtracked入力を変更していない。
- 待機中に次ModIntの候補を.cache/wip/modint_restore/repaired_original.hppへ保存した。原本全ファイルのAPI、SFINAE付きsigned/unsigned ctor/set、friend/stream、fac/C/initも削らず、signedのctor/setは2回剰余で0へ正規化、+=/-=はuint64中間値で還元、負powは(pow(-(n+1)) * *this).inv()へ変更してLLONG_MINの符号反転を避ける。これは隔離候補のみで、原本/publicやfixes.mdはまだ変更していない（候補の書換えを原本修正として記録しない規則に従う）。
- 原本を直接includeするbaseline_driverも用意し、負の法倍数がmになること、大きな法4294967291の加算が4294967284（期待4294967289）、0-(m-1)が6（期待1）、pow(LLONG_MIN)がUBSanのnegationエラーで停止することを確認した。baseline_failures.json/pow_min_baseline.stderrへ保存。法の素数性も試し割りで確認しており、原本の素数前提に反する例ではない。
- 修正候補は同じ公開演算をnative ASan/UBSanで実行し、5法（2/7/998244353/2147483647/4294967291）×836出力が独立Python整数剰余/モジュラpowと全一致した（check_repair.py、repair_checks.json、cases_*.txt）。符号付き/符号なしの型幅境界・乱数、receiver自己参照の加減算、signed指数両端を含む。候補のCPP正しさの有限検査であり、Lean対応/時間領域の証明やModInt原本全体の公開移植完了ではない。
- 先にMonoid全件gateを完了してlocal保存した後、これら原本修正と専用回帰・fixes.md記録、ModIntの全API（非型parameter/member template/SFINAE/負pow/streams/fac/C/init等）復元を進める。既存縮小public ModIntを完成形にしない。
- 次ModInt候補の純粋補題をignored BoundaryMath.leanへ用意した。Int.tmodを2回使う正規化=Int.emod、正規化中間値、1回還元の剰余との一致、uint64加減算の値域・剰余関係・中間幅/非underflow、負指数のnatAbs分解とLL範囲内の段階、inverse/powの代数法則を証明し、警告なしでcompile成功。候補の補題だけで、Cpp非型/member-template/グローバルfacとの機械対応は未実装。独立kernelの確認結果はboundary_kernel.logへ保存する。
- 同じgate session20664の最新ログは295件成功/失敗marker0。終端のall成功はまだない。ModInt隔離BoundaryMath14rootは別session36535で正常終了し、nanoda2256宣言がエラーなし（boundary_kernel.log）。ModIntの補題/CPP候補/driverはすべて.cache/wip/modint_restore内で、未反映・未commit。Monoid gate以外の検査processは終了済み。次も20664をpollし、止まっていない検査を再起動しない。

- 同じgate session20664で全313検査が成功し、最終監査へ進んだ。raw source/公理依存/固定仕様照合46387宣言が成功。7708rootから34282 project宣言を輸出する準備ができ、126変更moduleのleanchecker再生も成功した。所有宣言0の集約Proofsだけを既存cache規則で再生対象から除いた。現在はexport開始後で、coverage/direct probe/nanoda/最終終了コードはまだ未確認。ここを全件完了と誤読しない。
- 次ModIntの完全APIをClangから棚卸しし、api_inventory.jsonへ保存した。対象はModInt class templateだけでなくmint/mint17、MAX_FAC、可変global fac、自由関数C/initも含む。既存縮小public側からの棚卸しではこれらを落とすため、原本を基準にする。候補CPP内のsmall_template includeは隔離実行用の絶対パスであり、正本へ丸ごとコピーせず本体の差分だけ反映する。

### 2026-11-16 Monoid新方式の全件gate成功

- 継続していた同じexec session20664が正常終了0。全56部品・313検査に加え、source/公理依存/固定仕様46387宣言、7708roots→34282 project宣言の輸出coverage、126変更moduleのleanchecker再生、nanoda44069宣言がすべて成功した（public_full_gate.log）。exporterが省く190内部補助はdirect probeで同じ省略を確認し、輸出漏れを放置したものではない。所有宣言0の集約Proofsだけを既存の安全な再生cache規則で除外した。未完了の検査processは残っていない。
- docs/monoid.mdと台帳をこの結果へ更新した。測定値と環境は引き続きbenchmarks/local/だけに置く。対象ビルド増分は増加しており、冷えた全buildや実CI20分達成とはしない。浮動小数の一般演算誤差とlibrary3の別APIなどの残件は引き続き台帳対象で、原本137全体の完了とはしない。
- 検証済みの移行差分とこの記録をまとめてローカルcommitへ保存する。次セッションはgit log/statusの実状態を確認してからModIntへ進む。公開履歴には先行89 local commitの複数部品/途中作業があるため一括pushしていない。pushは原本1ファイルの完了単位と毎回の手動承認、対象SHAのCI/release確認が必要。
