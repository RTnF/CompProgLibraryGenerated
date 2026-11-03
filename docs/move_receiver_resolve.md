# receiverのfieldとpure scalar式から実引数評価を構成

`Proofs/CppMoveReceiverResolve.lean` は、借用vectorとscalar field参照、サイズfield読取り、外部のpure scalar式列から、実 `Context.resolveArguments` の成功と保存される引数列を一般に構成する。[receiver配置](move_receiver_layout.md)と[元UFのfields/QS/FW](union_find_receiver_layout.md)へ渡すresolve成功を、完成済みの入力条件から導出される結果へ移す段階である。

## 意味上の評価から実評価へ

`Ready` は任意長の式と値の組の列について、各式の結果型一致、scalarOnly、元caller環境での `denote = some value` を要求する。これは式の意味上の結果であり、実引数評価全体の成功や完成状態を要求しない。型のsupportやi32への固定はこの一般部分の前提にしない。

`stable_scalarCell` / `stable_environment` は既存のStable条件からfield読取りとscalar環境の保持を導く。`resolve_values` は既存のscalar式の完全性証明とこの保持を使い、左から順に実式評価・実引数評価を構成する。各式のwork/peakへの課金は実評価器に従う。`ready_values_valid` は評価される値が宣言型の範囲内であることも導く。

signed overflow等で意味上の評価が失敗する式にReadyを与えない。unsigned演算は元型のwrapを保つ。任意side-effectful式やvector観測をpure scalar式として受け入れない。

## vectorとfieldの接続

`resolve_receiver` は元vectorのcaptureBorrow、元counterのscalarCellと書込み権限、pure式列のReadyから、vector/counter参照と型付き値列の実resolve成功を構成する。vector引数はheader同一性を保ち、counterは元addressを参照する。

`ready_field` は現在のscalarCellからサイズfieldのvariable式の意味上の評価を構成し、外部式列の先頭に加える。`resolve_fields` はこのfieldを自動で先頭の値引数へ入れ、vector・counter・サイズfield・外部値引数という元UFの形へ接続する。サイズfieldとvector長を同一視しないため、moved-fromの空vectorにも元scalar値が残る。

ここで与えるslotは[同一TU receiver生成](context_method_receiver.md)がObjectRefから取り出すものに対応する。ObjectRef全体の元caller ASTからの選択・式評価までをこの定理だけで検証済みとはしない。

## 検査と残件

`tests/test_cpp_move_receiver_resolve.py` は元move後UFの全5methodについて、field cellと外部pure式の意味から実resolve成功を構成する。rootではfield読取りと算術式 `2+1` から、実resolve→prepare→compact→元fields/QS/FW→正常call→経路圧縮を一般定理で接続する。完成済みresolve/prepare/QS/FWやbody成功を先取りしない。

任意長suffixの一般定理、moved-from空vectorと元サイズfield、unsigned32最大値+1のwrap、signed32 overflowと不正counter slotの拒否も検査する。元C++は変更せず、既存のnative照合を維持する。

元ObjectRef/field slotからcaptureとscalarCell条件を一般構成し、生成wrapper・元caller ASTへ接続する作業は残る。callerのcallee/receiver/引数評価順と副作用、償却証明と任意混在寿命列、構築/返却/destructor、割当/resize/nested/異種vector、公開UFの元sourceとの相違と他旧ライブラリも未完了である。
