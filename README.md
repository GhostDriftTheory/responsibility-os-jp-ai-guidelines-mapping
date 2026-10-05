# Responsibility OS × AI事業者ガイドライン

[![Lean verification](https://github.com/GhostDriftTheory/responsibility-os-jp-ai-guidelines-mapping/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/responsibility-os-jp-ai-guidelines-mapping/actions/workflows/lean.yml)

**From governance principles to evidence-bound execution across the AI value chain.**

**Repository:** `GhostDriftTheory/responsibility-os-jp-ai-guidelines-mapping`

**Verification status:** CI builds `JPAIGuidelinesMapping.lean` with Lean 4.26.0 and checks
the source with warnings treated as errors. The `Lean verification / verify` result
for the exact commit is authoritative. Verified commit:
`81182a03e13d2da3a2080210db02183f2e99238f`.

Verified commit:
81182a03e13d2da3a2080210db02183f2e99238f

JPAIGuidelinesMapping.lean SHA-256:
db1bc2c9de89cf8f7581c6e148d48d12a17ea17e60f82a6918385a0eaf043dcc

Lean:
4.26.0

Responsibility OS Kernel:
9b4e7d25572f3a1e114508bdf1a2d62349e83993

mathlib:
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

## 指針への「対応表」から、実行に結び付く証拠連鎖へ

**誰に渡っても採用根拠と利用条件を切り離さず、条件が変われば古い承認では動かさない。**

AIの開発・提供・利用をつなぐ主体間の引渡しを、文書・証拠・利用範囲・再検証・実行記録まで結び付ける**公開抽象プロファイル**です。変更しない **Responsibility OS Kernel** の上に、日本のAI事業者ガイドラインを対象とする独立したプロファイルを構成します。

中核は `no_silent_responsibility_gap`。**局所的な適合条件を満たす実装に対し、実行より前の再検証、主体間の連続性、全段階の利用範囲、当時の証拠区別、保持と継続評価を、任意の有限履歴について結び付ける合成定理**です。単なる原則名の置換でも、具体的な製品プロトコルの公開でもありません。

**対象は選択した技術的要件の参照仕様です。ガイドライン全体への準拠、法的責任の確定・免責、AIの現実世界での安全性を証明するものではありません。非公開の検査器や制御実装が局所条件を満たすことは、別途立証する必要があります。**

### この配布物の確認状態

| 項目 | 状態 |
|---|---|
| 公開内容 | 単一Leanファイル、対応表、配置設定。具体的な業務パケット形式・受領確認形式・承認更新アルゴリズムは含めない |
| Leanコンパイル・証明検査 | **未完了（2026年10月5日）**。`lake build JPAIGuidelinesMapping`とwarning-as-error検査の起動を試みたが、実行環境に`lake`がなく終了コード127。公式配布元からの環境取得も名前解決失敗で進められなかった。Leanによる型検査・証明検査は開始できておらず、検証済みとは表示しない |
| 前版の有限モデル検査 | **本改訂の検証結果として引き継がない**。公開モデルと前提が変更されているため、前版のPython検査件数・成功を本版の証明に用いない |
| ガイドラインの対象版 | 提供された対応表と同じ、第1.2版・2026年3月31日公表の版を対象とする [S1] |
| 条項対応の根拠 | 提供された前版READMEの「最終版との条項番号・主体構造・表1の照合済み」という報告を引き継ぐ。**本改訂では公式最終本文の再取得・独立した逐条照合は行っていない**。脚注・細則を含む全文の逐語照合済みとも扱わない |

Leanの検査、ガイドラインの解釈、非公開実装との対応は別の確認です。いずれか一つの成功で、残りまで確認済みにはなりません。

## 1. 一つの保証連鎖として何を扱うか

```text
変更しない Responsibility OS Kernel
    │ 型付き証拠 / 重要な証拠区別 / 構造的な遡及監査
    ▼
Semantics      主体・範囲・証拠拘束・引渡しの意味上の観測と関係
    │ 実装固有の型・フィールド・通信形式は指定しない
    ▼
局所適合条件  HandoffLaws / AdapterLaws
    │ 各引渡しの拘束・範囲、採用検査の健全性、再検証の来歴、条件変更時の扱い
    ▼
公開参照ゲート・有限履歴
    │ allow / withhold / stop、試行記録、保持、更新の交錯
    ▼
統合定理       過去の再検証 → 全経路の裏付け → 実行 → 当時のPolicyによる監査
    │ 最終保持リストの一致 / 現在の支持証拠と再確認対象への分類
    ▼
実装適用       非公開の実装対応証明を接続する。公開定理だけで接続済みとはしない
```

### 公開するのは意味上の条件であり、実装方法ではない

`C`（判断文脈）、`B`（保証に関する観測）、`U`（利用）、`A`（主体）、`S`（制御状態）、`I`（再検証入力）は任意の型です。これらの具体的なフィールドは公開ファイルにありません。`Semantics`は、ある主体がどの範囲を裏付けるか、どの文脈に証拠が拘束されるか、どの二段階が引渡し関係にあるかを表す**関数・述語のインターフェース**です。

`Interface`の検査・再検証・条件変更も引数として与える関数です。実際にどう検査し、どの情報を保持し、どう古い採用根拠を無効にするかは実装しません。`Admission`は公開する**意味上の事後条件**であって、非公開検査器の内部判定式ではありません。

### 主体の列挙ではなく、全経路の性質を結び付ける

`ValueChain.Valid`は、抽象的な引渡し関係をつないだ有限経路です。各引渡しが証拠拘束を保持し、利用範囲を拡大しないという局所条件から、全経路の拘束と範囲の性質を帰納法で導きます。実行された利用は、最後の段階だけでなく、起点と途中のすべての段階の範囲に含まれます。

採用検査には、観測された主体列が、その時点で設定された主体列と一致するという局所的な健全性条件を置きます。**具体的な受領確認の構造や検査アルゴリズムは公開しません**。開発者→提供者→利用者は例であり、同一法人の複数役割、社内引渡し、多段構成、同じ主体の再登場を排除しません。必要な経路自体の妥当性は外部判断です。

### 条件変更と過去の承認を区別する

`AdapterLaws`は、条件変更だけでは実行可能な根拠を作らないこと、再検証後に利用可能となる根拠には当該再検証の受理があること、採用検査が現在の適用条件を満たすことを求めます。これにより、**再検証を挟まないA→B→Aの条件変更だけで実行許可が復活しない**ことを導きます。

その実現方法は指定しません。後から新たに再検証した場合の旧資料・旧受領確認の扱いは、実装側が`current`と検査の健全性をどう立証するかに依存します。特定の失効方式まで公開ファイルが検査した、とは主張しません。

## 2. ガイドラインとの対応表

条項番号・要旨は提供された前版の対応表を基礎とし、同READMEが報告する最終版の条項番号・主体構造の照合結果を引き継いでいます。これは本改訂での独立した再照合や、全文の逐語一致の確認を意味しません。**条項の要請、公開参照仕様、局所的な前提、導かれる結論、実装外の評価を区別します。** ガイドラインがこのデータ構造や制御方式を指定するという意味ではありません。

宣言名には `JPAIGuidelinesMapping.` が付きます。D/P/Uは開発者／提供者／業務でAIを利用する者です。原文の合理的範囲・リスクに応じた対応という限定を、一律の義務に置き換えません。[S1][S2]

| ガイドラインの対応箇所 | 主体 | 参照元の要旨 | Responsibility OSの公開参照仕様 | Lean宣言・結論 | 意味上保持する証拠 | 外部で必要な評価 |
|---|---|---|---|---|---|---|
| 第3部 D-6(i)、D-7(ii) | D | 開発の事後検証・文書化 | 型付き証拠と文脈への拘束を抽象関係で表す | `ValueChain.every_stage_is_bound`、`KernelConnection.standard_evidence_keeps_operation` | 元の証拠と適用文脈 | 文書内容・網羅性・真正性、`bound`の意味付けと局所条件の立証 |
| 第4部 P-6(i)、P-7(ii) | P | 構成・処理過程、規約等の文書化 | 現在文脈、文書文脈、参照計画の整合を確認する公開監視仕様 | `Governance.current_support_document_binding` | 文書・計画の参照と支持判定 | 説明・規約の内容、参照と実文書の結合、法的有効性 |
| D-7(i)、P-7(i)、U-7(ii) | D→P→U | 対応状況の説明と提供文書の活用 | 主体列の一致と、実行より前の再検証を結び付ける | `Safety.required_route_is_exact`、`History.origin_is_validation_occurrence`、`execution_has_prior_assurance` | 意味上の主体経路と先行する受理済み再検証 | 実際の受領・理解、説明の十分性、経路設定、具体的検査器の健全性 |
| D-6(ii)、P-6(ii)、U-2(i) | D/P/U | 利用範囲の情報提供と適正利用 | 各引渡しの範囲非拡大から全段階の裏付けを導く | `ValueChain.no_scope_expansion`、`Safety.execution_respects_all_scopes` | 起点・途中・実行時の範囲関係 | 許容用途の選定、現実の操作と抽象利用の対応、各引渡しの局所条件 |
| 第2部C 6①・③、7①・⑥ | D/P/U | 検証可能性、追跡・文書の参照 | 全試行を記録し、保持と当時のPolicyによる証拠区別をつなぐ | `History.run_without_pruning`、`no_silent_responsibility_gap` | 順序・重複を含む保持記録、当時のPolicy | 実イベント収集、保持期限、永続保存、出力変換のPolicy保存 |
| 第2部C 7③・④ | D/P/U | 責任者・責任所在の明確化 | 主体と範囲を、先行する再検証・当時の採用条件に対応付ける | `ExecutionAssurance.priorValidation`、`Safety.required_route_is_exact` | 当時の主体列・条件と再検証の位置 | 本人確認・権限・契約・法的責任の分配。識別子だけでは代替しない |
| 第2部C 1・2、U-2(i)〔選択的な技術的寄与〕 | D/P/U | 人間中心・安全を考慮した利用 | 許可・保留・停止の公開ゲート。採用検査と意味上の条件は局所契約で接続 | `Safety.withhold_never_executes`、`History.stopped_run_stays_stopped`、`Safety.execution_is_locally_admitted` | 要求・採用判定・結果 | 検査器の健全性、人の介入手段、完全仲介、危険検知、物理的安全停止 |
| 第2部E ①〜③ | D/P/U | リスク・目標を踏まえた設計と運用 | 条件変更だけで許可しないという実装非依存の義務を、履歴へ接続 | `Safety.reprofile_requires_revalidation`、`History.profile_ABA_requires_revalidation` | 意味上の条件変更と再検証の先後関係 | リスク分析・設計・変更承認の妥当性、変更時の局所契約を満たす実装 |
| 第2部E ④・⑤、C 7⑤ | D/P/U | 継続評価・改善・環境変化への対応 | 文脈・文書・計画の整合と適用性チェックを用い、保持対象を分類 | `Governance.stale_evidence_requires_review`、`Governance.monitoring_preserves_occurrences` | 現在の支持証拠／再確認対象の分類 | 現在性チェックの健全性、評価基準、未観測リスク、実際の是正・改善 |

P-7(ii)を一般的な技術文書化だけの条項として扱わず、構成・処理過程にはP-6(i)、規約等にはP-7(ii)を対応させる整理を維持しています。第2部Eについては、選ばれた条件を運用・評価・再検証へ接続する部分が対象です。組織のアジャイル・ガバナンス全体や、改善活動の実施までを証明したという意味ではありません。[S1][S2]

## 3. 主定理の正確な意味

### `no_silent_responsibility_gap`

未承認の制御状態・空の試行履歴から開始し、`attempt / revalidate / reprofile / prune`を任意の有限回数・順序で実行します。主な前提は、**局所的な適合条件、初期状態での根拠の未承認、中間削除基準が最終監査時刻以下であること、保持された実行記録の当時のPolicyを監査ビューが保存すること**です。

その下で`HistoryAssurance`として導く結論は、次の通りです。

1. **保持対象の履歴が失われない。** 中間削除を一切行わない参照実行と、最終保持リストが完全に一致します。順序と同じ記録の重複回数も対象です。
2. **実行より前の再検証までたどれる。** 各実行記録には、その記録が作られた操作位置と、それより前の受理済み再検証が存在します。当時の採用条件において、主体列、現在適用性、設定範囲、有限経路が結び付きます。未来の再検証を過去の実行根拠にする結論ではありません。
3. **起点と全段階の裏付けがつながる。** 局所的な引渡し条件から、実行対象の全段階での範囲内性と、文脈への証拠拘束を導きます。最終Profileへの読み替えではなく、記録時のPolicyで証拠区別を扱います。
4. **継続評価から記録を落とさない。** 保持対象を支持証拠と再確認対象へ排他的・網羅的に分類し、件数を保存します。支持証拠には現在文脈・文書・参照計画の整合と各チェックの成功が伴い、不成立は再確認対象になります。

`ExecutionAssurance`は一件の実行に対応する**結論**です。入力データに「全記録が正しい」という証明を持たせているのではありません。`History.record_has_production`、`History.run_available_origin`、`History.origin_is_validation_occurrence`が、記録の生成位置と先行する再検証を、実際に扱った論理的なコマンド列から導きます。非公開の制御状態そのものを公開記録に丸ごと保存する仕様でもありません。

### 抽象化によって変わった検証境界

この公開版は、**非公開実装が局所契約を満たすなら、組み合わせた有限履歴全体について何が成立するか**を示します。具体的な判定器・受領確認検査・承認更新方式まで公開して検証するモデルとは、検証対象の粒度が異なります。

`HandoffLaws`は一段の拘束保存と範囲非拡大、`AdapterLaws`は検査の健全性・再検証の来歴・条件変更時の不許可と文脈反映を求めます。これらは引数として渡す局所条件であり、無条件に導入した公理ではありません。**実装側の条件が未立証なら、公開定理だけを根拠に当該実装を検証済みとは呼べません。** 逆に、すべての出力記録が保証済みであることや、履歴全体の結論そのものを前提にはしていません。

### 全データの開示・可逆変換を必須条件にしない

主定理の出力側の前提は`ResponsibilityOS.PreservesPolicy`です。選択された重要な証拠区別が保存されればよく、全データの公開・全情報の可逆変換を必須にはしません。Policyを満たす限定的な監査ビューも対象になります。

`no_silent_responsibility_gap_recoverable`は往復則を十分条件とする版、`Transparency.composed_exports_preserve_policy`は二段階の可逆なビューを十分条件として扱う補助定理です。これらは秘密保持・匿名化・法令適合性を保証するものではありません。

## 4. 最小の存在証人と抽象的な帰結

`Examples.toy`を残す目的は、**局所条件を満たすモデルが存在し、実行された記録が実際に保持され、非空の証拠Policyとも両立すること**だけです。本番実装や推奨プロトコルのひな型ではありません。

文脈・根拠・利用・主体・再検証入力をそれぞれ一要素の型にし、制御状態だけを二値にした退化的な例です。三役割の具体的経路、用途の判定分岐、再検証入力の判定式、受領確認・世代・失効方式の具体例は含めません。空経路を使うこの存在証人から、実際の主体間引渡しの正しさを主張しません。主体横断の経路・範囲・不成立時の帰結は、本文の一般定理で扱います。

`Examples.view_laws`と`Examples.toy_laws`は、この最小モデルが局所条件を満たすことを示す証明項です。`Examples.nonvacuous_reference_chain`は、主定理の結論、**同じ実行列の保持履歴に存在する実行済み記録**、Kernelの非空`tracePolicy`を組み合わせます。全件保留・空のPolicy・実行記録を含まない監査だけを成功例にはしません。

| 例・性質 | ソースに記述した結論 | 宣言 |
|---|---|---|
| 最小モデルの局所条件と実行 | 未承認状態から再検証を経て実行され、その記録が保持される | `Examples.toy_laws`、`Examples.minimal_execution`、`Examples.retained_execution`、`Examples.nonvacuous_reference_chain` |
| 必要な主体列との不一致・不正な経路 | 局所条件を満たす検査器の下では実行されない | `Safety.required_handoff_cannot_be_skipped`、`Safety.invalid_chain_never_executes` |
| 範囲の拡大・実行対象の範囲 | 拡大する一段は引渡し条件を満たさず、実行された利用は全段階の範囲内にある | `ValueChain.scope_widening_is_not_handoff`、`Safety.execution_respects_all_scopes` |
| 条件変更・再検証不成立 | 条件変更だけでは許可されず、不成立の再検証後も許可されない | `Safety.reprofile_requires_revalidation`、`Safety.failed_revalidation_closes_gate` |
| 重要な責任証拠を落とす出力 | 非空Policyが要求する区別を失う | `Examples.operation_only_view_fails` |
| 未来の基準時刻による削除 | 後から保持対象を取り戻せない反例 | `History.future_cutoff_counterexample` |

最小モデル以外の行は、元から存在する抽象定理・反例への参照です。具体的な業務用チェッカーや失効方式を例として再公開しません。これらの証明項は本改訂でのLeanビルド・厳格検査を完了しておらず、前版のPython有限テストも本改訂の検証結果として使いません。

## 5. EU版との関係と公開範囲

元のEU版の公開要素である、許可・保留・停止、文脈／文書／計画の参照、保持期限、証拠区別の保存、監視時の分類、削除なしの参照実行との履歴比較を基礎としています。EU版のリポジトリもKernelも変更しません。

日本版で追加するのは、**局所契約から、主体横断の全経路と実行より前の再検証を結び付ける抽象的な定理**です。追加の数学的な仕様・関係は公開されますが、具体的な業務パケットの構造、受領確認のフィールド、承認の更新・失効アルゴリズム、専用チェッカー、非公開の制御状態の内部は公開対象に含めません。単にLeanの`private`や`opaque`を付け、実装本文を同じ配布物に残す方法は採りません。

日本のガイドラインにEU法の保存期間・適合性評価制度を持ち込みません。二つの制度の完全な同値性を主張するものでもありません。広島AIプロセスは第2部Dとの関連として参照できますが、全項目をこのファイルで重複形式化したとは主張しません。Responsibility OSの対象領域を、選択した条項・産業・用途へ限定しません。

## 6. 実装と保証の境界

**意味付けと実装対応。** `bound`、`scope`、`current`、主体経路等が、実際の要求・文書・利用を適切に表すことは外部で立証します。局所契約に「証明済み」というラベルを付けるだけでは足りません。公平性・プライバシー・セキュリティ等の具体的な評価手法を、この公開版がすべて実装したわけでもありません。

**真正性と完全仲介。** 人・文書・評価結果・経路の観測とモデルを真正に結合する必要があります。実際の実行がゲートを迂回しないこと、操作と抽象利用の対応、論理停止と安全な実機状態の接続は、実装側の検証事項です。カテゴリのfaithfulnessを自動ログ収集や物理的安全性と同一視せず、一意因子分解を実行リプレイとも呼びません。

**履歴・保存・時間。** 証明の対象は、与えられた有限コマンド列と、この参照モデルが生成した履歴です。入力されなかった実イベントを補完しません。コマンド列での再検証来歴を扱いますが、特定の台帳構造や無期限保存を指定しません。保持期限・時刻・永続保存・改ざん耐性は別途必要です。中間削除基準が最終監査時刻以下という前提は、明示した反例が示すとおり重要です。

**削除履歴に依存しない参照制御。** このモデルでは検査・更新は抽象制御状態と入力に依存し、削除される公開試行履歴を参照しません。実装がその履歴を用いて実行可否を変更する場合は、追加の対応証明が必要です。全システムの分岐・合流や無限実行の生存性までを証明していません。

**現在の支持証拠と過去の価値。** 再確認対象には、当時は正当に実行されたが現在は再利用できない記録、適切に保留・停止した記録も含まれます。再確認対象であることは、過去の違反・事故の認定ではありません。`MonitoringPlan.current`による現在性の判定自体は外部検査であり、肯定・否定結果の組込みと分類を公開モデルが扱います。

これらは本公開プロファイルの境界であり、Responsibility OS全体の適用範囲や実装可能性を限定するものではありません。公開範囲を抑える設計は、特許・公知性・営業秘密についての法的な保証を意味しません。

## 7. 配置と検証

リポジトリ名の案は **`responsibility-os-jp-ai-guidelines-mapping`** です。この配布によってGitHubへの作成・アップロードは行っていません。

```text
JPAIGuidelinesMapping.lean   # 公開抽象仕様・証明・最小存在証人
README.md                  # 対応表・前提・結論・公開範囲
lakefile.toml              # 既存日本版と同じ固定依存・ビルド対象
lean-toolchain             # Lean 4.26.0
.github/workflows/lean.yml  # ビルドとwarning-as-errorのソース検査
```

**日本版をすでに配置している場合は、LeanとREADMEの2ファイルを同時に差し替えます。** 添付されている他の3ファイルは前回の日本版から変更していません。初回配置は5ファイルを上の構造のままリポジトリ直下に置きます。EU版を上書きせず、旧版ソース・旧README・バックアップを公開用ZIPやリポジトリへ併記しないでください。

| 依存 | 固定値 |
|---|---|
| Responsibility OS Kernel | `9b4e7d25572f3a1e114508bdf1a2d62349e83993` |
| mathlib | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Lean toolchain | `leanprover/lean4:v4.26.0` |

Git・elanがある環境で次を実行します。

```sh
lake update
lake exe cache get
lake build JPAIGuidelinesMapping
lake env lean -DwarningAsError=true JPAIGuidelinesMapping.lean
```

公開時は対象コミットの **`Build mapping` と `Verify source with warnings as errors` の両方**が成功したことを確認します。前版の緑色表示・検証記録を使い回しません。成功コミット、ソースのSHA-256、Leanの版、解決された依存を記録してください。

本版には実装側の局所条件が明示的な引数としてあります。CI成功後も、非公開実装の局所条件の立証・実装対応・ガイドライン解釈の妥当性まで確認済みになるわけではありません。

## 8. 参照元と版の扱い

[S1]: https://www.meti.go.jp/shingikai/mono_info_service/ai_shakai_jisso/20260331_report.html
[S2]: https://www.ipa.go.jp/disc/committee/begoj9000000egny-att/20260305_009_04_00.pdf
[S3]: https://www.ipa.go.jp/disc/committee/begoj9000000egny-att/20260305_009_11_00.pdf

**[S1] 対象版の公表先。** 総務省・経済産業省「AI事業者ガイドライン（第1.2版）」、2026年3月31日。最終版本編の参照先として、提供READMEは[経済産業省PDF](https://www.meti.go.jp/shingikai/mono_info_service/ai_shakai_jisso/pdf/20260331_1.pdf)と[総務省PDF](https://www.soumu.go.jp/main_content/001064279.pdf)を挙げています。同READMEによる条項番号・主体構造・表1の照合報告を引き継ぎますが、この抽象化改訂で同本文を独立に再照合したとは表示しません。

**[S2] 初稿の詳細対応に用いられた一次資料。** IPA公開、第9回AI事業者ガイドライン検討会・資料4「AI事業者ガイドライン（第1.2版案）本編」、2026年3月5日。変更履歴付きの案であり、最終版そのものではありません。案のページ番号を最終版に転用しません。

**[S3] 補助資料。** IPA公開、同検討会・資料11「AI事業者ガイドライン活用の手引き（案）」、2026年3月5日。役割整理・活用の補助であり、本文や最終版の同一性確認の代替ではありません。

**技術的基盤。** 提供されたEU版Lean、日本版Lean、改訂READMEを参照し、公開範囲と証明境界を組み直しました。Kernelは[指定コミット](https://github.com/GhostDriftTheory/responsibility-os-kernel/blob/9b4e7d25572f3a1e114508bdf1a2d62349e83993/ResponsibilityOS.lean)の外部依存です。具体的な非公開実装をこの配布物へ含めていません。

## English summary

This is a **public abstract assurance profile**, not a compliance certificate or an implementation disclosure. Contexts, evidence-bearing observations, actors, uses, controller states and validation inputs are type parameters. Local handoff and adapter obligations are explicit theorem premises. No private packet format, receipt-checking algorithm, approval-revocation mechanism or hidden-state snapshot is published.

`no_silent_responsibility_gap` derives a finite-history composition result: exact retained-history equality against a no-pruning reference run, validation provenance strictly before the captured execution, all-stage scope and binding consequences, preservation of each record's **historical** policy, and an exhaustive current-support/review partition. Policy-aware views are permitted; full recoverability is only a sufficient alternative. The headline conclusion is not assumed for every output record.

The concrete checker is not verified by hiding its body. An adapter must independently discharge the declared local obligations and establish correspondence to deployment. The source retains only a deliberately degenerate existence witness: context, basis, use, actor and validation input are singleton types, and control has two states. It demonstrates satisfiable local obligations, an actually retained execution and the kernel's nonempty trace policy, not a production adapter or a concrete multi-actor protocol. **This revision has not been compiled**: on October 5, 2026, both requested verification commands could not start because Lake was absent (exit 127); toolchain acquisition was also blocked by DNS resolution failure. Previous finite Python-model results are not reused as verification of this revision.

The guideline crosswalk inherits the supplied README's report of final-v1.2 clause-number/actor-structure reconciliation. This abstraction revision did not independently re-fetch or reconcile the final guideline text. Formal source checking, guideline interpretation and private implementation verification remain separate.

## License

© 2026 AI Assurance, Inc. All rights reserved.

No license is granted to use, copy, modify, distribute, sublicense, or create
derivative works from the source code in this repository except with prior
written permission from the copyright holder.

This reservation does not restrict rights arising under applicable law or
[GitHub's Terms of Service](https://docs.github.com/en/site-policy/github-terms/github-terms-of-service),
including their provisions for public repositories. Third-party dependencies
remain governed by their respective licenses; this notice does not relicense them.
No patent license is granted by this notice.
