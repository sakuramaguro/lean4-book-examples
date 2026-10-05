# 第4巻の読者用コードと固定環境

『Lean 4で学ぶ確率過程と初等確率積分【第4巻】』第19〜24章で使う、独立したLeanプロジェクトです。本文の89掲載例、共通基盤、212宣言の公理監査を収録しています。書籍の本文・画像・原稿の履歴は配布に含めません。

| 対象 | 固定した版 |
|---|---|
| Lean | 4.33.0-rc1 |
| Mathlib | 0434c03386d3e7f7fd3ed95754543eabe4ab251b |
| BrownianMotion | 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9 |
| 間接依存 | 同梱の `lake-manifest.json` の13パッケージ |

第1〜3巻の `lean/` はLean 4.34.1です。第4巻は `lean-volume4/` をVS Codeで開き、このフォルダで実行してください。二つの環境のファイルを混ぜません。第4巻のLeanはリリース候補版で、最新版への更新を意味しません。

## 固定版を取得する

Git、Python 3.10以降、[Lean公式の導入案内](https://lean-lang.org/install/)に従ったelanとエディタを用意します。未使用の保存先に公開リポジトリを取得し、書籍に記載された40文字のコミットを指定します。

```sh
git clone https://github.com/sakuramaguro/lean4-book-examples.git lean4-book-examples-vol4
cd lean4-book-examples-vol4
# <書籍の固定コミット> を実際の40文字の識別子へ置き換える。
git checkout <書籍の固定コミット>
cd lean-volume4
python3 scripts/reader_catalog.py
```

この最後の検査にはLean本体と原稿は不要です。110個のソース・依存設定のSHA-256、89掲載例と83証明・6型確認の分類、公理監査212宣言を照合します。

## 初回の準備と実行

Lean本体と依存キャッシュの初回取得にはネットワークと十分なディスク容量が必要です。通常の学習では `lake update` を実行せず、同梱の固定版を使います。

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake exe cache get \
  BrownianMotion.Gaussian.BrownianMotion \
  Mathlib.Probability.Martingale.Basic \
  Mathlib.Probability.Distributions.Uniform \
  Mathlib.Probability.ProbabilityMassFunction.Integrals \
  Mathlib.Probability.Process.Adapted \
  Mathlib.MeasureTheory.Function.LpSeminorm.Basic \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Tactic.FinCases Mathlib.Tactic.Ring Mathlib.Tactic.NormNum \
  Mathlib.Probability.HasLaw \
  Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic \
  Mathlib.Probability.Distributions.Gaussian.Real \
  Mathlib.Probability.Independence.Integration \
  Mathlib.Probability.ConditionalExpectation \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

python3 scripts/verify_reader.py
```

この検査は、依存13パッケージの実コミットと追跡ファイルの状態、Leanの版、通常の `lake build`、212宣言の公理、89ファイルの独立実行を確認します。許容する公理は `propext`、`Classical.choice`、`Quot.sound` のみです。エラー・警告、`sorryAx`、未確認の独自公理を拒否します。Mathlibのキャッシュを取得し、BrownianMotionと本巻のソースは通常のビルドで確認します。手動の `LEAN_PATH` は使いません。

結果は `.generated/reader-verification.json`、実行ログは `.generated/logs/` へ保存します。開始時に前回の成功記録を削除し、全検査が終わるまで新しい成功記録を作りません。掲載例だけを試す場合も同じフォルダを使います。

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Volume4Chapter19/M02.lean
```

`Volume4Chapter19`〜`Volume4Chapter24` の `M*.lean` が本文、`A*.lean` が解答の掲載コードです。一つずつ先頭の `import` から実行し、別の例を連結しません。`Volume4Stage0`・`Volume4Elementary` などの共通基盤と `Audit.lean` も同じ固定版で取得します。

## 検証範囲

読者用の検査は原稿14ページやZennの設定を要求しません。原稿との一致は著者側CIで別に照合しています。全89例のうち83例が完成証明、6例が型・定義の確認です。48問の紙上の説明すべてをLeanで証明したことを意味しません。

到達点は有限分割の初等伊藤等長性と、一次元・定数係数SDEの存在・区間上の一意性です。一般の伊藤積分への拡張、一般形の伊藤公式、状態依存係数SDEの存在・一意性までは含めません。ブラウン運動の構成は固定版の既存ライブラリを使います。

GitHub ActionsはUbuntu 24.04で新しいチェックアウトから取得・準備・全例の検査を実行します。成功は対象コミットの実行結果で確認してください。未実施のmacOS・Windowsでの初回準備、実端末やZennの表示確認まで成功したという意味ではありません。
