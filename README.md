# Lean 4の学習環境と配布例

「Lean 4で始める数学の形式化」第1〜3巻で使う学習用プロジェクトです。Git、elan、VS CodeとLean 4拡張を用意してください。

```sh
git clone https://github.com/sakuramaguro/lean4-book-examples.git
cd lean4-book-examples
# 本に記載されたコミットへ git checkout してから進めてください。
cd lean
lake exe cache get
lake build
```

VS Codeでは `lean` フォルダを開きます。本文のコードは `Scratch.lean` の内容を全体ごと置き換えて試してください。残したいコードは別名で保存し、本文に連結の指定がある例ではその指定に従います。

| 対象 | 固定版 |
|---|---|
| Lean | 4.34.1 |
| Mathlib | d13f23b723b8a846827a245b89c10fc7d3f11612 |
| 間接依存 | lean/lake-manifest.json |

初回の取得にはネットワークと数GBのディスク容量が必要です。`lake exe cache get` はMathlibなどのビルド済みデータを取得します。通常の学習では `lake update` を実行せず、固定した版を使います。

## 収録ファイル

- `lean/LeanBook.lean`・`lean/Scratch.lean`：環境確認と練習の開始用ファイル。
- `lean/examples/Volume3Exercises.lean`：第3巻で配布を案内している、問題18.3の追加確認と総合演習18.4・18.5のコード。
- `lean/Audit.lean`・`lean/scripts/verify.py`：収録した例の実行と公理依存の確認。

第3巻の配布例は、`lean` フォルダで次のように実行します。

```sh
lake env lean examples/Volume3Exercises.lean
```

未使用の別フォルダへ取得する場合は、`git clone` の最後に `lean4-book-examples-vol3` のような保存先名を指定し、そこへ移動してください。

## 検証範囲

`lake build` が確認するのは環境確認用モジュールです。第3巻の配布例は上記コマンドで別に確認します。Python 3.10以降がある場合は、`lean` フォルダで `python3 scripts/verify.py` を実行すると、両方の実行と16宣言の公理依存を検査します。

この配布物には、書籍の本文・画像・全章の演習解答・原稿リポジトリの履歴は含めていません。掲載コード全体の検証は著者用の環境で行っています。第4巻はLeanの版が異なり、この配布物の対象外です。
