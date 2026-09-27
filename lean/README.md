# 第1〜3巻の学習用プロジェクト

取得と固定版の説明は[配布物のREADME](../README.md)を参照してください。このフォルダをVS Codeで開いて使います。

```sh
lake exe cache get
lake build
lake env lean examples/Volume3Exercises.lean
```

`Scratch.lean` に本文のコードを入力します。独立した例はファイル全体を置き換え、連結する例は本の指定に従ってください。

`lake build` は環境確認用の小さなモジュールをビルドします。全章の解答を一括検証するコマンドではありません。第3巻の配布例を含む検証は `python3 scripts/verify.py` で実行できます。
