## 概要
Isabelleで証明されたDP-アルゴリズムの実行可能なコード生成が目的

### 各ファイルの説明
samplerフォルダ:サンプリングアルゴリズムの形式化と検証をまとめたフォルダ
* Bernoulli_rat.thy
  * 0以上の有理数n/dをパラメータとするベルヌーイ分布のサンプリングアルゴリズム
* Bernoulli_exp_minus_real.thy
  * 0以上の実数pを入力とし、exp(-p)をパラメータとするベルヌーイ分布のサンプリングアルゴリズム
* Bernoulli_exp_minus_rat.thy
  * 0以上の有理数pを入力とし、exp(-p)をパラメータとするベルヌーイ分布のサンプリングアルゴリズム
* Discrete_Lplace_rat.thy
  *  0より大きい有理数t/sを入力とし、スケールがt/sの離散ラプラス分布のサンプリングアルゴリズム
testフォルダ:実験に用いたScalaとPythonのコードを含むフォルダ

 
### 利用したAFP
* Probabilistic_While_Loop
  * 命令型で書かれたLoopを含む確率的アルゴリズムを扱うためのAFP
* Executed_Randomized_Algorithm
  * 実行可能な確率的アルゴリズムのコードを生成するためのAFP
