## 概要
Isabelleで証明されたDP-アルゴリズムの実行可能なコード生成が目的

### 各ファイルの説明
* Bernoulli_rat.thy
  * 0以上の有理数n/dをパラメータとするベルヌーイ分布のサンプリングアルゴリズム
* Bernoulli_exp_minus_rat.thy
  * 0以上の有理数n/dを入力とし、exp(-n/d)をパラメータとするベルヌーイ分布のサンプリングアルゴリズム
* Discrete_Lplace_rat.thy
  *  0より大きい有理数t/sを入力とし、スケールがt/sの離散ラプラス分布のサンプリングアルゴリズム
 
### 利用する(予定の)AFP
* HOL.Probability
  * IsabelleのHOL上で定義された確率論関係のライブラリ
* Probabilistic_While_Loop
  * 命令型で書かれたLoopを含む確率的アルゴリズムを扱うためのAFP
* Executed_Randomized_Algorithm
  * Isabelleで実行可能な確率的アルゴリズムを生成するためのAFP
