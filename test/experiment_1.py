import matplotlib.pyplot as plt
import numpy as np
from collections import Counter
import matplotlib

# 日本語フォントの設定
matplotlib.rcParams['font.family'] = 'MS Gothic'  # 'IPAexGothic' を使う
# フォントがインストールされていない場合は、'MS Gothic' なども試してみてください

# 出力されたテキストファイルを読み込む
file_name = "output.txt"

with open(file_name, "r") as file:
    # 各行を整数に変換してリストに格納
    my_list = [int(line.strip()) for line in file]

# 結果を表示
print("Scalaから渡されたリスト:", my_list)

# 要素の出現頻度をカウント
element_counts = Counter(my_list)

# 総数を計算
total_count = len(my_list)

# 正規化した頻度
normalized_counts = {key: count / total_count for key, count in element_counts.items()}

# サンプリング結果のヒストグラムを描画 
plt.bar(
    list(normalized_counts.keys()),  
    normalized_counts.values(),
    width=0.6,  # バーの幅
    alpha=0.6,
    color='red',  # 色は赤
    label="スケール1の離散ラプラス分布のサンプリングアルゴリズムの頻度分布(10000回)",
)

# 元の分布の確率を計算する関数
def original_distribution(z):
    return (np.exp(1) - 1) / (np.exp(1) + 1) * np.exp(-abs(z))

# サンプリング結果の範囲を決める
z_values = np.array(list(normalized_counts.keys()))

# 元の分布の確率を計算
original_probs = [original_distribution(z) for z in z_values]

# 元の分布のヒストグラムを描画 
plt.bar(
    z_values,  # x座標をそのまま使用
    original_probs,
    width=0.6,  # バーの幅
    alpha=0.6,
    color='blue',  # 色は青
    label="スケール1の離散ラプラス分布の確率密度関数",
)

# タイトルとラベルの設定
plt.xlabel('値')
plt.ylabel('確率密度')
plt.title('スケール1の離散ラプラス分布の密度関数とサンプリング結果の比較')

# 凡例を追加
plt.legend()

# グラフの表示
plt.show()
