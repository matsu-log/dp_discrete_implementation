package randomalg

import ExportCode._
import scala.util.Random

object CoinStream{
   // ランダムな無限コイン列を生成する関数
  def randomInfiniteCoinStream(seed: Long): Coin_Space.coin_stream = {
    val random = new Random(seed)

    // 無限にコインを生成
    def generateCoinStream: Coin_Space.coin_stream_lazy = {
      // 1つのコインを生成
      val coinValue: Boolean = random.nextBoolean()

      // 次のコインのストリームを遅延評価で生成
      val nextStream: Lazy.Lazy[Coin_Space.coin_stream_lazy] = Lazy.delay(Unit => generateCoinStream)

      // 現在のコインと次のストリームを組み合わせる
      Coin_Space.Coin_Lazy(coinValue, Coin_Space.Lazy_coin_stream(nextStream))
    }

  // 初期コイン列を返す
  Coin_Space.Lazy_coin_stream(Lazy.delay(Unit => generateCoinStream))
  }
}