package randomalg

import ExportCode._
import CoinStream._


object RandomAlg {

  //seedによる乱数列の下で、n回確率的アルゴリズムraを実行し、その結果をリストにして返す
  def test_ra[A](ra: Randomized_Algorithm.random_alg[A], seed: Long , n: scala.Int): List[A] = {

    def test_ra_sub[A](ra: Randomized_Algorithm.random_alg[A], cs: Coin_Space.coin_stream, n: scala.Int): List[A] = {
      val ra2 = Randomized_Algorithm.Rep_random_alg[A](ra)
      if (n<= 0) {
        Nil
      }
      else {
        ra2(cs) match {
          case Some(tuple) => tuple match{
            case (a,cs2) => {
            a :: test_ra_sub(ra, cs2, n-1)
            }
          }
          case None => Nil
        }
      }
    }
    test_ra_sub(ra, randomInfiniteCoinStream(seed),n)
  }
  def test_time_ra[A](ra: Randomized_Algorithm.random_alg[A], seed: Long , n: scala.Int): List[Long] = {

    def test_time_ra_sub[A](ra: Randomized_Algorithm.random_alg[A], cs: Coin_Space.coin_stream, n: scala.Int): List[Long] = {
      val ra2 = Randomized_Algorithm.Rep_random_alg[A](ra)
      if (n<= 0) {
        Nil
      }
      else {
        val startTime = System.nanoTime()
        val result = ra2(cs)
        val endTime = System.nanoTime()
        val duration = endTime - startTime
        result match {
          case Some(tuple) => tuple match {
            case (a,cs2) => {
              duration :: test_time_ra_sub(ra,cs2,n-1)
            }
          }
          case None => Nil
        }
      }
    }
    test_time_ra_sub(ra, randomInfiniteCoinStream(seed),n)
  }
}