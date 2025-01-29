package randomalg

import ExportCode._
import CoinStream._

object Sampling {
  def discrete_laplace_sampling(t: BigInt, s: BigInt): Randomized_Algorithm.random_alg[Int.int] = {
    Code_Generation_sampler.discrete_laplace_rat_ra(Nat.Nata(t), Nat.Nata(s))
  }
}