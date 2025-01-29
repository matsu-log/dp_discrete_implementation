package randomalg

import ExportCode._
import CoinStream._

object Mechanism {
  def discrete_laplace_mechanism(f : (List[A]) => Int.int, delta : BigInt,
                                      epsilon1 : BigInt, epsilon2 : BigInt,
                                      x : List[A]): Randomized_Algorithm.random_alg[Int.int] = {
    Code_Generation_mechanism.discrete_laplace_mechanism_ra(f, Nat.Nata(delta), Nat.Nata(epsilon1),Nat.Nata(epsilon2),x)
  }
}