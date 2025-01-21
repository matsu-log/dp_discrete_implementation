package Main

import randomalg.RandomAlg._
import randomalg.Sampling._
import randomalg.ExportCode._
import output.ListToFile._

object Main1 {
  def main(args: Array[String]): Unit = {
    val t: BigInt = 10
    val s: BigInt = 1
    val ra = discrete_laplace_sampling(t,s)
    val list: List[Int.int] = test_ra(ra, 10, 10000)
    val list1:List[Int] = list.map(x => x match {case Int.int_of_integer(bi) => bi.toInt})
    print(list1, "output10.txt")
  }
}