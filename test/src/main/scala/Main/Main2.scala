package Main

import randomalg.RandomAlg._
import randomalg.Sampling._
import randomalg.ExportCode._
import output.ListToFile._

object Main2 {
  def main(args: Array[String]): Unit = {
    val t: BigInt = 10
    val s: BigInt = 1
    val ra = discrete_laplace_sampling(t,s)
    val list: List[Long] = test_time_ra(ra, 10, 10000) //10 is a seed for randomnumber generator
    print(list.map(_.toInt), "time.txt")
    val startTime = System.nanoTime()
    val result = Thread.sleep(1000)
    val endTime = System.nanoTime()
    val duration = endTime - startTime
    println(duration)
  }
}