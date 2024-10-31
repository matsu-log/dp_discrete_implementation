object Lazy {
  final class Lazy[A] (f: Unit => A) {
    var evaluated = false;
    lazy val x: A = f(())

    def get() : A = {
      evaluated = true;
      return x
    }
  }

  def force[A] (x: Lazy[A]) : A = {
    return x.get()
  }

  def delay[A] (f: Unit => A) : Lazy[A] = {
    return new Lazy[A] (f)
  }

  def termify_lazy[Typerep, Term, A] (
    const: String => Typerep => Term,
    app: Term => Term => Term,
    abs: String => Typerep => Term => Term,
    unitT: Typerep,
    funT: Typerep => Typerep => Typerep,
    lazyT: Typerep => Typerep,
    term_of: A => Term,
    ty: Typerep,
    x: Lazy[A],
    dummy: Term) : Term = {
    if (x.evaluated)
      app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(abs("_")(unitT)(term_of(x.get())))
    else
      app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(const("Pure.dummy_pattern")(funT(unitT)(ty)))
  }
}

object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

} /* object Fun */

object Nat {

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a: nat) extends nat

def one_nat: nat = Suc(zero_nat())

def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
  case (Suc(m), n) => less_nat(m, n)
  case (zero_nat(), n) => true
}

def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
  case (m, Suc(n)) => less_eq_nat(m, n)
  case (n, zero_nat()) => false
}

def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (zero_nat(), n) => n
}

def equal_nat(x0: nat, x1: nat): Boolean = (x0, x1) match {
  case (zero_nat(), Suc(x2)) => false
  case (Suc(x2), zero_nat()) => false
  case (Suc(x2), Suc(y2)) => equal_nat(x2, y2)
  case (zero_nat(), zero_nat()) => true
}

def minus_nat(m: nat, n: nat): nat = (m, n) match {
  case (Suc(m), Suc(n)) => minus_nat(m, n)
  case (zero_nat(), n) => zero_nat()
  case (m, zero_nat()) => m
}

def times_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (zero_nat(), n) => zero_nat()
  case (Suc(m), n) => plus_nat(n, times_nat(m, n))
}

} /* object Nat */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def nat_of_num(x0: num): Nat.nat = x0 match {
  case Bit1(n) => {
                    val m = nat_of_num(n): Nat.nat;
                    Nat.Suc(Nat.plus_nat(m, m))
                  }
  case Bit0(n) => {
                    val m = nat_of_num(n): Nat.nat;
                    Nat.plus_nat(m, m)
                  }
  case One() => Nat.one_nat
}

} /* object Num */

object Optiona {

def bind[A, B](x0: Option[A], f: A => Option[B]): Option[B] = (x0, f) match {
  case (None, f) => None
  case (Some(x), f) => f(x)
}

} /* object Optiona */

object Coin_Space {

abstract sealed class coin_stream_lazy
final case class Coin_Lazy(a: Boolean, b: coin_stream) extends coin_stream_lazy

abstract sealed class coin_stream
final case class Lazy_coin_stream(a: Lazy.Lazy[coin_stream_lazy]) extends
  coin_stream

def unlazy_coin_stream(x0: coin_stream): Lazy.Lazy[coin_stream_lazy] = x0 match
  {
  case Lazy_coin_stream(uu) => uu
}

def chd(xa: coin_stream): Boolean =
  {
    val (Coin_Lazy(x2aa, _)) =
      Lazy.force[coin_stream_lazy](unlazy_coin_stream(xa)): coin_stream_lazy;
    x2aa
  }

def ctl(xa: coin_stream): coin_stream =
  {
    val (Coin_Lazy(_, x1aa)) =
      Lazy.force[coin_stream_lazy](unlazy_coin_stream(xa)): coin_stream_lazy;
    x1aa
  }

} /* object Coin_Space */

object Randomized_Algorithm_Internal {

def bind_rai[A, B](m: Coin_Space.coin_stream =>
                        Option[(A, Coin_Space.coin_stream)],
                    f: A => Coin_Space.coin_stream =>
                              Option[(B, Coin_Space.coin_stream)],
                    bs: Coin_Space.coin_stream):
      Option[(B, Coin_Space.coin_stream)]
  =
  Optiona.bind[(A, Coin_Space.coin_stream),
                (B, Coin_Space.coin_stream)](m(bs),
      ((a: (A, Coin_Space.coin_stream)) =>
        {
          val (aa, b) = a: ((A, Coin_Space.coin_stream));
          (f(aa))(b)
        }))

def coin_rai(bs: Coin_Space.coin_stream):
      Option[(Boolean, Coin_Space.coin_stream)]
  =
  Some[(Boolean,
         Coin_Space.coin_stream)]((Coin_Space.chd(bs), Coin_Space.ctl(bs)))

def return_rai[A](x: A, bs: Coin_Space.coin_stream):
      Option[(A, Coin_Space.coin_stream)]
  =
  Some[(A, Coin_Space.coin_stream)]((x, bs))

} /* object Randomized_Algorithm_Internal */

object Randomized_Algorithm {

abstract sealed class random_alg[A]
final case class Abs_random_alg[A](a: Coin_Space.coin_stream =>
Option[(A, Coin_Space.coin_stream)])
  extends random_alg[A]

def Rep_random_alg[A](x0: random_alg[A]):
      Coin_Space.coin_stream => Option[(A, Coin_Space.coin_stream)]
  =
  x0 match {
  case Abs_random_alg(x) => x
}

def bind_ra[B, A](xb: random_alg[B], xc: B => random_alg[A]): random_alg[A] =
  Abs_random_alg[A](((a: Coin_Space.coin_stream) =>
                      Randomized_Algorithm_Internal.bind_rai[B,
                      A](Rep_random_alg[B](xb),
                          Fun.comp[B, Coin_Space.coin_stream =>
Option[(A, Coin_Space.coin_stream)],
                                    B](Fun.comp[random_alg[A],
         Coin_Space.coin_stream => Option[(A, Coin_Space.coin_stream)],
         B](((aa: random_alg[A]) => Rep_random_alg[A](aa)), xc),
Fun.id[B]),
                          a)))

def coin_ra: random_alg[Boolean] =
  Abs_random_alg[Boolean](((a: Coin_Space.coin_stream) =>
                            Randomized_Algorithm_Internal.coin_rai(a)))

def return_ra[A](xa: A): random_alg[A] =
  Abs_random_alg[A](((a: Coin_Space.coin_stream) =>
                      Randomized_Algorithm_Internal.return_rai[A](xa, a)))

} /* object Randomized_Algorithm */

object Code_Test {

def fast_dice_roll_ra(n: Nat.nat, v: Nat.nat, c: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  (if (Nat.less_eq_nat(n, v))
    (if (Nat.less_nat(c, n)) Randomized_Algorithm.return_ra[Nat.nat](c)
      else fast_dice_roll_ra(n, Nat.minus_nat(v, n), Nat.minus_nat(c, n)))
    else Randomized_Algorithm.bind_ra[Boolean,
                                       Nat.nat](Randomized_Algorithm.coin_ra,
         ((b: Boolean) =>
           fast_dice_roll_ra(n, Nat.times_nat(Num.nat_of_num(Num.Bit0(Num.One())),
       v),
                              Nat.plus_nat(Nat.times_nat(Num.nat_of_num(Num.Bit0(Num.One())),
                  c),
    (if (b) Nat.one_nat else Nat.zero_nat()))))))

def fast_uniform_ra(n: Nat.nat): Randomized_Algorithm.random_alg[Nat.nat] =
  fast_dice_roll_ra(n, Nat.one_nat, Nat.zero_nat())

def bernoulli_rat_ra(n: Nat.nat, d: Nat.nat):
      Randomized_Algorithm.random_alg[Boolean]
  =
  (if (Nat.equal_nat(d, Nat.zero_nat()))
    Randomized_Algorithm.return_ra[Boolean](false)
    else Randomized_Algorithm.bind_ra[Nat.nat,
                                       Boolean](fast_uniform_ra(d),
         ((x: Nat.nat) =>
           Randomized_Algorithm.return_ra[Boolean](Nat.less_nat(x, n)))))

} /* object Code_Test */



//ここからは非生成コード
//Scastieでscala2.13.15で動作確認済み

import scala.util.Random


object Main {
  val zero = Nat.zero_nat()
  val one = Nat.one_nat
  val two = Nat.Suc(one)
  def main(args: Array[String]) = {
    val ra: Randomized_Algorithm.random_alg[Boolean] = Code_Test.bernoulli_rat_ra(one,two)
    val cs: Coin_Space.coin_stream = randomInfiniteCoinStream(170)
    val list = test_ra(ra, cs, 10)
    println(list mkString "\n")
    println("end")
    /*
    val result:Option[(Nat.nat, Coin_Space.coin_stream)] = ra2(cs)
    result match {
      case Some(tuple) => {
        tuple match {
          case (zero, cs2)=> println ("0")
          case _ => println("1")
        }
      }
      case None => println("None")
    }
    */
  }

  def test_ra[A](ra: Randomized_Algorithm.random_alg[A],cs: Coin_Space.coin_stream, n: scala.Int): List[A] = {
    val ra2 = Randomized_Algorithm.Rep_random_alg[A](ra)
    if (n<= 0) {
      Nil
    }
    else {
      ra2(cs) match {
        case Some(tuple) => tuple match{
          case (a,cs2) => {
            a :: test_ra(ra, cs2, n-1)
          }
        }
        case None => Nil
      }
    }
  }

  
  
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