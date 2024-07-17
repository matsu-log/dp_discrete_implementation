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
    x.evaluated match {
      case true => app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(abs("_")(unitT)(term_of(x.get())))
      case false => app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(const("Pure.dummy_pattern")(funT(unitT)(ty)))
    }
  }
}

object Bernoulli {

abstract sealed class num
final case class One() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

abstract sealed class int
final case class zero_inta() extends int
final case class Pos(a : num) extends int
final case class Neg(a : num) extends int

def one_inta : int = Pos(One())

trait one[A] {
  val `Bernoulli.one` : A
}
def one[A](implicit A: one[A]) : A = A.`Bernoulli.one`
object one {
  implicit def `Bernoulli.one_int` : one[int] = new one[int] {
    val `Bernoulli.one` = one_inta
  }
}

trait zero[A] {
  val `Bernoulli.zero` : A
}
def zero[A](implicit A: zero[A]) : A = A.`Bernoulli.zero`
object zero {
  implicit def `Bernoulli.zero_int` : zero[int] = new zero[int] {
    val `Bernoulli.zero` = zero_inta()
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def `Bernoulli.zero_neq_one_int` : zero_neq_one[int] = new
    zero_neq_one[int] {
    val `Bernoulli.zero` = zero_inta()
    val `Bernoulli.one` = one_inta
  }
}

abstract sealed class rat
final case class Frct(a : (int, int)) extends rat

abstract sealed class real
final case class Ratreal(a : rat) extends real

abstract sealed class coin_stream_lazy
final case class Coin_Lazy(a : Boolean, b : coin_stream) extends
  coin_stream_lazy

abstract sealed class coin_stream
final case class Lazy_coin_stream(a : Lazy.Lazy[coin_stream_lazy]) extends
  coin_stream

abstract sealed class random_alg[A]
final case class Abs_random_alg[A](a : coin_stream => Option[(A, coin_stream)])
  extends random_alg[A]

def id[A] : A => A = ((x : A) => x)

def dup(x0 : int) : int = x0 match {
  case Neg(n) => Neg(Bit0(n))
  case Pos(n) => Pos(Bit0(n))
  case zero_inta() => zero_inta()
}

def uminus_int(x0 : int) : int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case zero_inta() => zero_inta()
}

def plus_num(x0 : num, x1 : num) : num = (x0, x1) match {
  case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
  case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
  case (Bit1(m), One()) => Bit0(plus_num(m, One()))
  case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
  case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
  case (Bit0(m), One()) => Bit1(m)
  case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
  case (One(), Bit0(n)) => Bit1(n)
  case (One(), One()) => Bit0(One())
}

def BitM(x0 : num) : num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(BitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

def minus_int(k : int, l : int) : int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (zero_inta(), l) => uminus_int(l)
  case (k, zero_inta()) => k
}

def plus_int(k : int, l : int) : int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(plus_num(m, n))
  case (zero_inta(), l) => l
  case (k, zero_inta()) => k
}

def sub(x0 : num, x1 : num) : int = (x0, x1) match {
  case (Bit0(m), Bit1(n)) => minus_int(dup(sub(m, n)), one_inta)
  case (Bit1(m), Bit0(n)) => plus_int(dup(sub(m, n)), one_inta)
  case (Bit1(m), Bit1(n)) => dup(sub(m, n))
  case (Bit0(m), Bit0(n)) => dup(sub(m, n))
  case (One(), Bit1(n)) => Neg(Bit0(n))
  case (One(), Bit0(n)) => Neg(BitM(n))
  case (Bit1(m), One()) => Pos(Bit0(m))
  case (Bit0(m), One()) => Pos(BitM(m))
  case (One(), One()) => zero_inta()
}

def comp[A, B, C](f : A => B, g : C => A) : C => B = ((x : C) => f(g(x)))

def of_int(a : int) : rat = Frct((a, one_inta))

def bind[A, B](x0 : Option[A], f : A => Option[B]) : Option[B] = (x0, f) match {
  case (None, f) => None
  case (Some(x), f) => f(x)
}

def times_num(m : num, n : num) : num = (m, n) match {
  case (Bit1(m), Bit1(n)) =>
    Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
  case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
  case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
  case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
  case (One(), n) => n
  case (m, One()) => m
}

def times_int(k : int, l : int) : int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(times_num(m, n))
  case (zero_inta(), l) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

def less_num(m : num, x1 : num) : Boolean = (m, x1) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_num(m, n)
  case (One(), Bit1(n)) => true
  case (One(), Bit0(n)) => true
  case (m, One()) => false
}

def less_eq_num(x0 : num, n : num) : Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_eq_int(x0 : int, x1 : int) : Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_eq_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => true
}

def less_int(x0 : int, x1 : int) : Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => false
}

def abs_int(i : int) : int =
  (less_int(i, zero_inta()) match { case true => uminus_int(i) case false => i
    })

def divmod_step_int(l : int, qr : (int, int)) : (int, int) =
  {
    val (q, r) = qr : ((int, int));
    (less_eq_int(abs_int(l), abs_int(r)) match {
      case true => (plus_int(times_int(Pos(Bit0(One())), q), one_inta),
                     minus_int(r, l))
      case false => (times_int(Pos(Bit0(One())), q), r) })
  }

def divmod_int(m : num, x1 : num) : (int, int) = (m, x1) match {
  case (Bit1(m), Bit1(n)) =>
    (less_num(m, n) match { case true => (zero_inta(), Pos(Bit1(m)))
      case false => divmod_step_int(Pos(Bit1(n)),
                                     divmod_int(Bit1(m), Bit0(Bit1(n))))
      })
  case (Bit0(m), Bit1(n)) =>
    (less_eq_num(m, n) match { case true => (zero_inta(), Pos(Bit0(m)))
      case false => divmod_step_int(Pos(Bit1(n)),
                                     divmod_int(Bit0(m), Bit0(Bit1(n))))
      })
  case (Bit1(m), Bit0(n)) =>
    {
      val (q, r) = divmod_int(m, n) : ((int, int));
      (q, plus_int(times_int(Pos(Bit0(One())), r), one_inta))
    }
  case (Bit0(m), Bit0(n)) => {
                               val (q, r) = divmod_int(m, n) : ((int, int));
                               (q, times_int(Pos(Bit0(One())), r))
                             }
  case (One(), Bit1(n)) => (zero_inta(), Pos(One()))
  case (One(), Bit0(n)) => (zero_inta(), Pos(One()))
  case (m, One()) => (Pos(m), zero_inta())
}

def fst[A, B](x0 : (A, B)) : A = x0 match {
  case (x1, x2) => x1
}

def of_bool[A : zero_neq_one](x0 : Boolean) : A = x0 match {
  case true => one[A]
  case false => zero[A]
}

def equal_num(x0 : num, x1 : num) : Boolean = (x0, x1) match {
  case (Bit0(x2), Bit1(x3)) => false
  case (Bit1(x3), Bit0(x2)) => false
  case (One(), Bit1(x3)) => false
  case (Bit1(x3), One()) => false
  case (One(), Bit0(x2)) => false
  case (Bit0(x2), One()) => false
  case (Bit1(x3), Bit1(y3)) => equal_num(x3, y3)
  case (Bit0(x2), Bit0(y2)) => equal_num(x2, y2)
  case (One(), One()) => true
}

def equal_int(x0 : int, x1 : int) : Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_inta()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => equal_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => false
  case (zero_inta(), zero_inta()) => true
}

def adjust_div(x0 : (int, int)) : int = x0 match {
  case (q, r) => plus_int(q, of_bool[int](! (equal_int(r, zero_inta()))))
}

def divide_int(k : int, ka : int) : int = (k, ka) match {
  case (Neg(m), Neg(n)) => fst[int, int](divmod_int(m, n))
  case (Pos(m), Neg(n)) => uminus_int(adjust_div(divmod_int(m, n)))
  case (Neg(m), Pos(n)) => uminus_int(adjust_div(divmod_int(m, n)))
  case (Pos(m), Pos(n)) => fst[int, int](divmod_int(m, n))
  case (k, Neg(One())) => uminus_int(k)
  case (k, Pos(One())) => k
  case (zero_inta(), k) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

def snd[A, B](x0 : (A, B)) : B = x0 match {
  case (x1, x2) => x2
}

def adjust_mod(l : num, r : int) : int =
  (equal_int(r, zero_inta()) match { case true => zero_inta()
    case false => minus_int(Pos(l), r) })

def modulo_int(k : int, ka : int) : int = (k, ka) match {
  case (Neg(m), Neg(n)) => uminus_int(snd[int, int](divmod_int(m, n)))
  case (Pos(m), Neg(n)) =>
    uminus_int(adjust_mod(n, snd[int, int](divmod_int(m, n))))
  case (Neg(m), Pos(n)) => adjust_mod(n, snd[int, int](divmod_int(m, n)))
  case (Pos(m), Pos(n)) => snd[int, int](divmod_int(m, n))
  case (k, Neg(One())) => zero_inta()
  case (k, Pos(One())) => zero_inta()
  case (zero_inta(), k) => zero_inta()
  case (k, zero_inta()) => k
}

def gcd_int(k : int, l : int) : int =
  abs_int((equal_int(l, zero_inta()) match { case true => k
            case false => gcd_int(l, modulo_int(abs_int(k), abs_int(l))) }))

def normalize(p : (int, int)) : (int, int) =
  (less_int(zero_inta(), snd[int, int](p)) match {
    case true => {
                   val a = gcd_int(fst[int, int](p), snd[int, int](p)) : int;
                   (divide_int(fst[int, int](p), a),
                     divide_int(snd[int, int](p), a))
                 }
    case false => (equal_int(snd[int, int](p), zero_inta()) match {
                    case true => (zero_inta(), one_inta)
                    case false => {
                                    val a =
                                      uminus_int(gcd_int(fst[int, int](p),
                  snd[int, int](p))) : int;
                                    (divide_int(fst[int, int](p), a),
                                      divide_int(snd[int, int](p), a))
                                  }
                    })
    })

def quotient_of(x0 : rat) : (int, int) = x0 match {
  case Frct(x) => x
}

def one_rat : rat = Frct((one_inta, one_inta))

def less_rat(p : rat, q : rat) : Boolean =
  {
    val (a, c) = quotient_of(p) : ((int, int))
    val (b, d) = quotient_of(q) : ((int, int));
    less_int(times_int(a, d), times_int(c, b))
  }

def unlazy_coin_stream(x0 : coin_stream) : Lazy.Lazy[coin_stream_lazy] = x0
  match {
  case Lazy_coin_stream(uu) => uu
}

def chd(xa : coin_stream) : Boolean =
  {
    val (Coin_Lazy(x2aa, _)) =
      Lazy.force[coin_stream_lazy](unlazy_coin_stream(xa)) : coin_stream_lazy;
    x2aa
  }

def ctl(xa : coin_stream) : coin_stream =
  {
    val (Coin_Lazy(_, x1aa)) =
      Lazy.force[coin_stream_lazy](unlazy_coin_stream(xa)) : coin_stream_lazy;
    x1aa
  }

def one_real : real = Ratreal(one_rat)

def Rep_random_alg[A](x0 : random_alg[A]) : coin_stream =>
      Option[(A, coin_stream)]
  =
  x0 match {
  case Abs_random_alg(x) => x
}

def bind_rai[A, B](m : coin_stream => Option[(A, coin_stream)],
                    f : A => coin_stream => Option[(B, coin_stream)],
                    bs : coin_stream) : Option[(B, coin_stream)]
  =
  bind[(A, coin_stream),
        (B, coin_stream)](m(bs),
                           ((a : (A, coin_stream)) =>
                             {
                               val (aa, b) = a : ((A, coin_stream));
                               (f(aa))(b)
                             }))

def bind_ra[B, A](xb : random_alg[B], xc : B => random_alg[A]) : random_alg[A] =
  Abs_random_alg[A](((a : coin_stream) =>
                      bind_rai[B, A](Rep_random_alg[B](xb),
                                      comp[B,
    coin_stream => Option[(A, coin_stream)],
    B](comp[random_alg[A], coin_stream => Option[(A, coin_stream)],
             B](((aa : random_alg[A]) => Rep_random_alg[A](aa)), xc),
        id[B]),
                                      a)))

def coin_rai(bs : coin_stream) : Option[(Boolean, coin_stream)] =
  Some[(Boolean, coin_stream)]((chd(bs), ctl(bs)))

def coin_ra : random_alg[Boolean] =
  Abs_random_alg[Boolean](((a : coin_stream) => coin_rai(a)))

def minus_rat(p : rat, q : rat) : rat =
  Frct({
         val (a, c) = quotient_of(p) : ((int, int))
         val (b, d) = quotient_of(q) : ((int, int));
         normalize((minus_int(times_int(a, d), times_int(b, c)),
                     times_int(c, d)))
       })

def less_eq_rat(p : rat, q : rat) : Boolean =
  {
    val (a, c) = quotient_of(p) : ((int, int))
    val (b, d) = quotient_of(q) : ((int, int));
    less_eq_int(times_int(a, d), times_int(c, b))
  }

def times_rat(p : rat, q : rat) : rat =
  Frct({
         val (a, c) = quotient_of(p) : ((int, int))
         val (b, d) = quotient_of(q) : ((int, int));
         normalize((times_int(a, b), times_int(c, d)))
       })

def less_real(x0 : real, x1 : real) : Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_rat(x, y)
}

def return_rai[A](x : A, bs : coin_stream) : Option[(A, coin_stream)] =
  Some[(A, coin_stream)]((x, bs))

def return_ra[A](xa : A) : random_alg[A] =
  Abs_random_alg[A](((a : coin_stream) => return_rai[A](xa, a)))

def divide_rat(p : rat, q : rat) : rat =
  Frct({
         val (a, c) = quotient_of(p) : ((int, int))
         val (b, d) = quotient_of(q) : ((int, int));
         normalize((times_int(a, d), times_int(c, b)))
       })

def minus_real(x0 : real, x1 : real) : real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(minus_rat(x, y))
}

def less_eq_real(x0 : real, x1 : real) : Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_eq_rat(x, y)
}

def times_real(x0 : real, x1 : real) : real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(times_rat(x, y))
}

def divide_real(x0 : real, x1 : real) : real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(divide_rat(x, y))
}

def bernoulli_ra(p : real) : random_alg[Boolean] =
  bind_ra[Boolean,
           Boolean](coin_ra,
                     ((b : Boolean) =>
                       (b match {
                         case true => return_ra[Boolean](less_eq_real(divide_real(one_real,
   Ratreal(of_int(Pos(Bit0(One()))))),
                               p))
                         case false => (less_real(p,
           divide_real(one_real, Ratreal(of_int(Pos(Bit0(One())))))) match {
 case true => bernoulli_ra(times_real(Ratreal(of_int(Pos(Bit0(One())))), p))
 case false => bernoulli_ra(minus_real(times_real(Ratreal(of_int(Pos(Bit0(One())))),
           p),
one_real))
 })
                         })))

} /* object Bernoulli */

object TestCode_Bernoulli {
  
  import Bernoulli._
  val zero = zero_nat()
  def nat_n(n: Int): nat = {
    if (n==0) {zero}
    else Suc(nat_n(n-1))
  }
  def n_nat(n:nat): Int = {
    n match {
      case zero_nat() => 0
      case Suc(m) => 1 + (n_nat(m))
    }
  }

  
  
  import scala.util.Random

  // 乱数生成器を初期化
  val rand = new Random()

  // coin_stream_lazy のインスタンスを生成する関数
  def generateCoinStreamLazy(): Lazy.Lazy[coin_stream_lazy] = {
    Lazy.delay( _ => {
      val coin = rand.nextBoolean() // ランダムなBoolean値を生成
      val nextStream = generateCoinStream() // 再帰的に次の coin_stream を生成
      Coin_Lazy(coin, nextStream)
    })
  }

  // coin_stream のインスタンスを生成する関数
  def generateCoinStream(): coin_stream = {
    Lazy_coin_stream(generateCoinStreamLazy())
  }
  
  var cs = generateCoinStream()

  def m(): Unit = {
  val Abs_random_alg(f) = bernoulli_ra(p)
  val x = f(cs)
  x match {
    case Some((result, cs1)) => {
      println(n_nat(result))
      cs = cs1
    }
    case None => println("None")
  }
  }
}
