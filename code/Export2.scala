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

object Product_Type {

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def equal_bool(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

} /* object Product_Type */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Num {

trait numeral[A] extends Groups.one[A] with Groups.semigroup_add[A] {
}
object numeral {
  implicit def `Real.numeral_real`: numeral[Real.real] = new numeral[Real.real]
    {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.one` = Real.one_reala
  }
  implicit def `Nat.numeral_nat`: numeral[Nat.nat] = new numeral[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.one` = Nat.one_nata
  }
  implicit def `Int.numeral_int`: numeral[Int.int] = new numeral[Int.int] {
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
    val `Groups.one` = Int.one_inta
  }
}

trait semiring_numeral[A]
  extends Groups.monoid_mult[A] with numeral[A] with Rings.semiring[A] {
}
object semiring_numeral {
  implicit def `Real.semiring_numeral_real`: semiring_numeral[Real.real] = new
    semiring_numeral[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
  implicit def `Nat.semiring_numeral_nat`: semiring_numeral[Nat.nat] = new
    semiring_numeral[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
  implicit def `Int.semiring_numeral_int`: semiring_numeral[Int.int] = new
    semiring_numeral[Int.int] {
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
    val `Groups.one` = Int.one_inta
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
  }
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def BitM(x0: num): num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(BitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

def nat_of_num(x0: num): Nat.nat = x0 match {
  case Bit1(n) => {
                    val m = nat_of_num(n): Nat.nat;
                    Nat.Suc(Nat.plus_nata(m, m))
                  }
  case Bit0(n) => {
                    val m = nat_of_num(n): Nat.nat;
                    Nat.plus_nata(m, m)
                  }
  case One() => Nat.one_nata
}

def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_num(m: num, x1: num): Boolean = (m, x1) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_num(m, n)
  case (One(), Bit1(n)) => true
  case (One(), Bit0(n)) => true
  case (m, One()) => false
}

def plus_num(x0: num, x1: num): num = (x0, x1) match {
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

def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
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

def times_num(m: num, n: num): num = (m, n) match {
  case (Bit1(m), Bit1(n)) =>
    Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
  case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
  case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
  case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
  case (One(), n) => n
  case (m, One()) => m
}

} /* object Num */

object Nat {

abstract sealed class nat
final case class zero_nata() extends nat
final case class Suc(a: nat) extends nat

def equal_nata(x0: nat, x1: nat): Boolean = (x0, x1) match {
  case (zero_nata(), Suc(x2)) => false
  case (Suc(x2), zero_nata()) => false
  case (Suc(x2), Suc(y2)) => equal_nata(x2, y2)
  case (zero_nata(), zero_nata()) => true
}

def plus_nata(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nata(m, Suc(n))
  case (zero_nata(), n) => n
}

def times_nata(x0: nat, n: nat): nat = (x0, n) match {
  case (zero_nata(), n) => zero_nata()
  case (Suc(m), n) => plus_nata(n, times_nata(m, n))
}

def one_nata: nat = Suc(zero_nata())

def minus_nata(m: nat, n: nat): nat = (m, n) match {
  case (Suc(m), Suc(n)) => minus_nata(m, n)
  case (zero_nata(), n) => zero_nata()
  case (m, zero_nata()) => m
}

def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
  case (Suc(m), n) => less_nat(m, n)
  case (zero_nata(), n) => true
}

def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
  case (m, Suc(n)) => less_eq_nat(m, n)
  case (n, zero_nata()) => false
}

def of_nat_aux[A : Rings.semiring_1](inc: A => A, x1: nat, i: A): A =
  (inc, x1, i) match {
  case (inc, zero_nata(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : Rings.semiring_1](n: nat): A =
  of_nat_aux[A](((i: A) => Groups.plus[A](i, Groups.one[A])), n, Groups.zero[A])

} /* object Nat */

object Power {

trait power[A] extends Groups.one[A] with Groups.times[A] {
}
object power {
  implicit def `Real.power_real`: power[Real.real] = new power[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.one` = Real.one_reala
  }
  implicit def `Nat.power_nat`: power[Nat.nat] = new power[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.one` = Nat.one_nata
  }
  implicit def `Int.power_int`: power[Int.int] = new power[Int.int] {
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
    val `Groups.one` = Int.one_inta
  }
}

} /* object Power */

object Groups {

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)
object plus {
  implicit def `Real.plus_real`: plus[Real.real] = new plus[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.plus_nat`: plus[Nat.nat] = new plus[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.plus_int`: plus[Int.int] = new plus[Int.int] {
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `Real.semigroup_add_real`: semigroup_add[Real.real] = new
    semigroup_add[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.semigroup_add_nat`: semigroup_add[Nat.nat] = new
    semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.semigroup_add_int`: semigroup_add[Int.int] = new
    semigroup_add[Int.int] {
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`
object zero {
  implicit def `Real.zero_real`: zero[Real.real] = new zero[Real.real] {
    val `Groups.zero` = Real.zero_reala
  }
  implicit def `Nat.zero_nat`: zero[Nat.nat] = new zero[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
  }
  implicit def `Int.zero_int`: zero[Int.int] = new zero[Int.int] {
    val `Groups.zero` = Int.zero_inta()
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `Real.monoid_add_real`: monoid_add[Real.real] = new
    monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.monoid_add_nat`: monoid_add[Nat.nat] = new
    monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.monoid_add_int`: monoid_add[Int.int] = new
    monoid_add[Int.int] {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait times[A] {
  val `Groups.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`Groups.times`(a, b)
object times {
  implicit def `Real.times_real`: times[Real.real] = new times[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
  implicit def `Nat.times_nat`: times[Nat.nat] = new times[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
  implicit def `Int.times_int`: times[Int.int] = new times[Int.int] {
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult {
  implicit def `Real.semigroup_mult_real`: semigroup_mult[Real.real] = new
    semigroup_mult[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
  implicit def `Nat.semigroup_mult_nat`: semigroup_mult[Nat.nat] = new
    semigroup_mult[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
  implicit def `Int.semigroup_mult_int`: semigroup_mult[Int.int] = new
    semigroup_mult[Int.int] {
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with Power.power[A] {
}
object monoid_mult {
  implicit def `Real.monoid_mult_real`: monoid_mult[Real.real] = new
    monoid_mult[Real.real] {
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
  implicit def `Nat.monoid_mult_nat`: monoid_mult[Nat.nat] = new
    monoid_mult[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
  implicit def `Int.monoid_mult_int`: monoid_mult[Int.int] = new
    monoid_mult[Int.int] {
    val `Groups.one` = Int.one_inta
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def `Real.ab_semigroup_add_real`: ab_semigroup_add[Real.real] = new
    ab_semigroup_add[Real.real] {
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.ab_semigroup_add_nat`: ab_semigroup_add[Nat.nat] = new
    ab_semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.ab_semigroup_add_int`: ab_semigroup_add[Int.int] = new
    ab_semigroup_add[Int.int] {
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def `Real.comm_monoid_add_real`: comm_monoid_add[Real.real] = new
    comm_monoid_add[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.comm_monoid_add_nat`: comm_monoid_add[Nat.nat] = new
    comm_monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.comm_monoid_add_int`: comm_monoid_add[Int.int] = new
    comm_monoid_add[Int.int] {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait ab_semigroup_mult[A] extends semigroup_mult[A] {
}
object ab_semigroup_mult {
  implicit def `Nat.ab_semigroup_mult_nat`: ab_semigroup_mult[Nat.nat] = new
    ab_semigroup_mult[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait comm_monoid_mult[A]
  extends ab_semigroup_mult[A] with monoid_mult[A] with Rings.dvd[A] {
}
object comm_monoid_mult {
  implicit def `Nat.comm_monoid_mult_nat`: comm_monoid_mult[Nat.nat] = new
    comm_monoid_mult[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait cancel_semigroup_add[A] extends semigroup_add[A] {
}
object cancel_semigroup_add {
  implicit def `Nat.cancel_semigroup_add_nat`: cancel_semigroup_add[Nat.nat] =
    new cancel_semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait minus[A] {
  val `Groups.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`Groups.minus`(a, b)
object minus {
  implicit def `Nat.minus_nat`: minus[Nat.nat] = new minus[Nat.nat] {
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
  }
}

trait cancel_ab_semigroup_add[A]
  extends ab_semigroup_add[A] with cancel_semigroup_add[A] with minus[A] {
}
object cancel_ab_semigroup_add {
  implicit def
    `Nat.cancel_ab_semigroup_add_nat`: cancel_ab_semigroup_add[Nat.nat] = new
    cancel_ab_semigroup_add[Nat.nat] {
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait cancel_comm_monoid_add[A]
  extends cancel_ab_semigroup_add[A] with comm_monoid_add[A] {
}
object cancel_comm_monoid_add {
  implicit def `Nat.cancel_comm_monoid_add_nat`: cancel_comm_monoid_add[Nat.nat]
    = new cancel_comm_monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait one[A] {
  val `Groups.one`: A
}
def one[A](implicit A: one[A]): A = A.`Groups.one`
object one {
  implicit def `Real.one_real`: one[Real.real] = new one[Real.real] {
    val `Groups.one` = Real.one_reala
  }
  implicit def `Nat.one_nat`: one[Nat.nat] = new one[Nat.nat] {
    val `Groups.one` = Nat.one_nata
  }
  implicit def `Int.one_int`: one[Int.int] = new one[Int.int] {
    val `Groups.one` = Int.one_inta
  }
}

} /* object Groups */

object Rings {

trait dvd[A] extends Groups.times[A] {
}
object dvd {
  implicit def `Nat.dvd_nat`: dvd[Nat.nat] = new dvd[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait divide[A] {
  val `Rings.divide`: (A, A) => A
}
def divide[A](a: A, b: A)(implicit A: divide[A]): A = A.`Rings.divide`(a, b)
object divide {
  implicit def `Euclidean_Rings.divide_nat`: divide[Nat.nat] = new
    divide[Nat.nat] {
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
  }
}

trait modulo[A] extends divide[A] with dvd[A] {
  val `Rings.modulo`: (A, A) => A
}
def modulo[A](a: A, b: A)(implicit A: modulo[A]): A = A.`Rings.modulo`(a, b)
object modulo {
  implicit def `Euclidean_Rings.modulo_nat`: modulo[Nat.nat] = new
    modulo[Nat.nat] {
    val `Rings.modulo` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.modulo_nata(a, b)
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
  }
}

trait mult_zero[A] extends Groups.times[A] with Groups.zero[A] {
}
object mult_zero {
  implicit def `Real.mult_zero_real`: mult_zero[Real.real] = new
    mult_zero[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
  }
  implicit def `Nat.mult_zero_nat`: mult_zero[Nat.nat] = new mult_zero[Nat.nat]
    {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
  implicit def `Int.mult_zero_int`: mult_zero[Int.int] = new mult_zero[Int.int]
    {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
  }
}

trait semiring[A]
  extends Groups.ab_semigroup_add[A] with Groups.semigroup_mult[A] {
}
object semiring {
  implicit def `Real.semiring_real`: semiring[Real.real] = new
    semiring[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.semiring_nat`: semiring[Nat.nat] = new semiring[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.semiring_int`: semiring[Int.int] = new semiring[Int.int] {
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait semiring_0[A]
  extends Groups.comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0 {
  implicit def `Real.semiring_0_real`: semiring_0[Real.real] = new
    semiring_0[Real.real] {
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.zero` = Real.zero_reala
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.semiring_0_nat`: semiring_0[Nat.nat] = new
    semiring_0[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.semiring_0_int`: semiring_0[Int.int] = new
    semiring_0[Int.int] {
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
    val `Groups.zero` = Int.zero_inta()
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait semiring_0_cancel[A]
  extends Groups.cancel_comm_monoid_add[A] with semiring_0[A] {
}
object semiring_0_cancel {
  implicit def `Nat.semiring_0_cancel_nat`: semiring_0_cancel[Nat.nat] = new
    semiring_0_cancel[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait comm_semiring[A] extends Groups.ab_semigroup_mult[A] with semiring[A] {
}
object comm_semiring {
  implicit def `Nat.comm_semiring_nat`: comm_semiring[Nat.nat] = new
    comm_semiring[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait comm_semiring_0[A] extends comm_semiring[A] with semiring_0[A] {
}
object comm_semiring_0 {
  implicit def `Nat.comm_semiring_0_nat`: comm_semiring_0[Nat.nat] = new
    comm_semiring_0[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait comm_semiring_0_cancel[A]
  extends comm_semiring_0[A] with semiring_0_cancel[A] {
}
object comm_semiring_0_cancel {
  implicit def `Nat.comm_semiring_0_cancel_nat`: comm_semiring_0_cancel[Nat.nat]
    = new comm_semiring_0_cancel[Nat.nat] {
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait zero_neq_one[A] extends Groups.one[A] with Groups.zero[A] {
}
object zero_neq_one {
  implicit def `Real.zero_neq_one_real`: zero_neq_one[Real.real] = new
    zero_neq_one[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.one` = Real.one_reala
  }
  implicit def `Nat.zero_neq_one_nat`: zero_neq_one[Nat.nat] = new
    zero_neq_one[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.one` = Nat.one_nata
  }
  implicit def `Int.zero_neq_one_int`: zero_neq_one[Int.int] = new
    zero_neq_one[Int.int] {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.one` = Int.one_inta
  }
}

trait semiring_1[A]
  extends Num.semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1 {
  implicit def `Real.semiring_1_real`: semiring_1[Real.real] = new
    semiring_1[Real.real] {
    val `Groups.zero` = Real.zero_reala
    val `Groups.one` = Real.one_reala
    val `Groups.times` = (a: Real.real, b: Real.real) => Real.times_reala(a, b)
    val `Groups.plus` = (a: Real.real, b: Real.real) => Real.plus_reala(a, b)
  }
  implicit def `Nat.semiring_1_nat`: semiring_1[Nat.nat] = new
    semiring_1[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
  implicit def `Int.semiring_1_int`: semiring_1[Int.int] = new
    semiring_1[Int.int] {
    val `Groups.zero` = Int.zero_inta()
    val `Groups.one` = Int.one_inta
    val `Groups.times` = (a: Int.int, b: Int.int) => Int.times_inta(a, b)
    val `Groups.plus` = (a: Int.int, b: Int.int) => Int.plus_inta(a, b)
  }
}

trait semiring_1_cancel[A] extends semiring_0_cancel[A] with semiring_1[A] {
}
object semiring_1_cancel {
  implicit def `Nat.semiring_1_cancel_nat`: semiring_1_cancel[Nat.nat] = new
    semiring_1_cancel[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait comm_semiring_1[A]
  extends Groups.comm_monoid_mult[A] with comm_semiring_0[A] with semiring_1[A]
  {
}
object comm_semiring_1 {
  implicit def `Nat.comm_semiring_1_nat`: comm_semiring_1[Nat.nat] = new
    comm_semiring_1[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
  }
}

trait comm_semiring_1_cancel[A]
  extends comm_semiring_0_cancel[A] with comm_semiring_1[A] with
    semiring_1_cancel[A]
  {
}
object comm_semiring_1_cancel {
  implicit def `Nat.comm_semiring_1_cancel_nat`: comm_semiring_1_cancel[Nat.nat]
    = new comm_semiring_1_cancel[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semiring_no_zero_divisors[A] extends semiring_0[A] {
}
object semiring_no_zero_divisors {
  implicit def
    `Nat.semiring_no_zero_divisors_nat`: semiring_no_zero_divisors[Nat.nat] =
    new semiring_no_zero_divisors[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semiring_1_no_zero_divisors[A]
  extends semiring_1[A] with semiring_no_zero_divisors[A] {
}
object semiring_1_no_zero_divisors {
  implicit def
    `Nat.semiring_1_no_zero_divisors_nat`: semiring_1_no_zero_divisors[Nat.nat]
    = new semiring_1_no_zero_divisors[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semidom[A]
  extends comm_semiring_1_cancel[A] with semiring_1_no_zero_divisors[A] {
}
object semidom {
  implicit def `Nat.semidom_nat`: semidom[Nat.nat] = new semidom[Nat.nat] {
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semiring_no_zero_divisors_cancel[A] extends semiring_no_zero_divisors[A] {
}
object semiring_no_zero_divisors_cancel {
  implicit def
    `Euclidean_Rings.semiring_no_zero_divisors_cancel_nat`:
      semiring_no_zero_divisors_cancel[Nat.nat]
    = new semiring_no_zero_divisors_cancel[Nat.nat] {
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semidom_divide[A]
  extends divide[A] with semidom[A] with semiring_no_zero_divisors_cancel[A] {
}
object semidom_divide {
  implicit def `Euclidean_Rings.semidom_divide_nat`: semidom_divide[Nat.nat] =
    new semidom_divide[Nat.nat] {
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
  }
}

trait semiring_modulo[A] extends comm_semiring_1_cancel[A] with modulo[A] {
}
object semiring_modulo {
  implicit def `Euclidean_Rings.semiring_modulo_nat`: semiring_modulo[Nat.nat] =
    new semiring_modulo[Nat.nat] {
    val `Rings.modulo` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.modulo_nata(a, b)
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait algebraic_semidom[A] extends semidom_divide[A] {
}
object algebraic_semidom {
  implicit def
    `Euclidean_Rings.algebraic_semidom_nat`: algebraic_semidom[Nat.nat] = new
    algebraic_semidom[Nat.nat] {
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semidom_modulo[A] extends algebraic_semidom[A] with semiring_modulo[A] {
}
object semidom_modulo {
  implicit def `Euclidean_Rings.semidom_modulo_nat`: semidom_modulo[Nat.nat] =
    new semidom_modulo[Nat.nat] {
    val `Rings.modulo` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.modulo_nata(a, b)
    val `Rings.divide` = (a: Nat.nat, b: Nat.nat) =>
      Euclidean_Rings.divide_nata(a, b)
    val `Groups.minus` = (a: Nat.nat, b: Nat.nat) => Nat.minus_nata(a, b)
    val `Groups.one` = Nat.one_nata
    val `Groups.times` = (a: Nat.nat, b: Nat.nat) => Nat.times_nata(a, b)
    val `Groups.zero` = Nat.zero_nata()
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

def dvd[A : HOL.equal : semidom_modulo](a: A, b: A): Boolean =
  HOL.eq[A](modulo[A](b, a), Groups.zero[A])

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => Groups.one[A]
  case false => Groups.zero[A]
}

} /* object Rings */

object Int {

abstract sealed class int
final case class zero_inta() extends int
final case class Pos(a: Num.num) extends int
final case class Neg(a: Num.num) extends int

def one_inta: int = Pos(Num.One())

def uminus_int(x0: int): int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case zero_inta() => zero_inta()
}

def dup(x0: int): int = x0 match {
  case Neg(n) => Neg(Num.Bit0(n))
  case Pos(n) => Pos(Num.Bit0(n))
  case zero_inta() => zero_inta()
}

def minus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(Num.plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(Num.plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (zero_inta(), l) => uminus_int(l)
  case (k, zero_inta()) => k
}

def sub(x0: Num.num, x1: Num.num): int = (x0, x1) match {
  case (Num.Bit0(m), Num.Bit1(n)) => minus_int(dup(sub(m, n)), one_inta)
  case (Num.Bit1(m), Num.Bit0(n)) => plus_inta(dup(sub(m, n)), one_inta)
  case (Num.Bit1(m), Num.Bit1(n)) => dup(sub(m, n))
  case (Num.Bit0(m), Num.Bit0(n)) => dup(sub(m, n))
  case (Num.One(), Num.Bit1(n)) => Neg(Num.Bit0(n))
  case (Num.One(), Num.Bit0(n)) => Neg(Num.BitM(n))
  case (Num.Bit1(m), Num.One()) => Pos(Num.Bit0(m))
  case (Num.Bit0(m), Num.One()) => Pos(Num.BitM(m))
  case (Num.One(), Num.One()) => zero_inta()
}

def plus_inta(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(Num.plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(Num.plus_num(m, n))
  case (zero_inta(), l) => l
  case (k, zero_inta()) => k
}

def times_inta(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(Num.times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(Num.times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(Num.times_num(m, n))
  case (zero_inta(), l) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

def nat(x0: int): Nat.nat = x0 match {
  case Pos(k) => Num.nat_of_num(k)
  case zero_inta() => Nat.zero_nata()
  case Neg(k) => Nat.zero_nata()
}

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => false
}

def abs_int(i: int): int = (if (less_int(i, zero_inta())) uminus_int(i) else i)

def equal_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_inta()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.equal_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => false
  case (zero_inta(), zero_inta()) => true
}

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => Num.less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => Num.less_eq_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => true
}

} /* object Int */

object Parity {

def adjust_div(x0: (Int.int, Int.int)): Int.int = x0 match {
  case (q, r) =>
    Int.plus_inta(q, Rings.of_bool[Int.int](! (Int.equal_int(r,
                      Int.zero_inta()))))
}

def adjust_mod(l: Num.num, r: Int.int): Int.int =
  (if (Int.equal_int(r, Int.zero_inta())) Int.zero_inta()
    else Int.minus_int(Int.Pos(l), r))

def divmod_step_int(l: Int.int, qr: (Int.int, Int.int)): (Int.int, Int.int) =
  {
    val (q, r) = qr: ((Int.int, Int.int));
    (if (Int.less_eq_int(Int.abs_int(l), Int.abs_int(r)))
      (Int.plus_inta(Int.times_inta(Int.Pos(Num.Bit0(Num.One())), q),
                      Int.one_inta),
        Int.minus_int(r, l))
      else (Int.times_inta(Int.Pos(Num.Bit0(Num.One())), q), r))
  }

def divmod_int(m: Num.num, x1: Num.num): (Int.int, Int.int) = (m, x1) match {
  case (Num.Bit1(m), Num.Bit1(n)) =>
    (if (Num.less_num(m, n)) (Int.zero_inta(), Int.Pos(Num.Bit1(m)))
      else divmod_step_int(Int.Pos(Num.Bit1(n)),
                            divmod_int(Num.Bit1(m), Num.Bit0(Num.Bit1(n)))))
  case (Num.Bit0(m), Num.Bit1(n)) =>
    (if (Num.less_eq_num(m, n)) (Int.zero_inta(), Int.Pos(Num.Bit0(m)))
      else divmod_step_int(Int.Pos(Num.Bit1(n)),
                            divmod_int(Num.Bit0(m), Num.Bit0(Num.Bit1(n)))))
  case (Num.Bit1(m), Num.Bit0(n)) =>
    {
      val (q, r) = divmod_int(m, n): ((Int.int, Int.int));
      (q, Int.plus_inta(Int.times_inta(Int.Pos(Num.Bit0(Num.One())), r),
                         Int.one_inta))
    }
  case (Num.Bit0(m), Num.Bit0(n)) =>
    {
      val (q, r) = divmod_int(m, n): ((Int.int, Int.int));
      (q, Int.times_inta(Int.Pos(Num.Bit0(Num.One())), r))
    }
  case (Num.One(), Num.Bit1(n)) => (Int.zero_inta(), Int.Pos(Num.One()))
  case (Num.One(), Num.Bit0(n)) => (Int.zero_inta(), Int.Pos(Num.One()))
  case (m, Num.One()) => (Int.Pos(m), Int.zero_inta())
}

} /* object Parity */

object Euclidean_Rings {

def divmod_nat(m: Nat.nat, n: Nat.nat): (Nat.nat, Nat.nat) =
  (if (Nat.equal_nata(n, Nat.zero_nata()) || Nat.less_nat(m, n))
    (Nat.zero_nata(), m)
    else {
           val (q, a) =
             divmod_nat(Nat.minus_nata(m, n), n): ((Nat.nat, Nat.nat));
           (Nat.Suc(q), a)
         })

def divide_nata(m: Nat.nat, n: Nat.nat): Nat.nat =
  Product_Type.fst[Nat.nat, Nat.nat](divmod_nat(m, n))

def modulo_nata(m: Nat.nat, n: Nat.nat): Nat.nat =
  Product_Type.snd[Nat.nat, Nat.nat](divmod_nat(m, n))

def divide_int(k: Int.int, ka: Int.int): Int.int = (k, ka) match {
  case (Int.Neg(m), Int.Neg(n)) =>
    Product_Type.fst[Int.int, Int.int](Parity.divmod_int(m, n))
  case (Int.Pos(m), Int.Neg(n)) =>
    Int.uminus_int(Parity.adjust_div(Parity.divmod_int(m, n)))
  case (Int.Neg(m), Int.Pos(n)) =>
    Int.uminus_int(Parity.adjust_div(Parity.divmod_int(m, n)))
  case (Int.Pos(m), Int.Pos(n)) =>
    Product_Type.fst[Int.int, Int.int](Parity.divmod_int(m, n))
  case (k, Int.Neg(Num.One())) => Int.uminus_int(k)
  case (k, Int.Pos(Num.One())) => k
  case (Int.zero_inta(), k) => Int.zero_inta()
  case (k, Int.zero_inta()) => Int.zero_inta()
}

def modulo_int(k: Int.int, ka: Int.int): Int.int = (k, ka) match {
  case (Int.Neg(m), Int.Neg(n)) =>
    Int.uminus_int(Product_Type.snd[Int.int, Int.int](Parity.divmod_int(m, n)))
  case (Int.Pos(m), Int.Neg(n)) =>
    Int.uminus_int(Parity.adjust_mod(n, Product_Type.snd[Int.int,
                  Int.int](Parity.divmod_int(m, n))))
  case (Int.Neg(m), Int.Pos(n)) =>
    Parity.adjust_mod(n, Product_Type.snd[Int.int,
   Int.int](Parity.divmod_int(m, n)))
  case (Int.Pos(m), Int.Pos(n)) =>
    Product_Type.snd[Int.int, Int.int](Parity.divmod_int(m, n))
  case (k, Int.Neg(Num.One())) => Int.zero_inta()
  case (k, Int.Pos(Num.One())) => Int.zero_inta()
  case (Int.zero_inta(), k) => Int.zero_inta()
  case (k, Int.zero_inta()) => k
}

} /* object Euclidean_Rings */

object GCD {

def gcd_int(k: Int.int, l: Int.int): Int.int =
  Int.abs_int((if (Int.equal_int(l, Int.zero_inta())) k
                else gcd_int(l, Euclidean_Rings.modulo_int(Int.abs_int(k),
                    Int.abs_int(l)))))

} /* object GCD */

object Rat {

abstract sealed class rat
final case class Frct(a: (Int.int, Int.int)) extends rat

def normalize(p: (Int.int, Int.int)): (Int.int, Int.int) =
  (if (Int.less_int(Int.zero_inta(), Product_Type.snd[Int.int, Int.int](p)))
    {
      val a =
        GCD.gcd_int(Product_Type.fst[Int.int, Int.int](p),
                     Product_Type.snd[Int.int, Int.int](p)):
          Int.int;
      (Euclidean_Rings.divide_int(Product_Type.fst[Int.int, Int.int](p), a),
        Euclidean_Rings.divide_int(Product_Type.snd[Int.int, Int.int](p), a))
    }
    else (if (Int.equal_int(Product_Type.snd[Int.int, Int.int](p),
                             Int.zero_inta()))
           (Int.zero_inta(), Int.one_inta)
           else {
                  val a =
                    Int.uminus_int(GCD.gcd_int(Product_Type.fst[Int.int,
                         Int.int](p),
        Product_Type.snd[Int.int, Int.int](p))):
                      Int.int;
                  (Euclidean_Rings.divide_int(Product_Type.fst[Int.int,
                        Int.int](p),
       a),
                    Euclidean_Rings.divide_int(Product_Type.snd[Int.int,
                         Int.int](p),
        a))
                }))

def Fract(a: Int.int, b: Int.int): rat = Frct(normalize((a, b)))

def of_int(a: Int.int): rat = Frct((a, Int.one_inta))

def quotient_of(x0: rat): (Int.int, Int.int) = x0 match {
  case Frct(x) => x
}

def one_rat: rat = Frct((Int.one_inta, Int.one_inta))

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((Int.int, Int.int))
    val (b, d) = quotient_of(q): ((Int.int, Int.int));
    Int.less_int(Int.times_inta(a, d), Int.times_inta(c, b))
  }

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((Int.int, Int.int))
         val (b, d) = quotient_of(q): ((Int.int, Int.int));
         normalize((Int.plus_inta(Int.times_inta(a, d), Int.times_inta(b, c)),
                     Int.times_inta(c, d)))
       })

def zero_rat: rat = Frct((Int.zero_inta(), Int.one_inta))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((Int.int, Int.int))
         val (b, d) = quotient_of(q): ((Int.int, Int.int));
         normalize((Int.minus_int(Int.times_inta(a, d), Int.times_inta(b, c)),
                     Int.times_inta(c, d)))
       })

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((Int.int, Int.int))
    val (b, d) = quotient_of(q): ((Int.int, Int.int));
    Int.less_eq_int(Int.times_inta(a, d), Int.times_inta(c, b))
  }

def times_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((Int.int, Int.int))
         val (b, d) = quotient_of(q): ((Int.int, Int.int));
         normalize((Int.times_inta(a, b), Int.times_inta(c, d)))
       })

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((Int.int, Int.int))
         val (b, d) = quotient_of(q): ((Int.int, Int.int));
         normalize((Int.times_inta(a, d), Int.times_inta(c, b)))
       })

def floor_rat(p: rat): Int.int =
  {
    val (a, b) = quotient_of(p): ((Int.int, Int.int));
    Euclidean_Rings.divide_int(a, b)
  }

} /* object Rat */

object Real {

abstract sealed class real
final case class Ratreal(a: Rat.rat) extends real

def one_reala: real = Ratreal(Rat.one_rat)

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.plus_rat(x, y))
}

def zero_reala: real = Ratreal(Rat.zero_rat)

def times_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.times_rat(x, y))
}

def divide_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.divide_rat(x, y))
}

def floor_real(x0: real): Int.int = x0 match {
  case Ratreal(x) => Rat.floor_rat(x)
}

} /* object Real */

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

object Discrete_Laplace_rat {

def calculate_y(x: Nat.nat, s: Nat.nat): Nat.nat =
  Int.nat(Real.floor_real(Real.divide_real(Nat.of_nat[Real.real](x),
    Nat.of_nat[Real.real](s))))

} /* object Discrete_Laplace_rat */

object Code_Generation {

def fast_dice_roll_ra(n: Nat.nat, v: Nat.nat, c: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  (if (Nat.less_eq_nat(n, v))
    (if (Nat.less_nat(c, n)) Randomized_Algorithm.return_ra[Nat.nat](c)
      else fast_dice_roll_ra(n, Nat.minus_nata(v, n), Nat.minus_nata(c, n)))
    else Randomized_Algorithm.bind_ra[Boolean,
                                       Nat.nat](Randomized_Algorithm.coin_ra,
         ((b: Boolean) =>
           fast_dice_roll_ra(n, Nat.times_nata(Num.nat_of_num(Num.Bit0(Num.One())),
        v),
                              Nat.plus_nata(Nat.times_nata(Num.nat_of_num(Num.Bit0(Num.One())),
                    c),
     (if (b) Nat.one_nata else Nat.zero_nata()))))))

def fast_uniform_ra(n: Nat.nat): Randomized_Algorithm.random_alg[Nat.nat] =
  fast_dice_roll_ra(n, Nat.one_nata, Nat.zero_nata())

def bernoulli_rat_ra(n: Nat.nat, d: Nat.nat):
      Randomized_Algorithm.random_alg[Boolean]
  =
  (if (Nat.equal_nata(d, Nat.zero_nata()))
    Randomized_Algorithm.return_ra[Boolean](false)
    else Randomized_Algorithm.bind_ra[Nat.nat,
                                       Boolean](fast_uniform_ra(d),
         ((x: Nat.nat) =>
           Randomized_Algorithm.return_ra[Boolean](Nat.less_nat(x, n)))))

def bernoulli_exp_minus_rat_from_0_to_1_loop_ra(p: Rat.rat, k: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  Randomized_Algorithm.bind_ra[Boolean,
                                Nat.nat]({
   val (n, d) = Rat.quotient_of(p): ((Int.int, Int.int));
   bernoulli_rat_ra(Int.nat(n),
                     Int.nat(Int.times_inta(d, Nat.of_nat[Int.int](k))))
 },
  ((a: Boolean) =>
    (if (a)
      bernoulli_exp_minus_rat_from_0_to_1_loop_ra(p,
           Nat.plus_nata(k, Nat.one_nata))
      else Randomized_Algorithm.return_ra[Nat.nat](k))))

def bernoulli_exp_minus_rat_from_0_to_1_ra(p: Rat.rat):
      Randomized_Algorithm.random_alg[Boolean]
  =
  Randomized_Algorithm.bind_ra[Nat.nat,
                                Boolean](bernoulli_exp_minus_rat_from_0_to_1_loop_ra(p,
      Nat.one_nata),
  ((k: Nat.nat) =>
    (if (! (Rings.dvd[Nat.nat](Num.nat_of_num(Num.Bit0(Num.One())), k)))
      Randomized_Algorithm.return_ra[Boolean](true)
      else Randomized_Algorithm.return_ra[Boolean](false))))

def bernoulli_exp_minus_rat_loop_ra(p: Rat.rat, k: Nat.nat):
      Randomized_Algorithm.random_alg[Boolean]
  =
  (if (Nat.less_eq_nat(Nat.one_nata, k))
    Randomized_Algorithm.bind_ra[Boolean,
                                  Boolean](bernoulli_exp_minus_rat_from_0_to_1_ra(Rat.one_rat),
    ((b: Boolean) =>
      (if (b)
        bernoulli_exp_minus_rat_loop_ra(p, Nat.minus_nata(k, Nat.one_nata))
        else Randomized_Algorithm.return_ra[Boolean](false))))
    else Randomized_Algorithm.return_ra[Boolean](true))

def bernoulli_exp_minus_rat_ra(p: Rat.rat):
      Randomized_Algorithm.random_alg[Boolean]
  =
  (if (Rat.less_rat(p, Rat.zero_rat))
    Randomized_Algorithm.return_ra[Boolean](true)
    else (if (Rat.less_eq_rat(Rat.zero_rat, p) &&
                Rat.less_eq_rat(p, Rat.one_rat))
           bernoulli_exp_minus_rat_from_0_to_1_ra(p)
           else Randomized_Algorithm.bind_ra[Boolean,
      Boolean](bernoulli_exp_minus_rat_loop_ra(p, Int.nat(Rat.floor_rat(p))),
                ((b: Boolean) =>
                  (if (b)
                    bernoulli_exp_minus_rat_from_0_to_1_ra(Rat.minus_rat(p,
                                  Rat.of_int(Rat.floor_rat(p))))
                    else Randomized_Algorithm.return_ra[Boolean](b))))))

def discrete_laplace_rat_unit_loop2_ra(v: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  Randomized_Algorithm.bind_ra[Boolean,
                                Nat.nat](bernoulli_exp_minus_rat_ra(Rat.one_rat),
  ((a: Boolean) =>
    (if (Product_Type.equal_bool(a, false))
      Randomized_Algorithm.return_ra[Nat.nat](v)
      else discrete_laplace_rat_unit_loop2_ra(Nat.plus_nata(v, Nat.one_nata)))))

def discrete_laplace_rat_unit_loop1_ra(t: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  Randomized_Algorithm.bind_ra[Nat.nat,
                                Nat.nat](fast_uniform_ra(t),
  ((u: Nat.nat) =>
    Randomized_Algorithm.bind_ra[Boolean,
                                  Nat.nat](bernoulli_exp_minus_rat_ra(Rat.Fract(Nat.of_nat[Int.int](u),
 Nat.of_nat[Int.int](t))),
    ((d: Boolean) =>
      (if (d) Randomized_Algorithm.return_ra[Nat.nat](u)
        else discrete_laplace_rat_unit_loop1_ra(t))))))

def discrete_laplace_rat_unit_ra(t: Nat.nat):
      Randomized_Algorithm.random_alg[Nat.nat]
  =
  Randomized_Algorithm.bind_ra[Nat.nat,
                                Nat.nat](discrete_laplace_rat_unit_loop1_ra(t),
  ((u: Nat.nat) =>
    Randomized_Algorithm.bind_ra[Nat.nat,
                                  Nat.nat](discrete_laplace_rat_unit_loop2_ra(Nat.zero_nata()),
    ((v: Nat.nat) =>
      Randomized_Algorithm.return_ra[Nat.nat](Nat.plus_nata(u,
                     Nat.times_nata(t, v)))))))

def discrete_laplace_rat_ra(t: Nat.nat, s: Nat.nat):
      Randomized_Algorithm.random_alg[Int.int]
  =
  Randomized_Algorithm.bind_ra[Nat.nat,
                                Int.int](discrete_laplace_rat_unit_ra(t),
  ((x: Nat.nat) =>
    Randomized_Algorithm.bind_ra[Boolean,
                                  Int.int](bernoulli_rat_ra(Nat.one_nata,
                     Num.nat_of_num(Num.Bit0(Num.One()))),
    ((b: Boolean) =>
      {
        val xa = Discrete_Laplace_rat.calculate_y(x, s): Nat.nat;
        (if (! b && Int.equal_int(Nat.of_nat[Int.int](xa), Int.zero_inta()))
          discrete_laplace_rat_ra(t, s)
          else (if (b)
                 Randomized_Algorithm.return_ra[Int.int](Int.uminus_int(Nat.of_nat[Int.int](xa)))
                 else Randomized_Algorithm.return_ra[Int.int](Nat.of_nat[Int.int](xa))))
      }))))

def discrete_laplace_mechanism_ra[A](f: (List[A]) => Int.int, delta: Nat.nat,
                                      x: List[A], epsilon1: Nat.nat,
                                      epsilon2: Nat.nat):
      Randomized_Algorithm.random_alg[Int.int]
  =
  Randomized_Algorithm.bind_ra[Int.int,
                                Int.int](discrete_laplace_rat_ra(Nat.times_nata(epsilon2,
 delta),
                          epsilon1),
  ((noise: Int.int) =>
    Randomized_Algorithm.return_ra[Int.int](Int.plus_inta(noise, f(x)))))

} /* object Code_Generation */
