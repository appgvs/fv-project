object HOL {

  trait equal[A] {
    val `HOL.equal`: (A, A) => Boolean
  }
  def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
  object equal {
    implicit def `Product_Type.equal_prod`[A: equal, B: equal]: equal[(A, B)] =
      new equal[(A, B)] {
        val `HOL.equal` = (a: (A, B), b: (A, B)) =>
          Product_Type.equal_proda[A, B](a, b)
      }
    implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
      val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
    }
  }

  def eq[A: equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Product_Type {

  def equal_proda[A: HOL.equal, B: HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
    (x0, x1) match {
      case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
    }

  def snd[A, B](x0: (A, B)): B = x0 match {
    case (x1, x2) => x2
  }

} /* object Product_Type */

object Orderings {

  trait ord[A] {
    val `Orderings.less_eq`: (A, A) => Boolean
    val `Orderings.less`: (A, A) => Boolean
  }
  def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
    A.`Orderings.less_eq`(a, b)
  def less[A](a: A, b: A)(implicit A: ord[A]): Boolean =
    A.`Orderings.less`(a, b)
  object ord {
    implicit def `Nat.ord_nat`: ord[Nat.nat] = new ord[Nat.nat] {
      val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) =>
        Nat.less_eq_nat(a, b)
      val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
    }
  }

  trait preorder[A] extends ord[A] {}
  object preorder {
    implicit def `Nat.preorder_nat`: preorder[Nat.nat] = new preorder[Nat.nat] {
      val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) =>
        Nat.less_eq_nat(a, b)
      val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
    }
  }

  trait order[A] extends preorder[A] {}
  object order {
    implicit def `Nat.order_nat`: order[Nat.nat] = new order[Nat.nat] {
      val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) =>
        Nat.less_eq_nat(a, b)
      val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
    }
  }

  trait linorder[A] extends order[A] {}
  object linorder {
    implicit def `Nat.linorder_nat`: linorder[Nat.nat] = new linorder[Nat.nat] {
      val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) =>
        Nat.less_eq_nat(a, b)
      val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
    }
  }

  def max[A: ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

} /* object Orderings */

object Lista {

  def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
    case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
    case (f, Nil, s)     => s
  }

  def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
    case (p, Nil)     => Nil
    case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
  }

  def member[A: HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
    case (Nil, y)     => false
    case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
  }

  def insert[A: HOL.equal](x: A, xs: List[A]): List[A] =
    (if (member[A](xs, x)) xs else x :: xs)

  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil)        => Nil
    case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
  }

  def removeAll[A: HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
    case (x, Nil) => Nil
    case (x, y :: xs) =>
      (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
  }

} /* object Lista */

object Set {

  abstract sealed class set[A]
  final case class seta[A](a: List[A]) extends set[A]
  final case class coset[A](a: List[A]) extends set[A]

  def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
    case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
  }

  def insert[A: HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
    case (x, coset(xs)) => coset[A](Lista.removeAll[A](x, xs))
    case (x, seta(xs))  => seta[A](Lista.insert[A](x, xs))
  }

  def member[A: HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
    case (x, coset(xs)) => !(Lista.member[A](xs, x))
    case (x, seta(xs))  => Lista.member[A](xs, x)
  }

  def remove[A: HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
    case (x, coset(xs)) => coset[A](Lista.insert[A](x, xs))
    case (x, seta(xs))  => seta[A](Lista.removeAll[A](x, xs))
  }

  def bot_set[A]: set[A] = seta[A](Nil)

  def sup_set[A: HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
    case (coset(xs), a) =>
      coset[A](Lista.filter[A](((x: A) => !(member[A](x, a))), xs))
    case (seta(xs), a) =>
      Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
  }

  def minus_set[A: HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
    case (a, coset(xs)) =>
      seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
    case (a, seta(xs)) =>
      Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => remove[A](aa, b)), xs, a)
  }

} /* object Set */

object Lattices_Big {

  def Max[A: Orderings.linorder](x0: Set.set[A]): A = x0 match {
    case Set.seta(x :: xs) =>
      Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
  }

} /* object Lattices_Big */

object USet {

  abstract sealed class USeta[A]
  final case class USetb[A](a: Set.set[A]) extends USeta[A]

  def add[A: HOL.equal](x0: USeta[A], e: A): USeta[A] = (x0, e) match {
    case (USetb(s), e) =>
      USetb[A](Set.sup_set[A](s, Set.insert[A](e, Set.bot_set[A])))
  }

  def merge[A: HOL.equal](x0: USeta[A], x1: USeta[A]): USeta[A] =
    (x0, x1) match {
      case (USetb(s1), USetb(s2)) => USetb[A](Set.sup_set[A](s1, s2))
    }

  def query[A](x0: USeta[A]): Set.set[A] = x0 match {
    case USetb(s) => s
  }

  def initial[A]: USeta[A] = USetb[A](Set.bot_set[A])

} /* object USet */

object Nat {

  abstract sealed class nat
  final case class zero_nat() extends nat
  final case class Suc(a: nat) extends nat

  def equal_nata(x0: nat, x1: nat): Boolean = (x0, x1) match {
    case (zero_nat(), Suc(x2))    => false
    case (Suc(x2), zero_nat())    => false
    case (Suc(x2), Suc(y2))       => equal_nata(x2, y2)
    case (zero_nat(), zero_nat()) => true
  }

  def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
    case (m, Suc(n))     => less_eq_nat(m, n)
    case (n, zero_nat()) => false
  }

  def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
    case (Suc(m), n)     => less_nat(m, n)
    case (zero_nat(), n) => true
  }

  def one_nat: nat = Suc(zero_nat())

  def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
    case (Suc(m), n)     => plus_nat(m, Suc(n))
    case (zero_nat(), n) => n
  }

  def minus_nat(m: nat, n: nat): nat = (m, n) match {
    case (Suc(m), Suc(n)) => minus_nat(m, n)
    case (zero_nat(), n)  => zero_nat()
    case (m, zero_nat())  => m
  }

} /* object Nat */

object Log {

  def merge[A: HOL.equal](
      s1: USet.USeta[(A, Nat.nat)],
      s2: USet.USeta[(A, Nat.nat)]
  ): USet.USeta[(A, Nat.nat)] =
    USet.merge[(A, Nat.nat)](s1, s2)

  def max_timestamp[A](s: USet.USeta[(A, Nat.nat)]): Nat.nat =
    Lattices_Big.Max[Nat.nat](
      Set.image[(A, Nat.nat), Nat.nat](
        ((a: (A, Nat.nat)) => Product_Type.snd[A, Nat.nat](a)),
        USet.query[(A, Nat.nat)](s)
      )
    )

  def insert[A: HOL.equal](
      l: USet.USeta[(A, Nat.nat)],
      e: A
  ): USet.USeta[(A, Nat.nat)] =
    USet
      .add[(A, Nat.nat)](l, (e, Nat.plus_nat(max_timestamp[A](l), Nat.one_nat)))

  def initial_log[A]: USet.USeta[A] = USet.initial[A]

} /* object Log */

object PNSet {

  abstract sealed class PNSeta[A]
  final case class PNSetb[A](a: Set.set[A], b: Set.set[A]) extends PNSeta[A]

  abstract sealed class PNSetUpdate[A]
  final case class Add[A](a: A) extends PNSetUpdate[A]
  final case class Remove[A](a: A) extends PNSetUpdate[A]

  def update[A: HOL.equal](x0: PNSeta[A], x1: PNSetUpdate[A]): PNSeta[A] =
    (x0, x1) match {
      case (PNSetb(a, r), Add(e)) =>
        PNSetb[A](Set.sup_set[A](a, Set.insert[A](e, Set.bot_set[A])), r)
      case (PNSetb(a, r), Remove(e)) =>
        PNSetb[A](
          Set.sup_set[A](a, Set.insert[A](e, Set.bot_set[A])),
          Set.sup_set[A](r, Set.insert[A](e, Set.bot_set[A]))
        )
    }

  def add[A: HOL.equal](pnset: PNSeta[A], e: A): PNSeta[A] =
    update[A](pnset, Add[A](e))

  def merge[A: HOL.equal](x0: PNSeta[A], x1: PNSeta[A]): PNSeta[A] =
    (x0, x1) match {
      case (PNSetb(a1, r1), PNSetb(a2, r2)) =>
        PNSetb[A](Set.sup_set[A](a1, a2), Set.sup_set[A](r1, r2))
    }

  def query[A: HOL.equal](x0: PNSeta[A]): Set.set[A] = x0 match {
    case PNSetb(a, r) => Set.minus_set[A](a, r)
  }

  def remove[A: HOL.equal](pnset: PNSeta[A], e: A): PNSeta[A] =
    update[A](pnset, Remove[A](e))

  def initial[A]: PNSeta[A] = PNSetb[A](Set.bot_set[A], Set.bot_set[A])

} /* object PNSet */

object IntegerVector {

  def merge(v1: List[Nat.nat], x1: List[Nat.nat]): List[Nat.nat] =
    (v1, x1) match {
      case (v1, Nil)      => v1
      case (Nil, v :: va) => v :: va
      case (x :: xs, y :: ys) =>
        (if (Nat.less_nat(y, x)) x else y) :: merge(xs, ys)
    }

  def query(xs: List[Nat.nat]): List[Nat.nat] = xs

  def update(x0: List[Nat.nat], x1: Nat.nat): List[Nat.nat] = (x0, x1) match {
    case (Nil, Nat.zero_nat())     => List(Nat.one_nat)
    case (x :: xs, Nat.zero_nat()) => Nat.plus_nat(x, Nat.one_nat) :: xs
    case (Nil, Nat.Suc(v)) =>
      Nat.zero_nat() :: update(Nil, Nat.minus_nat(Nat.Suc(v), Nat.one_nat))
    case (x :: xs, Nat.Suc(v)) =>
      x :: update(xs, Nat.minus_nat(Nat.Suc(v), Nat.one_nat))
  }

  def initial[A]: List[A] = Nil

} /* object IntegerVector */

object GCounter {

  abstract sealed class Inc
  final case class Inca(a: Nat.nat) extends Inc

  abstract sealed class GCountera
  final case class GCounterb(a: List[Nat.nat]) extends GCountera

  def merge(x0: GCountera, x1: GCountera): GCountera = (x0, x1) match {
    case (GCounterb(a), GCounterb(b)) => GCounterb(IntegerVector.merge(a, b))
  }

  def listsum(x0: List[Nat.nat]): Nat.nat = x0 match {
    case Nil     => Nat.zero_nat()
    case x :: xs => Nat.plus_nat(x, listsum(xs))
  }

  def query(x0: GCountera): Nat.nat = x0 match {
    case GCounterb(l) => listsum(l)
  }

  def update(x0: GCountera, x1: Inc): GCountera = (x0, x1) match {
    case (GCounterb(l), Inca(n)) => GCounterb(IntegerVector.update(l, n))
  }

  def increment(c: GCountera, n: Nat.nat): GCountera = update(c, Inca(n))

  def initial_counter: GCountera = GCounterb(IntegerVector.initial[Nat.nat])

} /* object GCounter */
