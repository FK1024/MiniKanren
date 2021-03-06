object Implementation {

  var varCounter = 0

  trait Term
  case class Lit(v: String) extends Term
  case object End extends Term
  case class Pair(left: Term, right: Term) extends Term
  case class Var(varName: String) extends Term {
    var name: String = varName
    val id: Int = varCounter
    varCounter += 1

    override def toString: String = name + id

    override def equals(obj: Any): Boolean = {
      obj.isInstanceOf[Var] && obj.asInstanceOf[Var].id == this.id
    }
  }

  trait Stream[+T] {
    def map[B](f: T => B): List[B] = {
      this match {
        case Cons(fst, rst) => f(fst()) :: rst().map(f)
        case Empty => Nil
      }
    }

    override def toString: String = toString(None)

    def toString(n: Int): String = toString(Some(n))

    def toString(n: Option[Int]): String = {
      this match {
        case Empty => "Empty"
        case Cons(fst, rst) => s"Cons(${fst().toString}, ${
          n match {
            case None => rst().toString
            case Some(n) =>
              if (n == 1) "..."
              else rst().toString(Some(n - 1))
          }
        })"
        case Susp(f) => s"Susp(${f().toString}"
      }
    }
  }

  case object Empty extends Stream[Nothing]
  case class Cons[T](elem: () => T, rst: () => Stream[T]) extends Stream[T] {
    override def equals(obj: Any): Boolean = {
      obj match {
        case Cons(fst, rst) => fst() == this.elem() && rst().equals(this.rst())
        case _ => false
      }
    }
  }
  case class Susp[T](func: () => Stream[T]) extends Stream[T]
  object Stream {
    def cons[T](elem: => T, rst: => Stream[T]): Stream[T] = {
      lazy val element = elem
      lazy val rest = rst
      Cons(() => element, () => rest)
    }
  }

  type Subst = Map[Var, Term]
  type Goal = Subst => Stream[Subst]

  def succeed: Goal = {
    s: Subst => Stream.cons(s, Empty)
  }

  def fail: Goal = {
    _: Subst => Empty
  }

  def isVar(myVar: Any): Boolean = myVar.isInstanceOf[Var]

  def walk(v: Term, s: Subst): Term =
    if (isVar(v)) {
      s.get(v.asInstanceOf[Var]) match {
        case Some(t) => walk(t, s)
        case None => v
      }
    } else v

  def occurs(x: Var, v: Term, s: Subst): Boolean = {
    walk(v, s) match {
      case v: Var => v.equals(x)
      case Pair(l, r) => occurs(x, l, s) || occurs(x, r, s)
      case _ => false
    }
  }

  def ext_s(x: Var, v: Term, s: Subst): Option[Subst] = {
    if (occurs(x, v, s)) None
    else Some(s + (x -> v))
  }

  def unify(u: Term, v: Term, s: Subst): Option[Subst] = {
    val uWalked = walk(u, s)
    val vWalked = walk(v, s)
    if (uWalked.equals(vWalked)) Some(s)
    else (uWalked, vWalked) match {
      case (u: Var, v: Term) => ext_s(u, v, s)
      case (u: Term, v: Var) => ext_s(v, u, s)
      case (Pair(ul, ur), Pair(vl, vr)) => unify(ul, vl, s) match {
        case Some(s) => unify(ur, vr, s)
        case None => None
      }
      case _ => None
    }
  }

  def ==(u: Term, v: Term): Goal = {
    s: Subst => unify(u, v, s) match {
      case Some(unified) => succeed(unified)
      case None => fail(s)
    }
  }

  def append_inf[T](s_inf: Stream[T], t_inf: Stream[T]): Stream[T] = {
    s_inf match {
      case Empty => t_inf
      case Cons(fst, rst) => Stream.cons(fst(), append_inf(rst(), t_inf))
      case Susp(f) => Susp(() => append_inf(t_inf, f()))
    }
  }

  def append_map_inf(g: Goal, s_inf: Stream[Subst]): Stream[Subst] = {
    s_inf match {
      case Empty => Empty
      case Cons(fst, rst) => append_inf(g(fst()), append_map_inf(g, rst()))
      case Susp(f) => Susp(() => append_map_inf(g, f()))
    }
  }

  def disj2(g1: Goal, g2: Goal): Subst => Stream[Subst] = {
    s: Subst => append_inf(g1(s), g2(s))
  }

  def conj2(g1: Goal, g2: Goal): Subst => Stream[Subst] = {
    s: Subst => append_map_inf(g2, g1(s))
  }

  def take_inf(n: Int, s_inf: Stream[Subst]): Stream[Subst] = take_inf(Some(n), s_inf)

  def take_inf(n: Option[Int], s_inf: Stream[Subst]): Stream[Subst] = {
    n match {
      case None => s_inf
      case Some(n) =>
        if (n == 0) Empty
        else s_inf match {
          case Empty => Empty
          case Cons(fst, rst) => Stream.cons(fst(), take_inf(n - 1, rst()))
          case Susp(f) => take_inf(n, f())
        }
    }
  }

  // Never used
  def call_fresh(name: String, f: Var => Goal): Goal = {
    f(Var(name))
  }

  def reify_name(n: Int): String = {
    "_" + n.toString
  }

  def walk_star(v: Term, s: Subst): Term = {
    val walked = walk(v, s)
    walked match {
      case v: Var => v
      case Pair(l, r) => Pair(walk_star(l, s), walk_star(r, s))
      case _ => walked
    }
  }

  def reify_s(v: Term, r: Subst = Map()): Subst = {
    val walked = walk(v, r)
    walked match {
      case v: Var => r + (v -> Lit(reify_name(r.size)))
      case Pair(left, right) => reify_s(right, reify_s(left, r))
      case _ => r
    }
  }

  def reify(v: Term): Subst => Term = {
    s: Subst => {
      val walked = walk_star(v, s)
      walk_star(walked, reify_s(walked))
    }
  }

  def run_goal(n: Option[Int], g: Goal): Stream[Subst] = {
    take_inf(n, g(Map()))
  }

  def ifte(g1: Goal, g2: Goal, g3: Goal): Goal = {
    s: Subst => {
      def loop(s_inf: Stream[Subst]): Stream[Subst] = {
        s_inf match {
          case Empty => g3(s)
          case Cons(_, _) => append_map_inf(g2, s_inf)
          case _ => Susp(() => loop(s_inf))
        }
      }
      loop(g1(s))
    }
  }

  def once(g: Goal): Goal = {
    s: Subst => {
      def loop(s_inf: Stream[Subst]): Stream[Subst] = {
        s_inf match {
          case Empty => Empty
          case Cons(fst, _) => Stream.cons(fst(), Empty)
          case _ => Susp(() => loop(s_inf))
        }
      }
      loop(g(s))
    }
  }

  def disj(g: Goal*): Goal = {
    g.length match {
      case 0 => fail
      case 1 => g(0)
      case _ => disj2(g(0), disj(g.tail:_*))
    }
  }

  def conj(g: Goal*): Goal = {
    g.length match {
      case 0 => succeed
      case 1 => g(0)
      case _ => conj2(g(0), conj(g.tail:_*))
    }
  }

  // just for compliance
  def fresh(vars: List[Any], g: Goal*): Goal = {
    conj(g:_*)
  }

  def run(n: Int, q: Var, g: Goal*) : List[Any] = run(Some(n), q, g:_*)

  def run(n: Option[Int], q: Var, g: Goal*): List[Term] = {
    run_goal(n, conj(g:_*)).map(reify(q))
  }

  def run(n: Int, vars: List[Var], g: Goal*): List[Any] = run(Some(n), vars, g:_*)

  def run(n: Option[Int], vars: List[Var], g: Goal*): List[Any] = {
    val q = Var("q")
    run(n, q, fresh(vars, ==(listOfVarToPair(vars), q) +: g:_*))
  }

  def listOfVarToPair(l: List[Var]): Term = {
    l match {
      case Nil => End
      case v1 :: rst => Pair(v1, listOfVarToPair(rst))
    }
  }

  def listToPairOfLit[T](l: T*): Term = {
    l match {
      case Seq() => End
      case Seq(fst) => Pair(Lit(fst.toString), End)
      case Seq(fst, rst @ _*) => Pair(Lit(fst.toString), listToPairOfLit(rst:_*))
    }
  }

  def run_star(q: Var, g: Goal*): List[Any] = {
    run(None, q, g:_*)
  }

  def run_star(q: List[Var], g: Goal*): List[Any] = {
    run(None, q, g:_*)
  }

  def conde(g: List[Goal]*): Goal = {
    var res: List[Goal] = List()
    for (goalList <- g) {
      res = res :+ conj(goalList:_*)
    }
    disj(res:_*)
  }


  def conso(a: Term, d: Term, p: Term): Goal = {
    s: Subst => ==(Pair(a, d), p)(s)
  }

  def nullo(x: Term): Goal = {
    s: Subst => ==(End, x)(s)
  }

  def appendo(l: Term, t: Term, out: Term): Goal = {
    s: Subst => {
      val a = Var("a")
      val d = Var("d")
      val res = Var("res")

      lazy val apdo = appendo(d, t, res)
      lazy val result = conde(
        List(nullo(l), ==(t, out)),
        List(fresh(List(a, d, res),
          conso(a, d, l),
          apdo,
          conso(a, res, out))))

      result(s)
    }
  }

  def main(args: Array[String]): Unit = {
    val q = Var("q")
    // Example from the report representing the query (run* q (appendo '(1 2 3) q '(1 2 3 4 5 6))) resulting in '((4 5 6))
    println(run_star(q, appendo(listToPairOfLit(1, 2, 3), q, listToPairOfLit(1, 2, 3, 4, 5, 6))))

    // another example, returning the List(Lit(2))
    println(run_star(q, appendo(Pair(Lit("1"), Pair(q, Pair(Lit("3"), End))), listToPairOfLit(4, 5, 6), listToPairOfLit(1, 2, 3, 4, 5, 6))))

    // for more examples see or run the test cases
  }
}
