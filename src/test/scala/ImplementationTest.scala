import Implementation._
import org.scalatest.funsuite.AnyFunSuite

class ImplementationTest extends AnyFunSuite {
  val u = new Var("u")
  val v = new Var("v")
  val w = new Var("w")
  val x = new Var("x")
  val y = new Var("y")
  val z = new Var("z")

  test("walk test") {
    assert(walk(x, Map(y -> 7)) === x)
    assert(walk(x, Map(x -> 7)) === 7)
    assert(walk(x, Map(x -> y, y -> 42)) === 42)
    assert(walk(x, Map(x -> List(y, "42", z))) === List(y, "42", z))
  }

  test("occurs test") {
    assert(occurs(x, x, Map()))
    assert(occurs(x, List(y), Map(y -> x)))
    assert(occurs(x, y, Map(y -> x)))
    assert(!occurs(x, z, Map(y -> x)))
    assert(occurs(x, List(y, z), Map(y -> List(x, z))))
  }

  test("extend substitution test") {
    assert(ext_s(x, List(x), Map()) === None)
    assert(ext_s(x, List(y), Map(y -> x)) === None)
    assert(ext_s(y, z, Map(x -> y)) === Some(Map(x -> y, y -> z)))
  }

  test("unify test") {
    assert(unify(x, y, Map()) === Some(Map(x -> y)))
    assert(unify(x, x, Map(y -> z)) === Some(Map(y -> z)))
    assert(unify(1, 1, Map()) === Some(Map()))
    assert(unify("a", "b", Map()) === None)
    assert(unify(x, 7, Map()) === Some(Map(x -> 7)))
    assert(unify(7, x, Map()) === Some(Map(x -> 7)))

    assert(unify(List(x, y), List(1, 2), Map()) === Some(Map(x -> 1, y -> 2)))
    assert(unify(List(x, y), List(1, x), Map()) === Some(Map(x -> 1, y -> 1)))
    assert(unify(x, List(1, 2), Map()) === Some(Map(x -> List(1, 2))))
    assert(unify(x, List(1, x), Map()) === None)
    assert(unify(List(1, x, 3), List(1, 2, y), Map()) === Some(Map(x -> 2, y -> 3)))
    assert(unify(List(x, y), List(1, 2, 3), Map()) === None)
  }

  test("== test") {
    assert(Implementation.==(true, false)(Map()) === Implementation.fail(Map()))
    assert(Implementation.==(false, false)(Map()) === Implementation.succeed(Map()))
    assert(Implementation.==(x, y)(Map()) === Stream.cons(Map(x -> y), Empty))
    assert(Implementation.==(List(x, 1), List(x, z))(Map(x -> y)) === Stream.cons(Map(x -> y, z -> 1), Empty))
  }

  test("append_inf test") {
    lazy val ones: Stream[Int] = Stream.cons(1, ones)
    lazy val twos: Stream[Int] = Stream.cons(2, twos)
    assert(append_inf(ones, twos).toString(3) == "Cons(1, Cons(1, Cons(1, ...)))")

//    lazy val abc = Stream.cons("a", Stream.cons("b", Stream.cons("c", Susp(() => Empty))))
//    assert(append_inf(abc, twos).toString(5) == "Cons(a, Cons(b, Cons(c, Cons(2, Cons(2, ...)))))")
  }

  test("conj2 test") {
    assert(conj2(Implementation.==("olive", x), Implementation.==("olive", x))(Map())
      === Stream.cons(Map(x -> "olive"), Empty))
    assert(conj2(Implementation.==("olive", x), Implementation.==("oil", x))(Map())
      === Empty)
    assert(conj2(Implementation.==(List(2, x),List(2, 3)), Implementation.==(List(y, 3), List(2, 3)))(Map())
      === Stream.cons(Map(x -> 3, y -> 2), Empty))
  }

  test("disj2 test") {
    assert(disj2(Implementation.==("olive", x), Implementation.==("oil", x))(Map())
      === Stream.cons(Map(x -> "olive"), Stream.cons(Map(x -> "oil"), Empty)))
    assert(disj2(Implementation.==("olive", x), Implementation.==("oil", x))(Map(x -> "olive"))
      === Stream.cons(Map(x -> "olive"), Empty))
  }

  test("take_inf test") {
    val disj = disj2(Implementation.==(List("olive", y), List(x, "apple")), Implementation.==(List("oil", y), List(x, "panda")))(Map())
    assert(take_inf(0, disj) === Empty)
    assert(take_inf(1, disj) === Stream.cons(Map(x -> "olive", y -> "apple"), Empty))
    assert(take_inf(2, disj) === Stream.cons(Map(x -> "olive", y -> "apple"), Stream.cons(Map(x -> "oil", y -> "panda"), Empty)))
    assert(take_inf(42, disj) === Stream.cons(Map(x -> "olive", y -> "apple"), Stream.cons(Map(x -> "oil", y -> "panda"), Empty)))
    assert(take_inf(None, disj) === Stream.cons(Map(x -> "olive", y -> "apple"), Stream.cons(Map(x -> "oil", y -> "panda"), Empty)))
  }

  test("walk_star test") {
    assert(walk_star(y, Map(z -> "a", x -> 'w', y -> z)) === "a")
    assert(walk_star(x, Map(y -> "b", z -> y, x -> List(y, "e", z))) === List("b", "e", "b"))
    assert(walk_star(w, Map(x -> List(u, v), z -> y, w -> List(x, "e", z), u -> "c", v -> "q")) === List(List("c", "q"), "e", y))
  }

  test("reify_s test") {
    assert(reify_s(x) === Map(x -> "_0"))
    assert(reify_s(List(x, y, z)) === Map(x -> "_0", y -> "_1", z -> "_2"))
  }

  test("reify test") {
    val a1 = Map(x -> List(u, w, y, z, List(List("ice"), z)))
    val a2 = Map(y -> "corn")
    val a3 = Map(w -> List(v, u))
    val s = a1 ++ a2 ++ a3
    assert(reify(x)(s) === List("_0", List("_1", "_0"), "corn", "_2", List(List("ice"), "_2")))
  }

  test("ifte test") {
    assert(ifte(Implementation.succeed, Implementation.==(false, y), Implementation.==(true, y))(Map()) === Stream.cons(Map(y -> false), Empty))
    assert(ifte(Implementation.fail, Implementation.==(false, y), Implementation.==(true, y))(Map()) === Stream.cons(Map(y -> true), Empty))
    assert(ifte(Implementation.==(true, x), Implementation.==(false, y), Implementation.==(true, y))(Map())
      === Stream.cons(Map(x -> true, y -> false), Empty))
    assert(ifte(disj2(Implementation.==(true, x), Implementation.==(false, x)), Implementation.==(false, y), Implementation.==(true, y))(Map())
      === Stream.cons(Map(x -> true, y -> false), Stream.cons(Map(x -> false, y -> false), Empty)))
  }

  test("once test") {
    assert(ifte(once(disj2(Implementation.==(true, x), Implementation.==(false, x))), Implementation.==(false, y), Implementation.==(true, y))(Map())
      === Stream.cons(Map(x -> true, y -> false), Empty))
  }

  test("disj test") {
    assert(disj(Implementation.==("olive", x), Implementation.==("oil", x), Implementation.==("feta", x))(Map())
      === Stream.cons(Map(x -> "olive"), Stream.cons(Map(x -> "oil"), Stream.cons(Map(x -> "feta"), Empty))))
  }

  test("conj test") {
    assert(conj(Implementation.==("olive", x), Implementation.==("olive", x), Implementation.==("olive", x))(Map())
      === Stream.cons(Map(x -> "olive"), Empty))
  }

  test("run_star test") {
    assert(run_star(v, Implementation.fail) === List())
    assert(run_star(v, Implementation.succeed) === List("_0"))
    assert(run_star(u, disj(Implementation.==("pea", u), Implementation.==("pod", u))) === List("pea", "pod"))
    assert(run_star(x, fresh(List(y), conj(Implementation.==("oil", y), Implementation.==(x, y)))) === List("oil"))
    assert(run_star(List(x, y), Implementation.==("split", x), Implementation.==("pea", y)) === List(List("split", "pea")))
    assert(run_star(u, fresh(List(x, y), disj2(Implementation.==(List(x, y), u), Implementation.==(List(y, x), u))))
      === List(List("_0", "_1"), List("_0", "_1")))

    val myGoal = disj2(
      conj2(Implementation.==("split", x), Implementation.==("pea", y)),
      conj2(Implementation.==("red", x), Implementation.==("bean", y)))

    assert(run_star(List(x, y), myGoal) === List(List("split", "pea"), List("red", "bean")))
    assert(Implementation.run(1, List(x, y), myGoal) === List(List("split", "pea")))
  }
}
