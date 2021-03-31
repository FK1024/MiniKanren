import Implementation._
import org.scalatest.funsuite.AnyFunSuite

class ImplementationTest extends AnyFunSuite {
  val u = Var("u")
  val v = Var("v")
  val w = Var("w")
  val x = Var("x")
  val y = Var("y")
  val z = Var("z")

  test("walk test") {
    assert(walk(x, Map(y -> Lit("7"))) === x)
    assert(walk(x, Map(x -> Lit("7"))) === Lit("7"))
    assert(walk(x, Map(x -> y, y -> Lit("42"))) === Lit("42"))
    assert(walk(x, Map(x -> Pair(y, Pair(Lit("42"), Pair(z, End))))) === Pair(y, Pair(Lit("42"), Pair(z, End))))
  }

  test("occurs test") {
    assert(occurs(x, x, Map()))
    assert(occurs(x, Pair(y, End), Map(y -> x)))
    assert(occurs(x, y, Map(y -> x)))
    assert(!occurs(x, z, Map(y -> x)))
    assert(occurs(x, Pair(y, Pair(z, End)), Map(y -> Pair(x, Pair(z, End)))))
  }

  test("extend substitution test") {
    assert(ext_s(x, Pair(x, End), Map()) === None)
    assert(ext_s(x, Pair(y, End), Map(y -> x)) === None)
    assert(ext_s(y, z, Map(x -> y)) === Some(Map(x -> y, y -> z)))
  }

  test("unify test") {
    assert(unify(x, y, Map()) === Some(Map(x -> y)))
    assert(unify(x, x, Map(y -> z)) === Some(Map(y -> z)))
    assert(unify(Lit("1"), Lit("1"), Map()) === Some(Map()))
    assert(unify(Lit("a"), Lit("b"), Map()) === None)
    assert(unify(x, Lit("7"), Map()) === Some(Map(x -> Lit("7"))))
    assert(unify(Lit("7"), x, Map()) === Some(Map(x -> Lit("7"))))

    assert(unify(Pair(x, Pair(y, End)), Pair(Lit("1"), Pair(Lit("2"), End)), Map()) === Some(Map(x -> Lit("1"), y -> Lit("2"))))
    assert(unify(Pair(x, Pair(y, End)), Pair(Lit("1"), Pair(x, End)), Map()) === Some(Map(x -> Lit("1"), y -> Lit("1"))))
    assert(unify(x, Pair(Lit("1"), Pair(Lit("2"), End)), Map()) === Some(Map(x -> Pair(Lit("1"), Pair(Lit("2"), End)))))
    assert(unify(x, Pair(Lit("2"), Pair(x, End)), Map()) === None)
    assert(unify(Pair(Lit("1"), Pair(x, Pair(Lit("3"), End))), Pair(Lit("1"), Pair(Lit("2"), Pair(y, End))), Map())
      === Some(Map(x -> Lit("2"), y -> Lit("3"))))
    assert(unify(Pair(x, Pair(y, End)), Pair(Lit("1"), Pair(Lit("2"), Pair(Lit("3"), End))), Map()) === None)
  }

  test("== test") {
    assert(Implementation.==(Lit("true"), Lit("false"))(Map()) === Implementation.fail(Map()))
    assert(Implementation.==(Lit("false"), Lit("false"))(Map()) === Implementation.succeed(Map()))
    assert(Implementation.==(x, y)(Map()) === Stream.cons(Map(x -> y), Empty))
    assert(Implementation.==(Pair(x, Lit("1")), Pair(x, z))(Map(x -> y))
      === Stream.cons(Map(x -> y, z -> Lit("1")), Empty))
  }

  test("append_inf test") {
    lazy val ones: Stream[Int] = Stream.cons(1, ones)
    lazy val twos: Stream[Int] = Stream.cons(2, twos)
    assert(append_inf(ones, twos).toString(3) == "Cons(1, Cons(1, Cons(1, ...)))")

//    lazy val abc = Stream.cons("a", Stream.cons("b", Stream.cons("c", Susp(() => Empty))))
//    assert(append_inf(abc, twos).toString(5) == "Cons(a, Cons(b, Cons(c, Cons(2, Cons(2, ...)))))")
  }

  test("conj2 test") {
    assert(conj2(Implementation.==(Lit("olive"), x), Implementation.==(Lit("olive"), x))(Map())
      === Stream.cons(Map(x -> Lit("olive")), Empty))
    assert(conj2(Implementation.==(Lit("olive"), x), Implementation.==(Lit("oil"), x))(Map())
      === Empty)
    assert(conj2(
      Implementation.==(Pair(Lit("2"), x), Pair(Lit("2"), Lit("3"))),
      Implementation.==(Pair(y, Lit("3")), Pair(Lit("2"), Lit("3"))))(Map())
      === Stream.cons(Map(x -> Lit("3"), y -> Lit("2")), Empty))
  }

  test("disj2 test") {
    assert(disj2(Implementation.==(Lit("olive"), x), Implementation.==(Lit("oil"), x))(Map())
      === Stream.cons(Map(x -> Lit("olive")), Stream.cons(Map(x -> Lit("oil")), Empty)))
    assert(disj2(Implementation.==(Lit("olive"), x), Implementation.==(Lit("oil"), x))(Map(x -> Lit("olive")))
      === Stream.cons(Map(x -> Lit("olive")), Empty))
  }

  test("take_inf test") {
    val disj = disj2(
      Implementation.==(Pair(Lit("olive"), y), Pair(x, Lit("apple"))),
      Implementation.==(Pair(Lit("oil"), y), Pair(x, Lit("panda"))))(Map())

    assert(take_inf(0, disj) === Empty)
    assert(take_inf(1, disj) === Stream.cons(Map(x -> Lit("olive"), y -> Lit("apple")), Empty))
    assert(take_inf(2, disj) === Stream.cons(Map(x -> Lit("olive"), y -> Lit("apple")), Stream.cons(Map(x -> Lit("oil"), y -> Lit("panda")), Empty)))
    assert(take_inf(42, disj) === Stream.cons(Map(x -> Lit("olive"), y -> Lit("apple")), Stream.cons(Map(x -> Lit("oil"), y -> Lit("panda")), Empty)))
    assert(take_inf(None, disj) === Stream.cons(Map(x -> Lit("olive"), y -> Lit("apple")), Stream.cons(Map(x -> Lit("oil"), y -> Lit("panda")), Empty)))
  }

  test("walk_star test") {
    assert(walk_star(y, Map(z -> Lit("a"), x -> Lit("w"), y -> z)) === Lit("a"))
    assert(walk_star(x, Map(y -> Lit("b"), z -> y, x -> Pair(y, Pair(Lit("e"), z))))
      === Pair(Lit("b"), Pair(Lit("e"), Lit("b"))))
    assert(walk_star(w, Map(x -> Pair(u, v), z -> y, w -> Pair(x, Pair(Lit("e"), z)), u -> Lit("c"), v -> Lit("q")))
      === Pair(Pair(Lit("c"), Lit("q")), Pair(Lit("e"), y)))
  }

  test("reify_s test") {
    assert(reify_s(x) === Map(x -> Lit("_0")))
    assert(reify_s(Pair(x, Pair(y, z))) === Map(x -> Lit("_0"), y -> Lit("_1"), z -> Lit("_2")))
  }

  test("reify test") {
    val a1 = Map(x -> Pair(u, Pair(w, Pair(y, Pair(z, Pair(Pair(Lit("ice"), End), z))))))
    val a2 = Map(y -> Lit("corn"))
    val a3 = Map(w -> Pair(v, u))
    val s = a1 ++ a2 ++ a3
    assert(reify(x)(s) === Pair(Lit("_0"), Pair(Pair(Lit("_1"), Lit("_0")), Pair(Lit("corn"), Pair(Lit("_2"), Pair(Pair(Lit("ice"), End), Lit("_2")))))))
  }

  test("ifte test") {
    assert(ifte(Implementation.succeed, Implementation.==(Lit("false"), y), Implementation.==(Lit("true"), y))(Map())
      === Stream.cons(Map(y -> Lit("false")), Empty))
    assert(ifte(Implementation.fail, Implementation.==(Lit("false"), y), Implementation.==(Lit("true"), y))(Map())
      === Stream.cons(Map(y -> Lit("true")), Empty))
    assert(ifte(Implementation.==(Lit("true"), x), Implementation.==(Lit("false"), y), Implementation.==(Lit("true"), y))(Map())
      === Stream.cons(Map(x -> Lit("true"), y -> Lit("false")), Empty))
    assert(ifte(
      disj2(Implementation.==(Lit("true"), x), Implementation.==(Lit("false"), x)),
      Implementation.==(Lit("false"), y),
      Implementation.==(Lit("true"), y))(Map())
      === Stream.cons(Map(x -> Lit("true"), y -> Lit("false")), Stream.cons(Map(x -> Lit("false"), y -> Lit("false")), Empty)))
  }

  test("once test") {
    assert(ifte(once(disj2(Implementation.==(Lit("true"), x), Implementation.==(Lit("false"), x))), Implementation.==(Lit("false"), y), Implementation.==(Lit("true"), y))(Map())
      === Stream.cons(Map(x -> Lit("true"), y -> Lit("false")), Empty))
  }

  test("disj test") {
    assert(disj(Implementation.==(Lit("olive"), x), Implementation.==(Lit("oil"), x), Implementation.==(Lit("feta"), x))(Map())
      === Stream.cons(Map(x -> Lit("olive")), Stream.cons(Map(x -> Lit("oil")), Stream.cons(Map(x -> Lit("feta")), Empty))))
  }

  test("conj test") {
    assert(conj(Implementation.==(Lit("olive"), x), Implementation.==(Lit("olive"), x), Implementation.==(Lit("olive"), x))(Map())
      === Stream.cons(Map(x -> Lit("olive")), Empty))
  }

  test("run_star test") {
    assert(run_star(v, Implementation.fail) === List())
    assert(run_star(v, Implementation.succeed) === List(Lit("_0")))
    assert(run_star(u, disj(Implementation.==(Lit("pea"), u), Implementation.==(Lit("pod"), u))) === List(Lit("pea"), Lit("pod")))
    assert(run_star(x, fresh(List(y), conj(Implementation.==(Lit("oil"), y), Implementation.==(x, y)))) === List(Lit("oil")))
    assert(run_star(List(x, y), Implementation.==(Lit("split"), x), Implementation.==(Lit("pea"), y))
      === List(Pair(Lit("split"), Pair(Lit("pea"), End))))
    assert(run_star(u, fresh(List(x, y), disj2(Implementation.==(Pair(x, y), u), Implementation.==(Pair(y, x), u))))
      === List(Pair(Lit("_0"), Lit("_1")), Pair(Lit("_0"), Lit("_1"))))

    val myGoal = disj2(
      conj2(Implementation.==(Lit("split"), x), Implementation.==(Lit("pea"), y)),
      conj2(Implementation.==(Lit("red"), x), Implementation.==(Lit("bean"), y)))

    assert(run_star(List(x, y), myGoal) === List(Pair(Lit("split"), Pair(Lit("pea"), End)), Pair(Lit("red"), Pair(Lit("bean"), End))))
    assert(Implementation.run(1, List(x, y), myGoal) === List(Pair(Lit("split"), Pair(Lit("pea"), End))))
  }

  test("conso test") {
    assert(run_star(x, conso(x, Pair(Lit("a"), Pair(Lit("b"), Lit("c"))), Pair(Lit("d"), Pair(Lit("a"), Pair(Lit("b"), Lit("c"))))))
      === List(Lit("d")))
    assert(run_star(x, conso(x, Pair(Lit("a"), Pair(x, Lit("c"))), Pair(Lit("d"), Pair(Lit("a"), Pair(x, Lit("c"))))))
      === List(Lit("d")))
  }

  test("nullo test") {
    assert(run_star(x, nullo(Pair(Lit("grape"), Pair(Lit("raisin"), Lit("pear"))))) === List())
    assert(run_star(x, nullo(End)) == List(Lit("_0")))
  }
}
