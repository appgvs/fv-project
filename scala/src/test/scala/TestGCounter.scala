import scala.util.Random
import GCounter.*

class TestGCounter extends munit.FunSuite {
  private val MAX_VECTOR_SIZE = 4

  test("GCounter simple increment test") {
    val trace = (v => increment(v, intToNat(0))) :: Nil
    assertEquals(
      query(applyTrace(trace)),
      intToNat(1)
    )
  }

  test("GCounter simple merge test") {
    val trace =
      (
          v => merge(v, GCounterb(List(intToNat(0), intToNat(1), intToNat(1))))
      ) :: Nil

    assertEquals(
      query(applyTrace(trace)),
      intToNat(2)
    )
  }

  test("GCounter combined merge and increment test") {
    val merg = v => merge(v, GCounterb(List(intToNat(0), intToNat(1))))
    val inc = v => increment(v, intToNat(0))

    val exp = intToNat(2)
    assertEquals(
      query(applyTrace(List(inc, merg))),
      exp
    )

    // result should be the same if we swap the order of the trace
    assertEquals(
      query(applyTrace(List(merg, inc))),
      exp
    )
  }

  test("GCounter should be able to merge and update in any order") {
    val trace = getRandomTrace(size = 100)

    val results = for (_ <- 0 until 20) yield {
      val shuffled = Random.shuffle(trace)
      query(applyTrace(shuffled))
    }

    // all results should be the same at the end
    val exp = results.head
    for r <- results.tail do assertEquals(r, exp)
  }

  private def intToNat(i: Int): Nat.nat = {
    if (i == 0) Nat.zero_nat()
    else Nat.Suc(intToNat(i - 1))
  }

  private def getRandomNat(): Nat.nat =
    intToNat((Math.random() * MAX_VECTOR_SIZE).toInt)

  private def getRandomVector(nodeIdx: Int): GCountera =
    GCounterb(
      (0 until MAX_VECTOR_SIZE)
        // the vector we create should always have a value smaller or equal at the node we are testing
        .map(i => if nodeIdx == 0 then intToNat(0) else getRandomNat())
        .toList
    )

  private def getRandomTrace(
      testNodeIndex: Int = 0,
      size: Int = 10
  ): List[GCountera => GCountera] =
    val nodeIdx = intToNat(testNodeIndex)

    (0 until size)
      .map(_ => {
        if (Math.random() < 0.5) { (v: GCountera) =>
          {
            // a node can only increment its own value
            increment(v, nodeIdx)
          }

        } else {
          val randomV = getRandomVector(testNodeIndex)
          (v: GCountera) => {
            merge(v, randomV)
          }
        }
      })
      .toList

  private def applyTrace(trace: List[GCountera => GCountera]): GCountera =
    trace.foldLeft(initial_counter)((v, f) => f(v))
}
