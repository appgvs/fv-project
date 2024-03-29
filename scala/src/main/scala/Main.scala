private def intToNat(i: Int): Nat.nat = {
  if (i == 0) Nat.zero_nat()
  else Nat.Suc(intToNat(i - 1))
}

@main def main: Unit =
  val vector = IntegerVector.initial[Nat.nat]
  println(
    IntegerVector.query(
      IntegerVector.update(vector, intToNat(0))
    )
  )

  val vector2 = IntegerVector.update(
    vector,
    intToNat(1)
  )
  println(
    IntegerVector.query(
      IntegerVector.merge(
        IntegerVector.update(vector, intToNat(0)),
        vector2
      )
    )
  )
