theory CvRDT
    imports Main HOL.Lattices HOL.Orderings HOL.Set
begin

locale CvRDT = "'a" : Orderings.order + Lattices.semilattice_sup +
  fixes initial :: "'a"
    and query :: "'a => 'q"
    and update :: "'a => 'u => 'a"
  assumes monotonicity : "less_eq a (update a u)"
begin
    fun merge :: "'a => 'a => 'a" where "merge a b = sup a b"
    lemma associativity: "merge a (merge b c) = merge (merge a b) c"
      sorry
    lemma commutativity: "merge a b = merge b a"
      sorry
    lemma idempotency: "merge a a = a"
      sorry
end

end