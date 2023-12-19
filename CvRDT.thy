theory CvRDT
    imports Main HOL.Lattices HOL.Orderings HOL.Set
begin

locale CvRDT = "'a" : Orderings.order + Lattices.semilattice_sup +
  fixes initial :: "'a"
    and query :: "'a => 'q"
    and update :: "'a => 'u => 'a"
  assumes monotonicity : "less_eq a (update a u)"

context CvRDT
begin

  fun merge :: "'a => 'a => 'a" where "merge a b = sup a b"

  lemma merge_associativity:
    shows "merge a (merge b c) = merge (merge a b) c"
    by (simp add: local.sup.assoc)

  lemma merge_commutativity:
    shows "merge a b = merge b a"
    by (simp add: local.sup.commute)

  lemma merge_idempotency:
    shows "merge a a = a"
    by simp
end
end