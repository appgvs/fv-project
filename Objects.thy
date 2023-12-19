theory Objects
    imports Main HOL.Lattices HOL.Orderings HOL.Set
begin

locale mycvrdt = "'a" : Orderings.order + Lattices.semilattice_sup +
  fixes initial :: "'a"
    and query :: "'a => 'q"
    and update :: "'a => 'u => 'a"
  assumes monotonicity : "less_eq a (update a u)"
begin
    fun merge :: "'a => 'a => 'a" where "merge a b = sup a b"
end


(*locale cvrdt =
  fixes initial :: "'s"
    and query :: "'s => 'q"
    and update :: "'s => 'u => 's"
    and merge :: "'s => 's => 's"
    and order :: "'s => 's => bool"

  assumes associativity: "merge (merge a b) c = merge a (merge b c)"
      and commutativity: "merge a b = merge b a"
      and idempotency: "merge a a = a"

      and monotonicity : "order s (update s u) = true"
*)
end