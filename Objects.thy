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

datatype 'a USet = USet "'a set"

fun uset_add :: "'a USet => 'a => 'a USet" where
  "uset_add (USet s) e = USet (s \<union> {e})"
fun uset_value :: "'a USet => 'a set" where
  "uset_value (USet s) = s"

fun identity :: "'a => 'a" where
    "identity x = x"

fun add_to_set :: "'a set => 'a => 'a set" where
    "add_to_set all e = all \<union> {e}"

interpretation uset_cvrdt : mycvrdt
    Set.subset_eq
    Set.subset
    Set.union
    Set.empty
    identity
    add_to_set
proof
    show "\<And>a u. a \<subseteq> add_to_set a u" by auto
qed

instantiation USet :: (type) mycvrdt
begin
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