theory CvRDT
  imports Main
begin

class cvrdt =
  fixes
    merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes associativity: "merge (merge a b) c = merge a (merge b c)"
      and commutativity: "merge a b = merge b a"
      and idempotency: "merge a a = a"

instantiation int :: cvrdt
begin

definition "merge-int" : "merge a b = (if (a::int) > (b::int) then a else b)"
instance proof
  fix a b c :: int
  show "merge a b = merge b a"
    using "merge-int" by auto
  then show "merge a a = a"
    using "merge-int" by auto
  then show "merge (merge a b) c = merge a (merge b c)"
    by (simp add: "merge-int")
qed

export_code "merge" in Scala
  module_name "CvRDT"

end