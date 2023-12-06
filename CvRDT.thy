theory CvRDT
  imports Main
begin

class cvrdt =
  fixes
    merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes associativity: "merge (merge a b) c = merge (merge a b) c"
      and commutativity: "merge a b = merge b a"
      and idempotency: "merge a a = a"

end
