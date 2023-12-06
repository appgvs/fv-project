theory CvRDT
  imports Main
begin

class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

instantiation int :: semigroup
begin

definition
  "mult-int-def": "i \<otimes> j = i + (j::int)"

instance proof
  fix i j k :: int
  have "(i + j) + k = i + (j + k)" by simp
  then show "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
  unfolding "mult-int-def" .
qed
end
(*
locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<le>" 50)
  assumes refl [intro, simp]: "le x x"
    and trans [trans]: "le x y \<and> le y z \<Longrightarrow> le x z"
    and anti_sym [intro]: "le x y \<and> le y x \<Longrightarrow> x = y"

class cvrdt =
  fixes
    merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes associativity: "merge (merge a b) c = merge (merge a b) c"
      and commutativity: "merge a b = merge b a"
      and idempotency: "merge a a = a"

instantiation nat :: cvrdt
begin
definition "nat-cvrdt": "merge a b = (if (a > b) then a else b)"
instance proof
  sorry
end

end*)