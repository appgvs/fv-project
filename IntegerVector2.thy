theory IntegerVector2
    imports CvRDT HOL.List
begin

type_synonym IntegerVector = "nat list"
type_synonym Update = "nat"

definition "initial = []"

fun query :: "IntegerVector => nat list" where
    "query xs = xs"

fun update :: "IntegerVector => Update => IntegerVector" where
    "update []      0 = [1]" |
    "update (x#xs)  0 = ((x+1)#xs)" |
    "update []      n = (0#(update [] (n-1)))" |
    "update (x#xs)  n = (x#(update xs (n-1)))"

fun less_eq :: "IntegerVector => IntegerVector => bool" where
    "less_eq [] _ = True" |
    "less_eq (x#xs) [] = False" |
    "less_eq (x#xs) (y#ys) = ((x \<le> y) & less_eq xs ys)"

lemma less_eq_reflexive : "less_eq x x"
  apply (induct x)
  apply (auto)
  done

lemma less_eq_transitive: "less_eq x y \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq x z"
proof (induct x arbitrary: y z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain ys zs where "y = x # ys" and "z = x # zs"
    using less_eq.elims(2) by blast
  with Cons have "less_eq xs ys" and "less_eq ys zs"
    by auto
  with Cons have "less_eq xs zs"
    by blast
  with `y = x # ys` `z = x # zs` Cons show ?case
    by auto
qed

fun less :: "IntegerVector => IntegerVector => bool" where
    "less _ [] = False" |
    "less [] (y#ys) = True" |
    "less (x#xs) (y#ys) = (((x < y) & less_eq xs ys) | ((x = y) & less xs ys))"

fun merge :: "IntegerVector => IntegerVector => IntegerVector" where
    "merge v1 [] = v1" |
    "merge [] v2 = v2" |
    "merge (x#xs) (y#ys) = ((if (x > y) then x else y) #(merge xs ys))"

interpretation IntVector2CvRDT : CvRDT
  IntegerVector2.less_eq
  IntegerVector2.less
  IntegerVector2.merge
  IntegerVector2.initial
  IntegerVector2.query
  IntegerVector2.update
proof
    show "\<And>x. IntegerVector2.less_eq x x"
      by (simp add: less_eq_reflexive)
    show "\<And>x y. IntegerVector2.less x y = (IntegerVector2.less_eq x y \<and> \<not> IntegerVector2.less_eq y x)"
      sorry
    show "\<And>x y z.
       IntegerVector2.less_eq x y \<Longrightarrow>
       IntegerVector2.less_eq y z \<Longrightarrow> IntegerVector2.less_eq x z"
      by (simp add: less_eq_transitive)
    show "\<And>x y. IntegerVector2.less_eq x y \<Longrightarrow>
           IntegerVector2.less_eq y x \<Longrightarrow> x = y"
      sorry
    show "\<And>x y. IntegerVector2.less_eq x (IntegerVector2.merge x y)"
      sorry
    show "\<And>y x. IntegerVector2.less_eq y (IntegerVector2.merge x y)"
      sorry
    show "\<And>y x z.
       IntegerVector2.less_eq y x \<Longrightarrow>
       IntegerVector2.less_eq z x \<Longrightarrow>
       IntegerVector2.less_eq (IntegerVector2.merge y z) x"
      sorry
    show "\<And>a u. IntegerVector2.less_eq a (update a u)"
      sorry
qed
end