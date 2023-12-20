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

lemma less_eq_antisymmetry: "less_eq x y \<Longrightarrow> less_eq y x \<Longrightarrow> x = y"
proof (induct x arbitrary: y)
  case Nil
  then show ?case 
    using less_eq.elims(2) by auto
next
  case (Cons x xs)
  then obtain ys where "y = x # ys"
    using less_eq.elims(2) by blast
  with Cons have "less_eq xs ys" and "less_eq ys xs"
    by auto
  with `y = x # ys` Cons show ?case
    by auto
qed

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

lemma less_comb  : "less x y = (less_eq x y & (~less_eq y x))"
  apply (induct x arbitrary: y)
  by auto

fun merge :: "IntegerVector => IntegerVector => IntegerVector" where
    "merge v1 [] = v1" |
    "merge [] v2 = v2" |
    "merge (x#xs) (y#ys) = ((if (x > y) then x else y) #(merge xs ys))"

lemma less_eq_merge_left: "less_eq x (merge x y)"
proof (induct y arbitrary: x)
  case Nil
  then show ?case
    apply (auto)
    by (simp add: less_eq_reflexive)
next
  case (Cons a y)
  then show ?case
  proof (induct x)
    case Nil
    then show ?case
      apply (auto)
      done
  next
    case (Cons x xs)
    then show ?case
      apply (auto)
      done
  qed
qed

lemma merge_empty_left : "merge [] y = y"
  apply (induct y)
  apply (auto)
  done

lemma merge_empty_right : "merge x [] = x"
  apply (induct x)
  apply (auto)
  done

lemma merge_commutativity : "merge x y  = merge y x"
proof (induct x arbitrary: y)
  case Nil
  then show ?case
    apply (auto)
    apply (simp add: merge_empty_left)
    done
  case (Cons a as)
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      apply (auto)
      done
    case (Cons b bs)
    then show ?case
      apply (auto)
      done
  qed
qed

lemma less_eq_merge_right: "less_eq y (merge x y)"
proof -
  have merge_comm: "merge x y = merge y x" by (rule merge_commutativity)
  then have "less_eq y (merge y x)" using less_eq_merge_left by simp
  then show "less_eq y (merge x y)" using merge_comm by simp
qed

lemma less_eq_merge_bound: "less_eq a c \<Longrightarrow> less_eq b c \<Longrightarrow> less_eq (merge a b) c"
  sorry

lemma update_monotonicity: "less_eq a (update a u)"
proof (induct a arbitrary: u)
  case Nil
  then show ?case
    apply (auto)
    done
  case (Cons x xs)
  then show ?case
  proof (cases u)
    case 0
    then show ?thesis
      apply (auto)
      apply (simp add: less_eq_reflexive)
      done
  next
    case (Suc n)
    then show ?thesis
      apply (auto) using Cons.hyps less_eq.simps(3) by blast
  qed
qed

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
      by (simp add: less_comb)
    show "\<And>x y z.
       IntegerVector2.less_eq x y \<Longrightarrow>
       IntegerVector2.less_eq y z \<Longrightarrow> IntegerVector2.less_eq x z"
      by (simp add: less_eq_transitive)
    show "\<And>x y. IntegerVector2.less_eq x y \<Longrightarrow>
           IntegerVector2.less_eq y x \<Longrightarrow> x = y"
      by (simp add: less_eq_antisymmetry)
    show "\<And>x y. IntegerVector2.less_eq x (IntegerVector2.merge x y)"
      by (simp add: less_eq_merge_left)
    show "\<And>y x. IntegerVector2.less_eq y (IntegerVector2.merge x y)"
      by (simp add: less_eq_merge_right)
    show "\<And>y x z.
       IntegerVector2.less_eq y x \<Longrightarrow>
       IntegerVector2.less_eq z x \<Longrightarrow>
       IntegerVector2.less_eq (IntegerVector2.merge y z) x"
      by (simp add: less_eq_merge_bound)
    show "\<And>a u. IntegerVector2.less_eq a (update a u)"
      by (simp add: update_monotonicity)
qed
end