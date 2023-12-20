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
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      apply(auto)
      done
  next
    case (Cons y ys)
    then show ?case
      apply(auto)
      done
  qed
qed

lemma less_eq_transitive: "less_eq x y \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq x z"
proof (induct x arbitrary: y z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (induct y arbitrary: z)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    then show ?case
    proof (induct z)
      case Nil
      then show ?case by simp
    next
      case (Cons z zs)
      then show ?case
        by (meson dual_order.trans less_eq.simps(3))
    qed
  qed
qed

fun less :: "IntegerVector => IntegerVector => bool" where
    "less _ [] = False" |
    "less [] (y#ys) = True" |
    "less (x#xs) (y#ys) = (((x < y) & less_eq xs ys) | ((x = y) & less xs ys))"

lemma less_comb : "less x y = (less_eq x y & (~less_eq y x))"
proof (induct x arbitrary: y)
  case Nil
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      apply (auto)
      done
  next
    case (Cons y ys)
    then show ?case
      apply (auto)
      done
  qed
next
  case (Cons x xs)
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      apply (auto)
      done
  next
    case (Cons y ys)
    then show ?case
      using less_eq.simps(3) less_eq_antisymmetry less_eq_reflexive nat_less_le by force
  qed
qed

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

(*lemma merge_non_empty_left: "a \<noteq> [] \<Longrightarrow> merge a b \<noteq> []"
proof (rule ccontr)
  assume "a \<noteq> []" and "merge a b = []"
  then obtain x xs where "a = x # xs" by (cases a, auto)
  then have "merge (x # xs) b \<noteq> []" by (cases b, simp_all)
  with `merge a b = []` show False by simp
qed*)

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
next
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

lemma merge_takes_greater: "merge (x#xs) (y#ys) = (if x > y then x#(merge xs ys) else y#(merge xs ys))"
  apply(induct x)
  apply (auto)
  done

lemma less_eq_non_empty:
  assumes "less_eq (x#xs) c"
  shows "\<exists> z zs. c = z # zs"
proof -
  from assms show ?thesis
  proof (cases c)
    case Nil
    then show ?thesis 
      using assms
      by (cases "x # xs", auto)
  next
    case (Cons z zs)
    then show ?thesis by auto
  qed
qed

lemma less_eq_merge_bound: "less_eq a c \<Longrightarrow> less_eq b c \<Longrightarrow> less_eq (merge a b) c"
proof (induct a arbitrary: b c)
  case Nil
  then show ?case
  proof -
    from merge_empty_left have "merge [] b = b" by simp
    then have "less_eq (merge [] b) c" using Nil.prems by simp
    then show ?thesis by assumption
  qed
next
  case (Cons x xs)
  then show ?case
  proof (induct b)
    case Nil
    then show ?case
      apply (auto)
      done
  next
  case (Cons y ys)
  from `less_eq (x # xs) c` obtain z zs where c_eq: "c = z # zs" using less_eq_non_empty by blast
  then show ?case
    proof (cases "x > y")
      case True
      with `less_eq (x # xs) c` c_eq have "x \<le> z" by (metis list.sel(1) less_eq.elims(3))
      moreover have xs_less_eq_zs: "less_eq xs zs" using `less_eq (x # xs) c` c_eq by (metis list.sel(3) less_eq.elims(3))
      moreover have y_ys_less_eq_c: "less_eq (y # ys) c" using `less_eq (y # ys) c`
        by simp
      then have ys_less_eq_zs: "less_eq ys zs" using c_eq
        by (metis list.sel(3) less_eq.elims(3))
      ultimately show ?thesis by (simp add: merge.simps less_eq.simps)
    next
      case False
      with `less_eq (y # ys) c` c_eq have "y \<le> z"
        by (metis list.sel(1) less_eq.elims(3))
      moreover have "less_eq (merge (x # xs) ys) zs" using Cons.hyps `less_eq (x # xs) c` by simp
      ultimately show ?thesis by (simp add: merge.simps less_eq.simps)
    qed
  qed
qed

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
