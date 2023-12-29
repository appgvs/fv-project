theory GCounter
    imports CvRDT IntegerVector
begin

datatype GCounter = GCounter "IntegerVector"
datatype Inc = Inc "nat"

definition "initial_counter = GCounter IntegerVector.initial"

fun listsum :: "nat list \<Rightarrow> nat" where
    "listsum [] = 0" |
    "listsum (x#xs) = x + listsum xs"

fun query :: "GCounter => nat" where
    "query (GCounter l) = listsum l"

fun merge :: "GCounter => GCounter => GCounter" where
    "merge (GCounter a) (GCounter b) = GCounter (IntegerVector.merge a b)"

fun update :: "GCounter => Inc => GCounter" where
    "update (GCounter l) (Inc n) = GCounter (IntegerVector.update l n)"

fun increment :: "GCounter \<Rightarrow> nat \<Rightarrow> GCounter" where
    "increment c n = update c (Inc n)"

fun less_eq :: "GCounter => GCounter => bool" where
    "less_eq (GCounter a) (GCounter b) = IntegerVector.less_eq a b"

fun less :: "GCounter => GCounter => bool" where
    "less (GCounter a) (GCounter b) = IntegerVector.less a b"

(* list lemmas *)

lemma listsum_empty: "listsum [] = 0"
  by auto

lemma listsum_singleton: "listsum [x] = x"
  by auto

lemma listsum_append: "listsum (xs @ ys) = listsum xs + listsum ys"
  apply (induct xs)
  apply (induct ys)
  by (auto)

lemma list_add_head: "listsum ((x+n)#xs) = n + listsum (x#xs)"
  apply (induct xs)
  by auto

lemma list_update_zero: "listsum (IntegerVector.update x 0) = 1 + listsum x"
  apply (induct x)
  by (auto)

lemma list_update_empty: "listsum (IntegerVector.update [] n) = 1"
  apply (induct n)
  by (auto)  

(* GCounter properties *)

lemma counter_less_eq_initial: "\<And>x. GCounter.less_eq initial_counter x"
  by (metis "IntVector2CvRDT.'a.bot.extremum" GCounter.inject GCounter.less_eq.elims(3) initial_counter_def)

lemma initial_counter_sum_zero: "query initial_counter = 0"
  unfolding initial_counter_def
  apply (auto)
  unfolding initial_def
  by auto

lemma update_listsum_suc: "listsum (IntegerVector.update xa m) = Suc (listsum xa) \<Longrightarrow> listsum (IntegerVector.update (a # xa) (Suc m)) = Suc (a + listsum xa)"
  by auto

lemma update_empty: "listsum (IntegerVector.update [] n) = 1"
  apply (auto)
  apply (induct n)
  by auto


(*lemma increment_adds_one_zo_sum: "query (increment x n) = 1 + (query x)"
proof (induct x arbitrary: n)
  case (GCounter xa)
  then show ?case
    apply (auto)
    proof (induct xa)
      case Nil
      then show ?case
        apply(auto)
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc m)
        then show ?case by auto
      qed
    next
      case (Cons a xa)
      then show ?case
        apply(auto)
      proof (induct n)
        case 0
        then show ?case
          by auto
      next
        case (Suc m)
        then show ?case
          sorry
      qed
    qed
qed*)
  

(* CvRDT interpretation *)

interpretation GCounterCvRDT : CvRDT
    GCounter.initial_counter
    GCounter.less_eq
    GCounter.less
    GCounter.merge
    GCounter.query
    GCounter.update
proof
  show "\<And>x. GCounter.less_eq initial_counter x"
    by (simp add: counter_less_eq_initial)
  show "\<And>x. GCounter.less_eq x x"
    using GCounter.less_eq.elims(1) by blast
  show "\<And>x y. GCounter.less x y = (GCounter.less_eq x y \<and> \<not> GCounter.less_eq y x)"
    by (metis "IntVector2CvRDT.'a.leD" "IntVector2CvRDT.'a.less_le" GCounter.exhaust GCounter.less.simps GCounter.less_eq.simps)
  show "\<And>x y z. GCounter.less_eq x y \<Longrightarrow> GCounter.less_eq y z \<Longrightarrow> GCounter.less_eq x z"
    by (metis "IntVector2CvRDT.'a.order.trans" GCounter.exhaust GCounter.inject GCounter.less_eq.elims(2) GCounter.less_eq.simps)
  show "\<And>x y. GCounter.less_eq x y \<Longrightarrow> GCounter.less_eq y x \<Longrightarrow> x = y"
    by (metis "IntVector2CvRDT.'a.order.antisym" GCounter.inject GCounter.less_eq.elims(2))
  show "\<And>x y. GCounter.less_eq x (GCounter.merge x y)"
    by (metis GCounter.less_eq.simps GCounter.merge.elims IntVector2CvRDT.le_sup_iff \<open>\<And>x. GCounter.less_eq x x\<close>)
  show "\<And>y x. GCounter.less_eq y (GCounter.merge x y)"
    by (metis GCounter.exhaust GCounter.merge.simps \<open>\<And>y x. GCounter.less_eq x (GCounter.merge x y)\<close> merge_commutativity)
  show "\<And>y x z. GCounter.less_eq y x \<Longrightarrow> GCounter.less_eq z x \<Longrightarrow> GCounter.less_eq (GCounter.merge y z) x"
    by (smt (verit, ccfv_SIG) GCounter.exhaust GCounter.less_eq.simps GCounter.merge.simps IntVector2CvRDT.le_sup_iff)
  show "\<And>a u. GCounter.less_eq a (GCounter.update a u)"
    by (metis GCounter.less_eq.simps GCounter.update.elims update_monotonicity)    
qed

end