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

lemma update_singleton: "listsum (IntegerVector.update [] b) = 1"
  apply (induct b)
  by auto

lemma listsum_head: "listsum (x # xs) = x + listsum xs"
  apply (induct xs)
  by (auto)

lemma listsum_append: "listsum (xs @ ys) = listsum xs + listsum ys"
  apply (induct xs)
  apply (induct ys)
  by (auto)

lemma list_add_head: "listsum ((x+n)#xs) = n + listsum (x#xs)"
  apply (induct xs)
  by auto

lemma listsum_update_nil: "listsum (IntegerVector.update [] n) = Suc 0"
  apply (induct n)
  by auto

lemma list_update_zero: "listsum (IntegerVector.update x 0) = 1 + listsum x"
  apply (induct x)
  by (auto)

lemma listsum_pos: "listsum (IntegerVector.update xs a) = listsum (IntegerVector.update xs b)"
proof (induct xs arbitrary: a b)
case Nil
then show ?case by (metis listsum_update_nil)
next
case (Cons y ys)
then show ?case
  proof (induct a arbitrary: b)
  case 0
  then show ?case
    proof (induct b)
      case 0
      then show ?case by auto
    next
      case (Suc bs)
      then show ?case
        proof -
          have forward: "listsum (IntegerVector.update (y # ys) 0) = listsum ((y+1)#ys)" by auto
          then have "listsum ((y+1)#ys) = 1 + y + listsum ys" by auto

          have backward: "listsum (IntegerVector.update (y # ys) (Suc bs)) = listsum (y#(IntegerVector.update ys bs))" by auto
          then have "listsum (y#(IntegerVector.update ys bs)) = y + listsum (IntegerVector.update ys bs)" using listsum_head by blast
          then have "y + listsum (IntegerVector.update ys bs) = y + (1 + listsum ys)" by (metis list_update_zero local.Cons)
          then have "y + (1 + listsum ys) = 1 + y + listsum ys" by simp

          show "listsum (IntegerVector.update (y # ys) 0) = listsum (IntegerVector.update (y # ys) (Suc bs))"
            by (simp add: \<open>y + listsum (IntegerVector.update ys bs) = y + (1 + listsum ys)\<close>)
        qed
    qed
  next
  case (Suc as)
  then show ?case
    proof (induct b)
    case 0
      then show ?case
        proof -
          have forward: "listsum (IntegerVector.update (y # ys) (Suc as)) = listsum (y#(IntegerVector.update ys as))" by auto
          then have "listsum (y#(IntegerVector.update ys as)) = listsum (y#(IntegerVector.update ys 0))" by (simp add: local.Cons)
          then have "listsum (y#(IntegerVector.update ys 0)) = y + listsum (IntegerVector.update ys 0)" by simp
          then have "y + listsum (IntegerVector.update ys 0) = y + 1 + listsum ys" by (simp add: list_update_zero)

          have backward: "listsum (IntegerVector.update (y # ys) 0) = listsum ((y+1)#ys)" by auto
          then have "listsum ((y+1)#ys) = y + 1 + listsum ys" by simp

          show "listsum (IntegerVector.update (y # ys) (Suc as)) = listsum (IntegerVector.update (y # ys) 0)" by (metis Suc.hyps local.Cons)
      qed
    next
    case (Suc bs)
      then show ?case
        proof -
          have forward: "listsum (IntegerVector.update (y # ys) (Suc as)) = listsum (y#(IntegerVector.update ys as))" by auto
          then have "listsum (y#(IntegerVector.update ys as)) = y + listsum (IntegerVector.update ys as)" by auto
          then have "y + listsum (IntegerVector.update ys as) = y + listsum (IntegerVector.update ys 0)" using local.Cons by auto

          have backward: "listsum (IntegerVector.update (y # ys) (Suc bs)) = listsum (y#(IntegerVector.update ys bs))" by auto
          then have "listsum (y#(IntegerVector.update ys bs)) = y + listsum (IntegerVector.update ys bs)" by auto
          then have "y + listsum (IntegerVector.update ys bs) = y + listsum (IntegerVector.update ys 0)" using local.Cons by auto

          show "listsum (IntegerVector.update (y # ys) (Suc as)) = listsum (IntegerVector.update (y # ys) (Suc bs))" using local.Cons by auto
        qed
    qed
  qed
qed

lemma listsum_update_insert: "listsum (y # (IntegerVector.update ys n)) = listsum (IntegerVector.update (y#ys) n)"
proof (induct ys)
case Nil
then show ?case
  proof -
    have forward: "listsum (y # IntegerVector.update [] n) = y + listsum (IntegerVector.update [] n)" by (metis listsum_head)
    then have "y + listsum (IntegerVector.update [] n) = y + (Suc 0)" by (metis listsum_update_nil)
    then have "y + (Suc 0) = y + 1" by auto

    have backward: "listsum (IntegerVector.update [y] n) = listsum (IntegerVector.update [y] 0)" by (metis listsum_pos)
    then have "listsum (IntegerVector.update [y] 0) = listsum ((y+1)#Nil)" by auto
    then have "listsum ((y+1)#Nil) = y + 1" by auto

    show "listsum (y # IntegerVector.update [] n) = listsum (IntegerVector.update [y] n)" by (simp add: update_singleton forward backward)
  qed
case (Cons x xs)
then show ?case by (metis IntegerVector.update.simps(4) diff_Suc_1 listsum_pos)
qed

lemma "listsum (y # (IntegerVector.update ys n)) = listsum (IntegerVector.update (y#ys) n)"
proof -
(*listsum (y # IntegerVector.update ys n) = listsum (IntegerVector.update (y # ys) n)*)
have forward: "listsum (y # IntegerVector.update ys n) = y + listsum (IntegerVector.update ys n)" by (metis listsum_head)

oops

lemma list_update_any: "listsum (IntegerVector.update x n) = 1 + listsum x"
proof (induct x arbitrary: n)
case Nil
then show ?case
  apply (auto)
  by (metis listsum_update_nil)
next
case (Cons y ys)
then show ?case
  proof (induct n)
  case 0
  then show ?case by auto
  next
  case (Suc nx)
  then show ?case
    proof - 
      have "listsum (IntegerVector.update (y # ys) (Suc nx)) = listsum (y#(IntegerVector.update ys nx))" by auto
      then have "listsum (y#(IntegerVector.update ys nx)) = y + listsum (IntegerVector.update ys nx)" by (metis listsum_head)
      then have "y + listsum (IntegerVector.update ys nx) = y + 1 + listsum ys" by (simp add: local.Cons)
      then have "y + 1 + listsum ys = 1 + y + listsum ys" by simp
      then have "1 + y + listsum ys = 1 + (listsum (y#ys))" by simp
      show "listsum (IntegerVector.update (y # ys) (Suc nx)) = 1 + listsum (y # ys)" by (metis list_update_zero listsum_pos) 
    qed
  qed
qed

lemma listsum_update: "listsum (x # (IntegerVector.update xs n)) = listsum (IntegerVector.update (x#xs) n)"
proof (induct n)
  case 0
  then show ?case
    apply (auto)
    apply (induct xs)
    by (auto)
next
  case (Suc n)
  then show ?case
    by (metis listsum_head listsum_pos)
qed

lemma list_update_empty: "listsum (IntegerVector.update [] n) = 1"
  apply (induct n)
  by (auto)  

(* GCounter properties *)

lemma counter_less_eq_initial: "\<And>x. GCounter.less_eq initial_counter x"
  unfolding initial_counter_def initial_def
  using GCounter.less_eq.elims(3) by fastforce

lemma initial_counter_sum_zero: "query initial_counter = 0"
  unfolding initial_counter_def initial_def
  by auto

lemma update_listsum_suc: "listsum (IntegerVector.update xa m) = Suc (listsum xa) \<Longrightarrow> listsum (IntegerVector.update (a # xa) (Suc m)) = Suc (a + listsum xa)"
  by auto

lemma update_empty: "listsum (IntegerVector.update [] n) = Suc 0"
  apply (induct n)
  by auto

lemma increment_adds_one: "query (increment x n) = 1 + (query x)"
proof (induct x arbitrary: n)
  case (GCounter vec)
  then show ?case
    apply (auto)
    proof (induct vec)
    case Nil
      then show ?case
        apply (induct n)
        apply (auto)
        done
    next
    case (Cons x xs)
      then show ?case
        proof -
          assume a: "listsum (IntegerVector.update xs n) = Suc (listsum xs)"
          then have "x + listsum (IntegerVector.update xs n) = x + Suc (listsum xs)" by simp
          then have "x + listsum (IntegerVector.update xs n) = Suc (x + listsum xs)" by simp
          then have "listsum (x # (IntegerVector.update xs n)) = Suc (listsum (x # xs))" by simp
          then have res: "listsum (IntegerVector.update (x # xs) n) = Suc (listsum (x # xs))" by (metis listsum_update)
          from a res show "listsum (IntegerVector.update (x # xs) n) = Suc (listsum (x # xs))" by auto
      qed
    qed
  qed


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