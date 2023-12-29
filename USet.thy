theory USet
    imports CvRDT HOL.Set HOL.Fun
begin

datatype 'a USet = USet "'a set"

definition "initial = USet Set.empty"

fun add :: "'a USet => 'a => 'a USet" where
  "add (USet s) e = USet (s \<union> {e})"

fun query :: "'a USet => 'a set" where
  "query (USet s) = s"

fun less_eq :: "'a USet => 'a USet => bool" where
    "less_eq (USet s1) (USet s2) = Set.subset_eq s1 s2"

fun less :: "'a USet => 'a USet => bool" where
    "less (USet s1) (USet s2) = Set.subset s1 s2"

fun merge :: "'a USet => 'a USet => 'a USet" where
    "merge (USet s1) (USet s2) = USet (s1 \<union> s2)"

(* USet properties *)

lemma query_contains_add: "e \<in> query (add s e)"
  apply (induct s)
  by auto

lemma add_creates_no_item: "\<not> a \<in> (query s) & \<not> (a = b) ==> \<not> a \<in> (query (add s b))"
  apply (induct s)
  by auto

lemma initial_contains_nothing: "\<not> e \<in> (query initial)"
  by (simp add: initial_def)

lemma updated_preserves_items: "e \<in> query s ==> e \<in> query (add s a)"
  apply (induct s)
  by auto

lemma merge_preserves_items: "e \<in> query a \<Longrightarrow> e \<in> query (merge a b)"
  apply (induct a)
  apply (induct b)
  by auto

lemma merge_creates_no_item: "\<not> e \<in> query a \<and> \<not> e \<in> query b \<Longrightarrow> \<not> e \<in> query (merge a b)"
  apply (induct a)
  apply (induct b)
  by auto

lemma merge_identity_right: "(e \<in> query a) = (e \<in> query (merge a initial))"
  unfolding initial_def
  apply (induct a)
  by auto

lemma merge_identity_left: "(e \<in> query a) = (e \<in> query (merge initial a))"
  unfolding initial_def
  apply (induct a)
  by auto

(* CvRDT properties *)

lemma less_eq_empty: "less_eq initial x"
  unfolding initial_def
  apply (induct x)
  by auto

lemma less_eq_reflexive: "less_eq x x"
  apply (induct x)
  by auto

lemma less_comb: "less x y = (less_eq x y & (~ less_eq y x))"
  apply (induct x)
  apply (induct y)
  by auto

lemma less_eq_transitive: "less_eq x y ==> less_eq y z ==> less_eq x z"
  apply (induct x)
  apply (induct y)
  apply (induct z)
  by auto

lemma less_eq_eq: "less_eq x y ==> less_eq y x ==> x = y"
  apply (induct x)
  apply (induct y)
  by auto

lemma less_eq_merge_left: "less_eq x (merge x y)"
  apply (induct x)
  apply (induct y)
  by auto

lemma less_eq_merge_right: "less_eq y (merge x y)"
  apply (induct x)
  apply (induct y)
  by auto

lemma less_eq_merge_count: "less_eq a c ==> less_eq b c ==> less_eq (merge a b) c"
  apply (induct a)
  apply (induct b)
  apply (induct c)
  by auto

lemma less_eq_add_monotonic: "less_eq a (add a u)"
  apply (induct a)
  by auto

(* USet methods *)

interpretation USetCvRDT : CvRDT
    USet.initial
    USet.less_eq
    USet.less
    USet.merge
    USet.query
    USet.add
proof
  show "\<And>x. USet.less_eq initial x"
    by (simp add:less_eq_empty)
  show "\<And>x. USet.less_eq x x"
    by (simp add:less_eq_reflexive)
  show "\<And>x y. USet.less x y = (USet.less_eq x y \<and> \<not> USet.less_eq y x)"
    by (simp add:less_comb)
  show "\<And>x y z.
       USet.less_eq x y \<Longrightarrow>
       USet.less_eq y z \<Longrightarrow> USet.less_eq x z"
    by (simp add:less_eq_transitive)
  show "\<And>x y. USet.less_eq x y \<Longrightarrow> USet.less_eq y x \<Longrightarrow> x = y"
    by (simp add:less_eq_eq)
  show "\<And>x y. USet.less_eq x (USet.merge x y)"
    by (simp add:less_eq_merge_left)
  show  "\<And>y x. USet.less_eq y (USet.merge x y)"
    by (simp add:less_eq_merge_right)
  show "\<And>y x z.
       USet.less_eq y x \<Longrightarrow>
       USet.less_eq z x \<Longrightarrow>
       USet.less_eq (USet.merge y z) x"
    by (simp add:less_eq_merge_count)
  show "\<And>a u. USet.less_eq a (add a u)"
    by (simp add:less_eq_add_monotonic)
qed

end