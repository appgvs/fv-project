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
    "merge (USet s1) (USet s2) = USet (Set.union s1 s2)"

(* USet properties *)

lemma query_contains_add: "e \<in> query (add s e)"
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

(* USet methods *)

interpretation USetCvRDT : CvRDT
    USet.less_eq
    USet.less
    USet.merge
    USet.initial
    USet.query
    USet.add
proof
  show "\<And>x. USet.less_eq x x"
    using less_eq.elims(3) by fastforce
  show "\<And>x y. USet.less x y = (USet.less_eq x y \<and> \<not> USet.less_eq y x)"
    by (metis query.elims psubsetE psubsetI less.simps less_eq.simps)
  show "\<And>x y z.
       USet.less_eq x y \<Longrightarrow>
       USet.less_eq y z \<Longrightarrow> USet.less_eq x z"
    by (metis USet.inject subset_eq less_eq.elims(2) less_eq.elims(3))
  show "\<And>x y. USet.less_eq x y \<Longrightarrow>
           USet.less_eq y x \<Longrightarrow> x = y"
    using less_eq.elims(2) by fastforce
  show "\<And>x y. USet.less_eq x (USet.merge x y)"
    by (metis USet.exhaust Un_commute inf_sup_ord(4) less_eq.simps merge.simps)
  show  "\<And>y x. USet.less_eq y (USet.merge x y)"
    by (metis query.simps inf_sup_ord(4) less_eq.elims(3) merge.elims)
  show "\<And>y x z.
       USet.less_eq y x \<Longrightarrow>
       USet.less_eq z x \<Longrightarrow>
       USet.less_eq (USet.merge y z) x"
    by (smt (verit, ccfv_threshold) query.simps le_sup_iff less_eq.elims(2) less_eq.elims(3) merge.elims)
  show "\<And>a u. USet.less_eq a (add a u)"
    using less_eq.elims(3) by fastforce
qed

end