theory PNSet
    imports CvRDT HOL.Set HOL.Fun
begin

(* Datatypes definitions *)
datatype 'a PNSet = PNSet "'a set" "'a set"
datatype 'a PNSetUpdate = Add "'a" | Remove "'a"

(* CvRDT methods definitions *)
definition "initial = PNSet Set.empty Set.empty"

fun update :: "'a PNSet => 'a PNSetUpdate => 'a PNSet" where
    "update (PNSet a r) (Add e) = PNSet (a \<union> {e}) r" |
    "update (PNSet a r) (Remove e) = PNSet (a \<union> {e}) (r \<union> {e})"

fun add :: "'a PNSet => 'a => 'a PNSet" where
    "add pnset e = update pnset (Add e)"

fun remove :: "'a PNSet => 'a => 'a PNSet" where
    "remove pnset e = update pnset (Remove e)"

fun query :: "'a PNSet => 'a set" where
    "query (PNSet a r) = a - r"

fun merge :: "'a PNSet => 'a PNSet => 'a PNSet" where
    "merge (PNSet a1 r1) (PNSet a2 r2) = PNSet (Set.union a1 a2) (Set.union r1 r2)"

(* PNSet partial order *)
fun less_eq :: "'a PNSet => 'a PNSet => bool" where
    "less_eq (PNSet a1 r1) (PNSet a2 r2) = (Set.subset_eq a1 a2 & Set.subset_eq r1 r2)"

fun less :: "'a PNSet => 'a PNSet => bool" where
    "less (PNSet a1 r1) (PNSet a2 r2) = (
        (Set.subset a1 a2 & Set.subset_eq r1 r2) |
        (Set.subset_eq a1 a2 & Set.subset r1 r2)
    )"

(* PNSet properties *)

lemma initial_contains_nothing: "\<not> e \<in> (query initial)"
  by (simp add: initial_def)

lemma initial_add_contains_element: "e \<in> query (add initial e)"
  by (simp add: initial_def)

lemma merge_keep_common_items: "e \<in> query a \<and> e \<in> query b \<Longrightarrow> e \<in> query (merge a b)"
  apply (induct a)
  apply (induct b)
  by auto

lemma merge_creates_no_item: "\<not> e \<in> query a \<and> \<not> e \<in> query b \<Longrightarrow> \<not> e \<in> query (merge a b)"
  apply (induct a)
  apply (induct b)
  by auto

lemma add_remove_commutative: "remove (add s a) a = add (remove s a) a"
  apply (induct s)
  by auto

lemma merge_preserves_removals: "\<not> e \<in> query (merge (remove s e) x)"
  apply (induct s)
  apply (induct x)
  by auto

(* PNSet lemmas *)

lemma less_eq_reflexive: "less_eq x x"
  using less_eq.elims(3) by fastforce

(* Interpretation of PNSet as a CvRDT *)
interpretation PNSetCvRDT : CvRDT
    PNSet.less_eq
    PNSet.less
    PNSet.merge
    PNSet.initial
    PNSet.query
    PNSet.update
proof
    show "\<And>x. PNSet.less_eq x x"
      using less_eq.elims(3) by fastforce
    show "\<And>x y. PNSet.less x y = (PNSet.less_eq x y \<and> \<not> PNSet.less_eq y x)"
      by (smt (z3) order.preordering_axioms preordering.strict_iff_not less.elims(1) less_eq.simps)
    show "\<And>x y z.
       PNSet.less_eq x y \<Longrightarrow>
       PNSet.less_eq y z \<Longrightarrow> PNSet.less_eq x z"
      by (smt (verit, best) PNSet.inject less_eq.elims(1) subset_trans)
    show "\<And>x y. PNSet.less_eq x y \<Longrightarrow>
           PNSet.less_eq y x \<Longrightarrow> x = y"
      using less_eq.elims(2) by fastforce
    show "\<And>x y. PNSet.less_eq x (PNSet.merge x y)"
      by (smt (verit, del_insts) PNSet.inject UnCI subsetI less_eq.elims(3) merge.elims)
    show "\<And>y x. PNSet.less_eq y (PNSet.merge x y)"
      by (smt (verit, del_insts) PNSet.inject UnCI \<open>\<And>y x. PNSet.less_eq x (PNSet.merge x y)\<close> subsetI less_eq.elims(2) less_eq.elims(3) merge.simps)
    show "\<And>y x z.
       PNSet.less_eq y x \<Longrightarrow>
       PNSet.less_eq z x \<Longrightarrow>
       PNSet.less_eq (PNSet.merge y z) x"
      by (smt (verit, del_insts) PNSet.inject Un_subset_iff less_eq.elims(2) less_eq.elims(3) merge.simps)
    show "\<And>a u. PNSet.less_eq a (update a u)"
      by (metis PNSet.exhaust PNSetUpdate.exhaust \<open>\<And>x. PNSet.less_eq x x\<close> le_sup_iff less_eq.simps update.simps(1) update.simps(2))
qed

end