theory PNSet
    imports CvRDT HOL.Set HOL.Fun
begin

datatype 'a PNSet = PNSet "'a set" "'a set"
datatype 'a PNSetUpdate = Add "'a" | Remove "'a"

definition "initial = PNSet Set.empty Set.empty"

fun update :: "'a PNSet => 'a PNSetUpdate => 'a PNSet" where
    "update (PNSet a r) (Add e) = PNSet (a \<union> {e}) r" |
    "update (PNSet a r) (Remove e) = PNSet (a \<union> {e}) (r \<union> {e})"

fun add :: "'a PNSet => 'a => 'a PNSet" where
    "add pnset e = update pnset (Add e)"

fun remove :: "'a PNSet => 'a => 'a PNSet" where
    "remove pnset e = update pnset (Remove e)"

fun elements :: "'a PNSet => 'a set" where
    "elements (PNSet a r) = a - r"

fun subset_eq :: "'a PNSet => 'a PNSet => bool" where
    "subset_eq (PNSet a1 r1) (PNSet a2 r2) = (Set.subset_eq a1 a2 & Set.subset_eq r1 r2)"

fun subset :: "'a PNSet => 'a PNSet => bool" where
    "subset (PNSet a1 r1) (PNSet a2 r2) = (Set.subset a1 a2 & Set.subset r1 r2)"

fun union :: "'a PNSet => 'a PNSet => 'a PNSet" where
    "union (PNSet a1 r1) (PNSet a2 r2) = PNSet (Set.union a1 a2) (Set.union r1 r2)"

interpretation PNSetCvRDT : CvRDT
    PNSet.subset_eq
    PNSet.subset
    PNSet.union
    PNSet.initial
    PNSet.elements
    PNSet.update
proof
    show "\<And>x. PNSet.subset_eq x x"
      using subset_eq.elims(3) by fastforce
(*    show "\<And>x y. PNSet.subset x y = (PNSet.subset_eq x y \<and> \<not> PNSet.subset_eq y x)"*)

    show "\<And>x y z.
       PNSet.subset_eq x y \<Longrightarrow>
       PNSet.subset_eq y z \<Longrightarrow> PNSet.subset_eq x z"
      by (smt (verit, best) PNSet.inject subset_eq.elims(1) subset_trans)
    show "\<And>x y. PNSet.subset_eq x y \<Longrightarrow>
           PNSet.subset_eq y x \<Longrightarrow> x = y"
      using subset_eq.elims(2) by fastforce
    show "\<And>x y. PNSet.subset_eq x (PNSet.union x y)"
      by (smt (verit, del_insts) PNSet.inject UnCI subsetI subset_eq.elims(3) union.elims)
    show "\<And>y x. PNSet.subset_eq y (PNSet.union x y)"
      by (smt (verit, del_insts) PNSet.inject UnCI \<open>\<And>y x. PNSet.subset_eq x (PNSet.union x y)\<close> subsetI subset_eq.elims(2) subset_eq.elims(3) union.simps)
    show "\<And>y x z.
       PNSet.subset_eq y x \<Longrightarrow>
       PNSet.subset_eq z x \<Longrightarrow>
       PNSet.subset_eq (PNSet.union y z) x"
      by (smt (verit, del_insts) PNSet.inject Un_subset_iff subset_eq.elims(2) subset_eq.elims(3) union.simps)
    show "\<And>a u. PNSet.subset_eq a (update a u)"
      by (metis PNSet.exhaust PNSetUpdate.exhaust \<open>\<And>x. PNSet.subset_eq x x\<close> le_sup_iff subset_eq.simps update.simps(1) update.simps(2))
qed

end