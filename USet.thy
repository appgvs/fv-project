theory USet
    imports CvRDT HOL.Set HOL.Fun
begin

datatype 'a USet = USet "'a set"

definition "initial = USet Set.empty"

fun add :: "'a USet => 'a => 'a USet" where
  "add (USet s) e = USet (s \<union> {e})"

fun elements :: "'a USet => 'a set" where
  "elements (USet s) = s"

fun subset_eq :: "'a USet => 'a USet => bool" where
    "subset_eq (USet s1) (USet s2) = Set.subset_eq s1 s2"

fun subset :: "'a USet => 'a USet => bool" where
    "subset (USet s1) (USet s2) = Set.subset s1 s2"

fun union :: "'a USet => 'a USet => 'a USet" where
    "union (USet s1) (USet s2) = USet (Set.union s1 s2)"


interpretation USetCvRDT : CvRDT
    USet.subset_eq
    USet.subset
    USet.union
    USet.initial
    USet.elements
    USet.add
proof
  show "\<And>x. USet.subset_eq x x"
    using subset_eq.elims(3) by fastforce
  show "\<And>x y. USet.subset x y = (USet.subset_eq x y \<and> \<not> USet.subset_eq y x)"
    by (metis elements.elims psubsetE psubsetI subset.simps subset_eq.simps)
  show "\<And>x y z.
       USet.subset_eq x y \<Longrightarrow>
       USet.subset_eq y z \<Longrightarrow> USet.subset_eq x z"
    by (metis USet.inject subset_eq subset_eq.elims(2) subset_eq.elims(3))
  show "\<And>x y. USet.subset_eq x y \<Longrightarrow>
           USet.subset_eq y x \<Longrightarrow> x = y"
    using subset_eq.elims(2) by fastforce
  show "\<And>x y. USet.subset_eq x (USet.union x y)"
    by (metis USet.exhaust Un_commute inf_sup_ord(4) subset_eq.simps union.simps)
  show  "\<And>y x. USet.subset_eq y (USet.union x y)"
    by (metis elements.simps inf_sup_ord(4) subset_eq.elims(3) union.elims)
  show "\<And>y x z.
       USet.subset_eq y x \<Longrightarrow>
       USet.subset_eq z x \<Longrightarrow>
       USet.subset_eq (USet.union y z) x"
    by (smt (verit, ccfv_threshold) elements.simps le_sup_iff subset_eq.elims(2) subset_eq.elims(3) union.elims)
  show "\<And>a u. USet.subset_eq a (add a u)"
    using subset_eq.elims(3) by fastforce
qed

export_code "USet" "initial" "add" "elements" in Scala
module_name "USet"

end