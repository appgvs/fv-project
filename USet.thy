theory USet
    imports CvRDT HOL.Set HOL.Fun
begin

datatype 'a USet = USet "'a set"

definition "initial = USet Set.empty"

fun add :: "'a USet => 'a => 'a USet" where
  "add (USet s) e = USet (s \<union> {e})"

fun elements :: "'a USet => 'a set" where
  "elements (USet s) = s"

fun identity :: "'a => 'a" where
    "identity x = x"

fun add_to_set :: "'a set => 'a => 'a set" where
    "add_to_set all e = all \<union> {e}"

fun subset_eq :: "'a USet => 'a USet => bool" where
    "subset_eq (USet s1) (USet s2) = Set.subset_eq s1 s2"

fun subset :: "'a USet => 'a USet => bool" where
    "subset (USet s1) (USet s2) = Set.subset s1 s2"

fun union :: "'a USet => 'a USet => 'a USet" where
    "union (USet s1) (USet s2) = USet (Set.union s1 s2)"


interpretation uset_cvrdt : CvRDT
    USet.subset_eq
    USet.subset
    USet.union
    USet.initial
    Fun.id
    USet.add
proof
    (*show "\<And>a u. a \<subseteq> add_to_set a u" by auto*)
qed

end