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

end