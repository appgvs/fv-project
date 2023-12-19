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
    show "\<And>x y. PNSet.subset x y = (PNSet.subset_eq x y \<and> \<not> PNSet.subset_eq y x)"
    show "\<And>x y z.
       PNSet.subset_eq x y \<Longrightarrow>
       PNSet.subset_eq y z \<Longrightarrow> PNSet.subset_eq x z"
    show "\<And>x y. PNSet.subset_eq x y \<Longrightarrow>
           PNSet.subset_eq y x \<Longrightarrow> x = y"
    show "\<And>x y. PNSet.subset_eq x (PNSet.union x y)"
    show "\<And>y x. PNSet.subset_eq y (PNSet.union x y)"
    show "\<And>y x z.
       PNSet.subset_eq y x \<Longrightarrow>
       PNSet.subset_eq z x \<Longrightarrow>
       PNSet.subset_eq (PNSet.union y z) x"
    show "\<And>a u. PNSet.subset_eq a (add a u)"
qed

end