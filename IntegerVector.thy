theory IntegerVector
    imports CvRDT HOL.Map HOL.List
begin

type_synonym IntegerVector = "nat list"
type_synonym Update = "nat"

definition "initial = []"

fun current :: "IntegerVector => nat List.list" where
  "current xs = xs"

fun update :: "IntegerVector => Update => IntegerVector" where
  "update [] 0 = [1]" |
  "update [] n = 0#(update [] (n-1))" |
  "update (x#xs) 0 = (x+1)#xs" |
  "update (x#xs) n = x#(update xs (n-1))"

fun less :: "IntegerVector \<Rightarrow> IntegerVector \<Rightarrow> bool" where
  "less [] [] = True" |
  "less [] _  = True" | (* TODO: How to handle comp with empty list *) 
  "less _ []  = False" |
  "less (x#xs) (y#ys) = ((x < y) & less xs ys)"

fun less_eq :: "IntegerVector \<Rightarrow> IntegerVector \<Rightarrow> bool" where
  "less_eq [] [] = True" |
  "less_eq [] _  = True" | (* TODO: How to handle comp with empty list *) 
  "less_eq _ []  = False" |
  "less_eq (x#xs) (y#ys) = ((x \<le> y) & less_eq xs ys)"

fun max :: "IntegerVector \<Rightarrow> IntegerVector \<Rightarrow> IntegerVector" where
  "max [] xs = xs" |
  "max xs [] = xs" |
  "max (x#xs) (y#ys) = (if x > y then x else y)#max xs ys"
  
interpretation IntVectorCvRDT : CvRDT
  IntegerVector.less_eq
  IntegerVector.less
  IntegerVector.max
  IntegerVector.initial
  IntegerVector.current
  IntegerVector.update
proof
    show "\<And>x. IntegerVector.less_eq x x"
    show "\<And>x y. IntegerVector.less x y = (IntegerVector.less_eq x y \<and> \<not> IntegerVector.less_eq y x)"
    show "\<And>x y z.
       IntegerVector.less_eq x y \<Longrightarrow>
       IntegerVector.less_eq y z \<Longrightarrow> IntegerVector.less_eq x z"
    show "\<And>x y. IntegerVector.less_eq x y \<Longrightarrow>
           IntegerVector.less_eq y x \<Longrightarrow> x = y"
    show "\<And>x y. IntegerVector.less_eq x (IntegerVector.max x y)"
    show "\<And>y x. IntegerVector.less_eq y (IntegerVector.max x y)"
    show "\<And>y x z.
       IntegerVector.less_eq y x \<Longrightarrow>
       IntegerVector.less_eq z x \<Longrightarrow>
       IntegerVector.less_eq (IntegerVector.max y z) x"
    show "\<And>a u. IntegerVector.less_eq a (update a u)"
qed
  


end
