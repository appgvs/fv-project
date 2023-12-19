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

fun less_eq :: "IntegerVector \<Rightarrow> IntegerVector \<Rightarrow> bool" where
  "less_eq [] _ = True" |
  "less_eq (0#xs) [] = less_eq xs []" |
  "less_eq (x#xs) [] = False" |
  "less_eq (x#xs) (y#ys) = ((x \<le> y) & less_eq xs ys)"

lemma less_eq_self : "less_eq x x"
  apply (induct x)
  apply (auto)
  done

fun less :: "IntegerVector \<Rightarrow> IntegerVector \<Rightarrow> bool" where
  "less _ []  = False" |
  "less [] (0#ys) = less [] ys" |
  "less [] (y#ys) = True" | 
  "less (x#xs) (y#ys) = (((x = y) & less xs ys) | ((x < y) & less_eq xs ys))"

lemma less_comb  : "less x y = (less_eq x y & (~less_eq y x))"
  apply (induction x arbitrary: y)
  by auto

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
      by (simp add: less_eq_self)
    show "\<And>x y. IntegerVector.less x y = (IntegerVector.less_eq x y \<and> \<not> IntegerVector.less_eq y x)"
      by (simp add: less_comb)
    show "\<And>x y z.
       IntegerVector.less_eq x y \<Longrightarrow>
       IntegerVector.less_eq y z \<Longrightarrow> IntegerVector.less_eq x z"
      sorry
    show "\<And>x y. IntegerVector.less_eq x y \<Longrightarrow>
           IntegerVector.less_eq y x \<Longrightarrow> x = y"
      sorry
    show "\<And>x y. IntegerVector.less_eq x (IntegerVector.max x y)"
      sorry
    show "\<And>y x. IntegerVector.less_eq y (IntegerVector.max x y)"
      sorry
    show "\<And>y x z.
       IntegerVector.less_eq y x \<Longrightarrow>
       IntegerVector.less_eq z x \<Longrightarrow>
       IntegerVector.less_eq (IntegerVector.max y z) x"
      sorry
    show "\<And>a u. IntegerVector.less_eq a (update a u)"
      sorry
qed
  
end
