theory IntegerVector2
    imports CvRDT HOL.List
begin

type_synonym IntegerVector = "nat list"
type_synonym Update = "nat"

definition "initial = []"

fun query :: "IntegerVector => nat list" where
    "query xs = xs"

fun update :: "IntegerVector => Update => IntegerVector" where
    "update []      0 = [1]" |
    "update (x#xs)  0 = ((x+1)#xs)" |
    "update []      n = (0#(update [] (n-1)))" |
    "update (x#xs)  n = (x#(update xs (n-1)))"

fun less_eq :: "IntegerVector => IntegerVector => bool" where
    "less_eq [] _ = True" |
    "less_eq (x#xs) [] = False" |
    "less_eq (x#xs) (y#ys) = ((x \<le> y) & less_eq xs ys)"

fun less :: "IntegerVector => IntegerVector => bool" where
    "less _ [] = False" |
    "less [] (y#ys) = True" |
    "less (x#xs) (y#ys) = (((x < y) & less_eq xs ys) | ((x = y) & less xs ys))"

fun merge :: "IntegerVector => IntegerVector => IntegerVector" where
    "merge v1 [] = v1" |
    "merge [] v2 = v2" |
    "merge (x#xs) (y#ys) = ((if (x > y) then x else y) #(merge xs ys))"

end