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

end
