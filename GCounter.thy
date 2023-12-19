theory GCounter
    imports CvRDT HOL.Map HOL.Set HOL.Option
begin

datatype 'id GCounter = GCounter "'id \<rightharpoonup> nat"

datatype 'id Increment = Index "'id"

fun current :: "'id GCounter => nat" where
    "current (GCounter vector) = \<Sum> (Map.ran vector)"

fun less_eq :: "'id GCounter => 'id GCounter => bool" where
  "less_eq (GCounter g1) (GCounter g2) ="


fun less :: "'id GCounter => 'id GCounter => bool" where
  (* TODO *)

fun update :: "'id GCounter => 'id Increment => 'id GCounter" where
  (* TODO *)

fun merge :: "'id GCounter => 'id GCounter => 'id GCounter" where
  (* TODO *)

end
