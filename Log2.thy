theory Log2
    imports CvRDT USet HOL.List
begin

(* Datatypes definitions. *)
type_synonym 'a LogUpdate = "'a"
type_synonym 'a LogEvent = "('a * nat)"
type_synonym 'a Log = "'a LogEvent USet"

(* CvRDT methods definitions. *)

definition "initial_log = USet.initial"

fun max_timestamp :: "'a Log => nat" where
    "max_timestamp s = Max (snd ` (USet.query s))"

fun insert :: "'a Log => 'a LogUpdate => 'a Log" where
    "insert log e = USet.add log (e, max_timestamp log + 1)"

fun merge :: "'a Log => 'a Log => 'a Log" where
    "merge s1 s2 = USet.merge s1 s2"

(* Log partial order *)
fun less_eq :: "'a Log => 'a Log => bool" where
    "less_eq s1 s2 = USet.less_eq s1 s2"

fun less :: "'a Log => 'a Log => bool" where
    "less s1 s2 = USet.less s1 s2"

end
