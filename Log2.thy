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

fun query :: "'a Log \<Rightarrow> 'a Log" where
    "query s1 = s1"

(* Log partial order *)
fun less_eq :: "'a Log => 'a Log => bool" where
    "less_eq s1 s2 = USet.less_eq s1 s2"

fun less :: "'a Log => 'a Log => bool" where
    "less s1 s2 = USet.less s1 s2"

(* CvRDT proofs *)

lemma less_eq_reflexive: "less_eq x x" by simp

lemma less_eq_antisymmetric: "less_eq x y \<Longrightarrow> less_eq y x \<Longrightarrow> x = y" by simp

lemma less_eq_merge_left: "less_eq x (merge x y)" by simp

lemma less_eq_merge_right: "less_eq y (merge x y)" by simp

lemma less_eq_initial: "less_eq initial_log s"
  unfolding initial_log_def initial_def
  apply (auto)
  by (metis initial_def USet.less_eq_empty)

lemma less_less_eq: "less x y = (less_eq x y & ~(less_eq y x))"
  by auto

lemma less_eq_transitive: "less_eq x y \<Longrightarrow> less_eq y z \<Longrightarrow> less_eq x z"
  by auto

lemma less_eq_comb: "less_eq y x \<Longrightarrow> less_eq z x \<Longrightarrow> less_eq (merge y z) x"
  by simp

lemma insert_monotonic: "less_eq a (insert a u)"
  by (simp add: less_eq_add_monotonic)

interpretation Log2CvRDT : CvRDT
  Log2.initial_log
  Log2.less_eq
  Log2.less
  Log2.merge
  Log2.query
  Log2.insert
proof
  show "\<And> x. Log2.less_eq x x" by (metis less_eq_reflexive)
  show "\<And>x y. Log2.less x y = (Log2.less_eq x y \<and> \<not> Log2.less_eq y x)" by (metis less_less_eq)
  show "\<And>x y z. Log2.less_eq x y \<Longrightarrow> Log2.less_eq y z \<Longrightarrow> Log2.less_eq x z" by (metis less_eq_transitive)
  show "\<And>x y. Log2.less_eq x y \<Longrightarrow> Log2.less_eq y x \<Longrightarrow> x = y" by (metis less_eq_antisymmetric)
  show "\<And>a. Log2.less_eq initial_log a" by (metis less_eq_initial)
  show "\<And>x y. Log2.less_eq x (Log2.merge x y)" by (metis less_eq_merge_left)
  show "\<And>y x. Log2.less_eq y (Log2.merge x y)" by (metis less_eq_merge_right)
  show "\<And>y x z. Log2.less_eq y x \<Longrightarrow> Log2.less_eq z x \<Longrightarrow> Log2.less_eq (Log2.merge y z) x" by (metis less_eq_comb)
  show "\<And>a u. Log2.less_eq a (Log2.insert a u)" by (metis insert_monotonic)
  oops

end
