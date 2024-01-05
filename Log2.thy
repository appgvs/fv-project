theory Log2
  imports
    CvRDT
    USet
    HOL.List
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
    "insert l e = USet.add l (e, max_timestamp l + 1)"

fun merge :: "'a Log => 'a Log => 'a Log" where
    "merge s1 s2 = USet.merge s1 s2"

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma set_set_to_list: "finite s \<Longrightarrow> set (set_to_list s) = s"
  by (metis (mono_tags, lifting) finite_list set_to_list_def someI)

fun less_event :: "('a::linorder) LogEvent => 'a LogEvent => bool" where
  "less_event (e1, ts1) (e2, ts2) = (ts1 < ts2 | (ts1 = ts2 & (e1 < e2)))"

fun less_eq_event :: "'a::linorder LogEvent => 'a LogEvent => bool" where
  "less_eq_event (e1,ts1) (e2, ts2) = (ts1 < ts2 | (ts1 = ts2 & (e1 < e2)) | (e1 = e2 & ts1 = ts2))"

(*
interpretation Log2Event: Orderings.linorder
  less_eq_event
  less_event
proof
  show "\<And>x y. less_event x y = (less_eq_event x y \<and> \<not> less_eq_event y x)" by auto
  show "\<And>x. less_eq_event x x" by auto
  show "\<And>x y z. less_eq_event x y \<Longrightarrow> less_eq_event y z \<Longrightarrow> less_eq_event x z" by auto
  show "\<And>x y. less_eq_event x y \<Longrightarrow> less_eq_event y x \<Longrightarrow> x = y" by auto
  show "\<And>x y. less_eq_event x y \<or> less_eq_event y x" by auto
qed
*)

fun insort1 :: "'a::linorder LogEvent => 'a LogEvent list => 'a LogEvent list" where
  "insort1 x [] = [x]" |
  "insort1 x (y#ys) = (if less_eq_event x y then x#y#ys else y#(insort1 x ys))"

fun insort :: "'a::linorder LogEvent list => 'a LogEvent list" where
  "insort [] = []" |
  "insort [x] = [x]" |
  "insort (x#xs) = insort1 x (insort xs)"

fun contains :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains _ [] = False" |
  "contains e (x#xs) = (e = x | contains e xs)"

lemma contains_tail : "contains e xs \<Longrightarrow>  contains e (x#xs)" by auto

lemma contains_head_or_tail: "contains e (x#xs) \<Longrightarrow> (e = x | contains e xs)" by auto

lemma contains_insort1_elem: "contains e (insort1 e l)"
  apply (induct l arbitrary: e)
  by auto

lemma contains_insort1_list: "contains e l \<Longrightarrow> contains e (insort1 a l)"
  apply (induct l arbitrary: e a)
  by auto

fun mapToEvents :: "'a LogEvent list => 'a list" where
  "mapToEvents [] = []" |
  "mapToEvents ((e, _)#xs) = e # (mapToEvents xs)"

lemma contains_mapToEvents : "contains (e, ts) l \<Longrightarrow> contains e (mapToEvents l)"
  apply (induct l arbitrary: e ts)
  by auto

lemma contains_mapToEvents_exists: "contains e (mapToEvents l) \<Longrightarrow> \<exists>ts. contains (e, ts) l"
  apply (induct l arbitrary: e)
  apply auto[1]
  by fastforce

fun query :: "'a::linorder Log \<Rightarrow> 'a list" where
    "query s1 = mapToEvents (insort (set_to_list (USet.query s1)))"

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
qed

end
