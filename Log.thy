theory Log
  imports CvRDT HOL.Set HOL.Fun
begin

type_synonym Timestamp = "nat list"

datatype 'event LogEntry = LogEntry "'event" "Timestamp"
datatype 'event Log = Log "('event LogEntry) set"

definition initial :: "'event Log" where
  "initial = Log Set.empty"
 

fun vector_clock_update :: "nat => Timestamp => Timestamp" where
  "vector_clock_update i v = (let incremented = (nth v i) + 1 in
                                take i v @ [incremented] @ drop (i+1) v)"

fun update :: "'event Log => 'event => nat => Timestamp => 'event Log" where
  "update (Log s) e i v = Log (s \<union> {LogEntry e (vector_clock_update i v)})"

fun merge :: "'event Log => 'event Log => 'event Log" where
  "merge (Log s1) (Log s2) = Log (s1 \<union> s2)"

fun gc :: "'event Log => Timestamp => 'event Log" where
  "gc (Log s) min_ts = Log {entry. entry \<in> s \<and> (\<exists>e t. entry = LogEntry e t \<and> (\<forall>j<length t. nth t j <= nth min_ts j))}"

fun subset_eq :: "'event Log => 'event Log => bool" where
  "subset_eq (Log s1) (Log s2) = Set.subset_eq s1 s2"

fun subset :: "'event Log => 'event Log => bool" where
  "subset (Log s1) (Log s2) = (Set.subset s1 s2)"

fun union :: "'event Log => 'event Log => 'event Log" where
  "union (Log s1) (Log s2) = Log (s1 \<union> s2)"



interpretation LogCvRDT : CvRDT
  Log.subset_eq
  Log.subset
  Log.union
  Log.initial
  Log.update
  Log.merge
proof
  show "\<And>x. Log.subset_eq x x"
    using subset_eq.elims(3) by fastforce
  show "\<And>x y. Log.subset x y = (Log.subset_eq x y \<and> \<not> Log.subset_eq y x)"
    by (metis subset.elims psubsetE psubsetI subset.simps subset_eq.simps)
  show "\<And>x y z.
       Log.subset_eq x y \<Longrightarrow>
       Log.subset_eq y z \<Longrightarrow> Log.subset_eq x z"
    by (metis Log.inject subset_eq subset_eq.elims(2) subset_eq.elims(3))
  show "\<And>x y. Log.subset_eq x y \<Longrightarrow>
           Log.subset_eq y x \<Longrightarrow> x = y"
    using subset_eq.elims(2) by fastforce
  show "\<And>x y. Log.subset_eq x (Log.union x y)"
    by (metis Log.exhaust Un_commute inf_sup_ord(4) subset_eq.simps union.simps)
  show  "\<And>y x. Log.subset_eq y (Log.union x y)"
      by (smt (verit, del_insts) Log.inject UnCI \<open>\<And>y x. Log.subset_eq x (Log.union x y)\<close> subsetI subset_eq.elims(2) subset_eq.elims(3) union.simps)
  show "\<And>y x z.  
       Log.subset_eq y x \<Longrightarrow>
       Log.subset_eq z x \<Longrightarrow>
       Log.subset_eq (Log.union y z) x"
    by (metis Log.inject subset_eq subset_eq.elims(2) subset_eq.elims(3))
  show "\<And>a u. Log.subset_eq a (merge a u)"
    using subset_eq.elims(3) by fastforce
  qed
  
end
