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

(* Garbage Collection Function *)
fun gc :: "'event Log => Timestamp => 'event Log" where
  "gc (Log s) min_ts = Log {entry. entry \<in> s \<and> (\<exists>e t. entry = LogEntry e t \<and> (\<forall>j<length t. nth t j <= nth min_ts j))}"

interpretation logCvRDT : CvRDT
  log.initial
  log.update
  log.merge
  log.gc
proof
    

qed

end
