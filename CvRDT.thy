theory CvRDT
  imports Main
begin

class cvrdt =
  fixes
    merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes associativity: "merge (merge a b) c = merge a (merge b c)"
      and commutativity: "merge a b = merge b a"
      and idempotency: "merge a a = a"

instantiation int :: cvrdt
begin
definition "merge-int" : "merge a b = (if (a::int) > (b::int) then a else b)"
instance proof
  fix a b c :: int
  show "merge a b = merge b a"
    using "merge-int" by auto
  thus "merge a a = a"
    using "merge-int" by auto
  thus "merge (merge a b) c = merge a (merge b c)"
    by (simp add: "merge-int")
qed
end

instantiation prod :: (cvrdt, cvrdt) cvrdt
begin
definition "merge-prod" : "merge a b = (merge (fst a) (fst b), merge (snd a) (snd b))"
instance proof
  fix a b c :: "'a :: cvrdt \<times> 'b :: cvrdt"
  show "merge a b = merge b a"
    by (simp add: "merge-prod" commutativity)
  thus "merge a a = a"
    by (simp add: "merge-prod" idempotency)
  thus "merge (merge a b) c = merge a (merge b c)"
    by (simp add: "merge-prod" associativity)
qed
end

instantiation set :: (cvrdt) cvrdt
begin
definition "merge-set" : "merge a b = a \<union> b"
instance proof
  fix a b c :: "'a set"
  show "merge a b = merge b a"
    by (simp add: "merge-set" sup_commute)
  thus "merge a a = a"
    by (simp add: "merge-set")
  thus "merge (merge a b) c = merge a (merge b c)"
    using "merge-set" by auto
qed
end

datatype 'a USet = USet "'a set"
fun add :: "'a => 'a USet => 'a USet" where
  "add e (USet s) = USet (s \<union> {e})"
fun elements :: "'a USet => 'a set" where
  "elements (USet s) = s"
instantiation USet :: (cvrdt) cvrdt
begin
definition "merge-gset" : "merge a b = USet ((elements a) \<union> (elements b))"
instance proof
  fix a b c :: "'a USet"
  show "merge a b = merge b a"
    using "merge-gset" by auto
  thus "merge a a = a"
    by (metis "merge-gset" elements.elims sup.idem)
  thus "merge (merge a b) c = merge a (merge b c)"
    using "merge-gset" by auto
qed
end

export_code "merge" "USet" "add" in Scala 
  module_name "CvRDT"

end