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

instantiation set :: (type) cvrdt
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
fun uset_add :: "'a => 'a USet => 'a USet" where
  "uset_add e (USet s) = USet (s \<union> {e})"
fun uset_value :: "'a USet => 'a set" where
  "uset_value (USet s) = s"
instantiation USet :: (type) cvrdt
begin
definition "merge-gset" : "merge a b = USet ((uset_value a) \<union> (uset_value b))"
instance proof
  fix a b c :: "'a USet"
  show "merge a b = merge b a"
    using "merge-gset" by auto
  thus "merge a a = a"
    by (metis "merge-gset" uset_value.elims sup.idem)
  thus "merge (merge a b) c = merge a (merge b c)"
    using "merge-gset" by auto
qed
end

datatype 'a PNSet = PNSet "'a set \<times> 'a set"
fun pnset_add :: "'a => 'a PNSet => 'a PNSet" where
  "pnset_add e (PNSet (a, r)) = PNSet (a \<union> {e}, r)"
fun pnset_remove :: "'a => 'a PNSet => 'a PNSet" where
  "pnset_remove e (PNSet (a, r)) = PNSet (a \<union> {e}, r \<union> {e})"
fun pnset_value :: "'a PNSet => 'a set" where
  "pnset_value (PNSet (a,r)) = a - r"
instantiation PNSet :: (type) cvrdt
begin
fun pnset_a :: "'a PNSet => 'a set" where
  "pnset_a (PNSet p) = fst p"
fun pnset_r :: "'a PNSet => 'a set" where
  "pnset_r (PNSet p) = snd p"
definition "merge-pnset" : "merge a b = PNSet (
    pnset_a a \<union> pnset_a b,
    pnset_r a \<union> pnset_r b
  )"
instance proof
  fix a b c :: "'a PNSet"
  show "merge a b = merge b a"
    using "merge-pnset" by auto
  thus "merge a a = a"
    by (metis "merge-pnset" "merge-prod" "merge-set" idempotency pnset_a.elims pnset_r.simps)
  thus "merge (merge a b) c = merge a (merge b c)"
    using "merge-pnset" by auto
qed
end

export_code
  "merge"
  "USet" "uset_add" "uset_value"
  "PNSet" "pnset_add" "pnset_remove" "pnset_value"
in Scala 
  module_name "CvRDT"

end