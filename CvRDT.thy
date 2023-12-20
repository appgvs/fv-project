theory CvRDT
    imports Main HOL.Lattices HOL.Orderings HOL.Set
begin

(* CvRDTs, as defined by Shapiro et al. *)
locale CvRDT =
  "'a" : Orderings.order +                        (* partial order on S *)
  Lattices.semilattice_sup +                      (* semilattice on S *)
  fixes initial :: "'a"                           (* the initial state of a CvRDT*)
    and query :: "'a => 'q"                       (* the value of a CvRDT*)
    and update :: "'a => 'u => 'a"                (* update a CvRDT's state*)
  assumes monotonicity : "less_eq a (update a u)" (* monotonic update*)

context CvRDT
begin

  fun merge :: "'a => 'a => 'a" where "merge a b = sup a b"

  (* merge function properties *)

  lemma merge_associativity: "merge a (merge b c) = merge (merge a b) c"
    by (simp add: local.sup.assoc)

  lemma merge_commutativity: "merge a b = merge b a"
    by (simp add: local.sup.commute)

  lemma merge_idempotency: "merge a a = a"
    by simp
end
end