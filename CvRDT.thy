theory CvRDT
    imports Main HOL.Lattices HOL.Orderings HOL.Set
begin

(* CvRDTs, as defined by Shapiro et al. *)
locale CvRDT =
  "'a" : Orderings.order_bot +                    (* partial order on S *)
  Lattices.semilattice_sup +                      (* semilattice on S *)
  fixes query :: "'a => 'q"                       (* the value of a CvRDT*)
    and update :: "'a => 'u => 'a"                (* update a CvRDT's state*)
  assumes monotonicity : "less_eq a (update a u)" (* monotonic update*)

context CvRDT
begin

  definition "initial = bot"

  fun merge :: "'a => 'a => 'a" where "merge a b = sup a b"

  (* merge function properties *)

  lemma merge_associativity: "merge a (merge b c) = merge (merge a b) c"
    by (simp add: local.sup.assoc)

  lemma merge_commutativity: "merge a b = merge b a"
    by (simp add: local.sup.commute)

  lemma merge_idempotency: "merge a a = a"
    by simp

  lemma merge_initial_right: "merge a initial = a"
    unfolding initial_def
    apply (auto)
    by (metis "'a.bot_least" local.sup.orderE)

  lemma merge_initial_left: "merge initial a = a"
    unfolding initial_def
    apply (simp add: local.merge_commutativity)
    using local.sup_absorb2 by force
end

end