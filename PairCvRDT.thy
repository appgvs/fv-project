theory PairCvRDT
    imports Main CvRDT HOL.Orderings
begin

locale PairCvRDT =
    (* first component definitions *)
  fixes bot1 :: "'a1"
    and less_eq1 :: "'a1 => 'a1 => bool"
    and less1 :: "'a1 => 'a1 => bool"
    and sup1 :: "'a1 => 'a1 => 'a1"
    and query1 :: "'a1 => 'q1"
    and update1 :: "'a1 => 'u1 => 'a1"

    (* second component definitions *)
    and bot2 :: "'a2"
    and less_eq2 :: "'a2 => 'a2 => bool"
    and less2 :: "'a2 => 'a2 => bool"
    and sup2 :: "'a2 => 'a2 => 'a2"
    and query2 :: "'a2 => 'q2"
    and update2 :: "'a2 => 'u2 => 'a2"

    (* both elements are a CvRDT *)
  assumes "CvRDT.CvRDT bot1 less_eq1 less1 sup1 update1"
    and   "CvRDT.CvRDT bot2 less_eq2 less2 sup2 update2"

datatype ('u1, 'u2) Update = Update1 "'u1" | Update2 "'u2"

context PairCvRDT
begin

    definition bot :: "('a1 \<times> 'a2)" where
        "bot = (bot1, bot2)"

    fun less_eq :: "('a1 \<times> 'a2) => ('a1 \<times> 'a2) => bool" where
        "less_eq (a, b) (x, y) = (less_eq1 a x & less_eq2 b y)"

    fun less :: "('a1 \<times> 'a2) => ('a1 \<times> 'a2) => bool" where
        "less (a, b) (x, y) = ((less1 a x & less_eq2 b y) | (less_eq1 a x & less2 b y))"

    fun merge :: "('a1 \<times> 'a2) => ('a1 \<times> 'a2) => ('a1 \<times> 'a2)" where
        "merge (a, b) (x, y) = (sup1 a x, sup2 b y)"

    fun query :: "('a1 \<times> 'a2) => ('q1 \<times> 'q2)" where
        "query (a, b) = (query1 a, query2 b)"

    fun update :: "('a1 \<times> 'a2) => ('u1, 'u2) Update => ('a1 \<times> 'a2)" where
        "update (a, b) (Update1 u) = (update1 a u, b)" |
        "update (a, b) (Update2 u) = (a, update2 b u)"

(*lemma less_eq1_reflexivity: "\<And>a b. x = (a, b) \<Longrightarrow> less_eq1 a a"
    using CvRDT_def[of bot1 less_eq1 less1 sup1 update1] assms(1)
    by (simp add: order.refl)*)

    (*
    lemma less_eq_reflexive: "less_eq x x"
        apply (cases x)
        apply (auto)
        using CvRDT_def[of bot1 less_eq1 less1 sup1 update1]
        using CvRDT_def[of bot2 less_eq2 less2 sup2 update2]
      proof -
        show "\<And>a b. x = (a, b) \<Longrightarrow> less_eq1 a a"
          
        show "\<And>a b. x = (a, b) \<Longrightarrow> less_eq2 b b"
          sorry
      qed

    interpretation PairCvRDTCvRDT : CvRDT
        bot less_eq less merge query update
        apply unfold_locales
    proof
        
    oops
    *)
end

end