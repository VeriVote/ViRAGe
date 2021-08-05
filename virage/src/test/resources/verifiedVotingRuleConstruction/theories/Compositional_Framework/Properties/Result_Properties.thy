theory Result_Properties
  imports "../Components/Electoral_Module"

begin

(*
   An electoral module is electing iff
   it always elects at least one alternative.
*)
definition electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect m A p \<noteq> {})"

lemma electing_for_only_alt:
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    f_prof: "finite_profile A p"
  shows "elect m A p = A"
  using Int_empty_right Int_insert_right card_1_singletonE
        elect_in_alts electing electing_def inf.orderE
        one_alt f_prof
  by (smt (verit, del_insts))


(*
   An electoral module is non-electing iff
   it never elects an alternative.
*)
definition non_electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> (\<forall>A p. finite_profile A p \<longrightarrow> elect m A p = {})"

(*
   An electoral module decrements iff
   this module rejects at least one alternative whenever possible (|A|>1).
*)
definition decrementing :: "'a Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    electoral_module m \<and> (
      \<forall> A p . finite_profile A p \<longrightarrow>
          (card A > 1 \<longrightarrow> card (reject m A p) \<ge> 1))"

(*
   An electoral module is non-blocking iff
   this module never rejects all alternatives.
*)
definition non_blocking :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and>
      (\<forall>A p.
          ((A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> reject m A p \<noteq> A))"


(*
   "elects n" is true for all electoral modules that
   elect exactly n alternatives, whenever there are n or more alternatives.
*)
definition elects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (elect m A p) = n)"

(*
   "defers n" is true for all electoral modules that defer exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition defers :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow>
          card (defer m A p) = n)"

(*
   "rejects n" is true for all electoral modules that reject exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition rejects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A \<ge> n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

(*
   As opposed to "rejects", "eliminates" allows to stop rejecting if no
   alternatives were to remain.
*)
definition eliminates :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p. (card A > n \<and> finite_profile A p) \<longrightarrow> card (reject m A p) = n)"

lemma single_elim_imp_red_def_set:
  assumes
    eliminating: "eliminates 1 m" and
    leftover_alternatives: "card A > 1" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts
        eliminates_def eliminating eq_iff leftover_alternatives
        not_one_le_zero f_prof psubsetI reject_not_elec_or_def
  by metis

lemma single_elim_decr_def_card:
  assumes
    rejecting: "rejects 1 m" and
    not_empty: "A \<noteq> {}" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
  using Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
        defer_not_elec_or_rej finite_subset non_electing
        non_electing_def not_empty f_prof reject_in_alts rejecting
        rejects_def
  by (smt (verit, ccfv_threshold))

lemma single_elim_decr_def_card2:
  assumes
    eliminating: "eliminates 1 m" and
    not_empty: "card A > 1" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p"
  shows "card (defer m A p) = card A - 1"
  using Diff_empty One_nat_def Suc_leI card_Diff_subset card_gt_0_iff
        defer_not_elec_or_rej finite_subset non_electing
        non_electing_def not_empty f_prof reject_in_alts
        eliminating eliminates_def
  by (smt (verit))

(*
   An electoral module is defer-deciding iff
   this module chooses exactly 1 alternative to defer and
   rejects any other alternative.
   Note that `rejects n-1 m` can be omitted due to the
   well-formedness property.
*)
definition defer_deciding :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    electoral_module m \<and> non_electing m \<and> defers 1 m"

end