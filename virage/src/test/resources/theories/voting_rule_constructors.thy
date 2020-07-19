theory voting_rule_constructors

imports  loop_composition defer_eq_condition elect_module electoral_modules condorcet_consistency elim_module

begin

(********************************************)
(*** Definition: Voting Rule Constructors ***)
(********************************************)

definition iter :: "'a Electoral_module\<Rightarrow> 'a Electoral_module" where
  "iter m \<equiv> let t = Defer_eq_condition 1 in
    (m \<circlearrowleft>\<^sub>t)"

definition elector :: "'a Electoral_module\<Rightarrow> 'a Electoral_module" where
  "elector m \<equiv> m \<triangleright> Elect_module"

definition iterelect :: "'a Electoral_module\<Rightarrow> 'a Electoral_module" where
  "iterelect m \<equiv> elector (iter m)"

(***************)
(*** Lemmata ***)
(***************)

(* If m is defer condorcet consistent, then elector(m) is condorcet consistent *)
lemma m_defer_cc_implies_elector_m_cc:
  assumes dcc : "defer_condorcet_consistent m"
  shows "condorcet_consistent (elector m)"
proof (unfold condorcet_consistent_def elector_def, auto)
  show "electoral_module (m \<triangleright> Elect_module)" using dcc defer_condorcet_consistent_def elect_module_sound seq_creates_modules by blast
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 0 : "condorcet_winner_in A p w" and 1 : "x \<in> elect m A p" show "x \<in> A"
    by (meson "0" "1" condorcet_winner_in_def dcc defer_condorcet_consistent_def elect_from_input subset_eq)
next  
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 0 : "condorcet_winner_in A p w" and 1 : "x \<in> reject m A p" show "x \<in> A"
    by (meson "0" "1" condorcet_winner_in_def dcc defer_condorcet_consistent_def in_mono reject_from_input)
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 0 : "condorcet_winner_in A p w" and 1 : "x \<in> defer m A p" show "x \<in> A"
    by (meson "0" "1" condorcet_winner_in_def dcc defer_condorcet_consistent_def defer_from_input order_trans subset_Compl_singleton)
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 00 : "condorcet_winner_in A p w" and 0 : "x \<in> reject m A p" and 1 : "x \<in> elect m A p" show "False"
    by (metis (no_types, lifting) "0" "00" "1" Int_iff condorcet_winner_in_def dcc defer_condorcet_consistent_def empty_iff split_disjoint3)  
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 00 : "condorcet_winner_in A p w" and 0 : "x \<in> reject m A p" and 1 : "x \<in> defer m A p" show "False"
    by (metis (no_types, lifting) "0" "00" "1" IntI condorcet_winner_in_def dcc defer_condorcet_consistent_def empty_iff split_disjoint3)
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 00 : "condorcet_winner_in A p w" show "x \<in> elect m A p \<Longrightarrow> condorcet_winner_in A p x"
  proof - 
    have "\<not> x \<in> elect m A p" by (metis (no_types, lifting) "00" Pair_inject condorcet_winner_in_def dcc defer_condorcet_consistent_def equals0D prod.exhaust_sel)
    then show "(x \<in> elect m A p) \<Longrightarrow> condorcet_winner_in A p x"
      by simp
  qed
next 
  fix A :: "'a set" and  p :: "'a Profile" and w x assume 00 : "x \<in> A" and 01 : "x \<notin> reject m A p" and 02 : "x \<notin> defer m A p" and 03 : " condorcet_winner_in A p w" show "x \<in> elect m A p"
    by (meson "00" "01" "02" "03" condorcet_winner_in_def dcc defer_condorcet_consistent_def electoral_module_element_in_defer) 
next 
  fix A :: "'a set" and  p :: "'a Profile" and w x assume winner : "condorcet_winner_in A p w" and d : "x \<in> defer m A p" show "condorcet_winner_in A p x"
    by (metis (no_types, lifting) CollectD condorcet_winner_in_def d dcc defer_condorcet_consistent_def snd_conv winner)
next
  fix A :: "'a set" and  p :: "'a Profile" and w x assume winner : "condorcet_winner_in A p w" and d : "x \<notin> defer m A p" and x_in_A : "x \<in> A" show "condorcet_winner_in A p x \<Longrightarrow> x \<in> elect m A p"
    by (metis (no_types, lifting) condorcet_winner_in_def d dcc defer_condorcet_consistent_def singletonI snd_conv unique_condorcet_winner3)
qed

theorem cr_eval_implies_elect_max_elim_is_cc:
  assumes rating : "condorcet_rating e"
  shows "condorcet_consistent (elector (MAX_Eliminator e))"
  using cr_eval_implies_max_elim_is_def_cc m_defer_cc_implies_elector_m_cc rating by blast

end