theory eval_func
  imports electoral_modules condorcet_consistency

begin

(***************************************)
(*** Definition: Evaluation function ***)
(***************************************)

type_synonym 'a Eval_function = "'a  \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat"

(* An Evaluation function is condorcet_rating iff the following holds: *)
(* If Condorcet Winner w exists, he and only he has the highest value *)
definition condorcet_rating :: "'a Eval_function \<Rightarrow> bool" where
  "condorcet_rating f \<equiv> 
  \<forall>A p w . condorcet_winner_in A p w \<longrightarrow> (\<forall>l \<in> A . l \<noteq> w \<longrightarrow> f l A p < f w A p)"

(***************)
(*** Lemmata ***)
(***************)

(* If e is condorcet_rating the following holds: *)
(* If a Condorcet Winner w exists, he has the max eval value *)
lemma cwinner_has_max_value:
  assumes rating : "condorcet_rating e" and
          profile: "finite_profile A p" and
          winner : "condorcet_winner_in A p w"
        shows "e w A p = Max{e a A p | a. a \<in> A}"
proof -
  (* lemma eq_Max_iff: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> m = Max A  \<longleftrightarrow>  m \<in> A \<and> (\<forall>a \<in> A. a \<le> m)" *)
  let ?set="{e a A p | a. a \<in> A}" and ?eMax = "Max {e a A p | a. a \<in> A}" and ?eW = "e w A p"
  (* finite A *)
  from profile have 0 : "finite ?set" by simp
  (* 2. non-empty A *)
  have 1 : "?set \<noteq> {}" using condorcet_winner_in_def winner by fastforce 
  (* 3. m \<in> A *)
  have 2 : "?eW \<in> ?set" by (metis (mono_tags, lifting) CollectI condorcet_winner_in_def winner)
  (* 4. (\<forall>a \<in> A. a \<le> m) *)
  have 3 : "\<forall> e \<in> ?set . e \<le> ?eW" by (smt CollectD condorcet_rating_def eq_iff order.strict_implies_order rating winner) 
  (* Result *)
  from 2 3 have 4 : "?eW \<in> ?set \<and> (\<forall>a \<in> ?set. a \<le> ?eW)" by blast
  from 0 1 4 Max_eq_iff show ?thesis by (metis (no_types, lifting)) 
qed

(* If e is condorcet_rating the following holds: *)
(* If a Condorcet Winner w exists, a Non-Condorcet winner has a value lower than the max eval value *)
lemma cnotwinner_has_not_max_value:
  assumes rating : "condorcet_rating e" and
          profile: "finite_profile A p" and
          winner : "condorcet_winner_in A p w"
        shows "\<forall> l \<in> A . w \<noteq> l \<longrightarrow>  e l A p < Max{e a A p | a. a \<in> A}"
proof (auto) fix l 
  assume linA : "l \<in> A" and loser : "w \<noteq> l"
  show "e l A p < Max {e a A p |a. a \<in> A}"
  proof -
    have "e l A p < e w A p" by (metis condorcet_rating_def linA loser rating winner)
    also have "e w A p = Max {e a A p |a. a \<in> A}" using cwinner_has_max_value profile rating winner by fastforce
    finally show ?thesis by simp 
  qed
qed


end