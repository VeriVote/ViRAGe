theory elim_module
imports electoral_modules eval_func condorcet_consistency

begin

(**************************************)
(*** Definition: Elimination Module ***)
(**************************************)

type_synonym threshold_value = nat

abbreviation elim_set :: "'a Eval_function \<Rightarrow> threshold_value \<Rightarrow> (nat \<Rightarrow> threshold_value \<Rightarrow> bool)  \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
 "elim_set e t r A p \<equiv> {a \<in> A . r (e a A p) t }"

definition Elimination_module :: "'a Eval_function \<Rightarrow> threshold_value \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a Electoral_module" where
  "Elimination_module e t r A p =
  (if (elim_set e t r A p) \<noteq> A
    then (  {},  (elim_set e t r A p),   A - (elim_set e t r A p)   )
   else ({},{},A)
  )"

(*** Important Elimination Modules ***)

abbreviation LESS_Eliminator where
  "LESS_Eliminator e t A p \<equiv> Elimination_module e t (<) A p"

abbreviation MAX_Eliminator  where
  "MAX_Eliminator e A p \<equiv> LESS_Eliminator e (Max {e x A p | x. x \<in> A}) A p"

abbreviation LEQ_Eliminator where
  "LEQ_Eliminator e t A p \<equiv> Elimination_module e t (\<le>) A p"

abbreviation MIN_Eliminator  where
  "MIN_Eliminator e A p \<equiv> LEQ_Eliminator e (Min{e x A p | x. x \<in> A}) A p"

(** Less important Elimination Modules ***)

abbreviation avg where 
  "avg e A p \<equiv> (\<Sum>x \<in> A. e x A p) div (card A)"

abbreviation LESS_AVG_Eliminator where
  "LESS_AVG_Eliminator e A p \<equiv> LESS_Eliminator e (avg e A p) A p"

abbreviation LEQ_AVG_Eliminator where
  "LEQ_AVG_Eliminator e A p \<equiv> LEQ_Eliminator e (avg e A p) A p"

(***************)
(*** Lemmata ***)
(***************)

(*** Soundness: An Elimination Module is an Electoral Module ***)
lemma elim_module_sound:
  shows "electoral_module (Elimination_module e t r)"
proof (unfold electoral_module_def)
  show "\<forall>A p. finite_profile A p \<longrightarrow> partition_of A (Elimination_module e t r A p)"
  proof (unfold partition_of_def)
    show "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (Elimination_module e t r A p) \<and> unify_to A (Elimination_module e t r A p)"
    proof (auto) (* Disjoint *)
      fix A
      fix p
      show "finite A \<Longrightarrow> profile_on A p \<Longrightarrow> disjoint3 (Elimination_module e t r A p)"
      proof (cases "elim_set e t r A p \<noteq> A")
          case True
          let ?mod = "(Elimination_module e t r A p)"
          let ?elim = "(elim_set e t r A p)"
          let ?result = "(  {},  ?elim,   A - ?elim)"
          from True have 0 : "?mod = ?result"
            by (simp add : Elimination_module_def)
          hence disjoint: "disjoint3 (?mod)"
            by simp
          then show ?thesis by auto
        next
          case False
          let ?mod = "(Elimination_module e t r A p)"
          from False have 0 : "?mod = ({},{},A)"
            by (simp add: Elimination_module_def)
          hence disjoint: "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (?mod)"
            by simp
          then show ?thesis by (simp add: "0")
        qed
    next (* Unity *)
      fix A
      fix p
      show "finite A \<Longrightarrow> profile_on A p \<Longrightarrow> unify_to A (Elimination_module e t r A p)"
      proof (cases "elim_set e t r A p \<noteq> A")
        case True
          let ?mod = "(Elimination_module e t r A p)"
          let ?elim = "(elim_set e t r A p)"
          let ?result = "(  {},  ?elim,   A - ?elim)"
          have 0: "{} \<union> ?elim \<union> (A - ?elim) = A"
            by blast
          from True have 1 : "?mod = ?result"
            by (simp add : Elimination_module_def)
        then show ?thesis by auto
      next
        case False
          let ?mod = "(Elimination_module e t r A p)"
          have 0: "{} \<union> {} \<union> A = A"
            by simp
          from False have 1 : "?mod = ({},{},A)"
            by (simp add: Elimination_module_def)
        then show ?thesis by simp
      qed
    qed
  qed
qed

(*** An elimination module is non-electing ***)
lemma elim_module_nonelecting:
  assumes profile: "finite_profile A p"
  shows "non_electing (Elimination_module e t r )"
proof (unfold non_electing_def, auto)
  show "electoral_module (Elimination_module e t r)" by (simp add: elim_module_sound)
next 
  show "\<And>A p x. finite A \<Longrightarrow> profile_on A p \<Longrightarrow> x \<in> elect (Elimination_module e t r) A p \<Longrightarrow> False"
    by (metis (no_types, lifting) Elimination_module_def emptyE prod.sel(1))
qed

        
(*** If the used Eval-Function is Condorcet Rating, MAX-Eliminator is Condorcet-Compatible ***)
lemma cr_eval_implies_max_elim_is_ccomp:
  assumes profile: "finite_profile A p"
  shows "condorcet_rating e \<Longrightarrow> condorcet_compatible (MAX_Eliminator e)" 
proof (unfold condorcet_compatible_def)
  show "condorcet_rating e \<Longrightarrow> electoral_module (MAX_Eliminator e) \<and> (\<forall>A p w. condorcet_winner_in A p w \<and> finite A \<longrightarrow> w \<notin> reject (MAX_Eliminator e) A p \<and> (\<forall>l. \<not> condorcet_winner_in A p l \<longrightarrow> l \<notin> elect (MAX_Eliminator e) A p) \<and> (w \<in> elect (MAX_Eliminator e) A p \<longrightarrow> (\<forall>l. \<not> condorcet_winner_in A p l \<longrightarrow> l \<in> reject (MAX_Eliminator e) A p)))"
  proof (auto)
    (* 1. Module is electoral module*)
    show "electoral_module (MAX_Eliminator e)" using electoral_module_def elim_module_sound by blast
    (* proof -
      let ?t = "(\<lambda>e' A' p'. Max {e' x A' p' | x. x \<in> A' })"
      fix A
      fix p
      have "MAX_Eliminator e A p = LESS_Eliminator e ?t A p" by simp
      also have "\<dots> = Elimination_module e ?t (<) A p" by simp
      then show ?thesis using elim_module_sound by blast 
    qed *)
  next (* 2. Condorcet Winner is not rejected *)
    show "\<And>A p w. condorcet_rating e \<Longrightarrow> condorcet_winner_in A p w \<Longrightarrow> finite A \<Longrightarrow> w \<in> reject (MAX_Eliminator e) A p \<Longrightarrow> False" 
    proof - 
      fix A p w show "condorcet_rating e \<Longrightarrow> condorcet_winner_in A p w \<Longrightarrow> finite A \<Longrightarrow> w \<in> reject (MAX_Eliminator e) A p \<Longrightarrow> False"
      proof -
      assume rating : "condorcet_rating e"
      assume winner : "condorcet_winner_in A p w "
      assume finiteness : "finite A"
      assume rejection : "w \<in> reject (MAX_Eliminator e) A p"
      show "False"
      proof -
        let ?elim = "(elim_set e (Max {e x A p | x. x \<in> A}) (<) A p)"
        let ?mod = "(MAX_Eliminator e) A p"

        from rejection have "w \<in> ?elim" by (metis (no_types, lifting) CollectD CollectI Elimination_module_def ex_in_conv prod.sel(1) prod.sel(2))
        from this have "(MAX_Eliminator e) A p = ({},?elim,A-?elim)" by (smt Collect_cong Elimination_module_def Pair_inject emptyE prod.collapse rejection) 
        from this have "A-?elim \<noteq> {}" by (metis (no_types, lifting) Diff_empty Elimination_module_def condorcet_winner_in_def elim_module_sound emptyE fst_conv reject_alternative_representation snd_conv winner) 
        from this have "\<exists> l \<in> A . l \<in> A-?elim" by blast
        then have "\<exists> l \<in> A . l \<in> (defer (MAX_Eliminator e) A p)" by (simp add: \<open>MAX_Eliminator e A p = ({}, elim_set e (Max {e x A p |x. x \<in> A}) (<) A p, A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p)\<close>) 
        from this obtain l where "l \<in> (defer (MAX_Eliminator e) A p)" by blast

        then have different : "l \<noteq> w" using \<open>MAX_Eliminator e A p = ({}, elim_set e (Max {e x A p |x. x \<in> A}) (<) A p, A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p)\<close> rejection by auto


        (* At one side *)
        from rating winner different have 0 : "e l A p < e w A p"  by (smt DiffE \<open>MAX_Eliminator e A p = ({}, elim_set e (Max {e x A p |x. x \<in> A}) (<) A p, A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p)\<close> \<open>l \<in> defer (MAX_Eliminator e) A p\<close> condorcet_rating_def snd_conv)

        (* At the other side *)
        have "l \<in> (defer (MAX_Eliminator e) A p)" using \<open>l \<in> defer (MAX_Eliminator e) A p\<close> by blast
        then have "l \<in> A - ?elim" by (simp add: \<open>MAX_Eliminator e A p = ({}, elim_set e (Max {e x A p |x. x \<in> A}) (<) A p, A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p)\<close>)
        then have "l \<notin> ?elim" by blast
        then have "\<not> (<) (e l A p) ( Max {f x A p | x. x \<in> A})" using "0" \<open>l \<in> A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> \<open>w \<in> elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> by auto
        then have "\<not> (e l A p) < ( Max {f x A p | x. x \<in> A})" by blast
        then have "(e l A p) \<ge> ( Max {f x A p | x. x \<in> A})" using not_less by blast
        then have 1 : "(e l A p) = ( Max {f x A p | x. x \<in> A})" using "0" \<open>l \<in> A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> \<open>w \<in> elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> by auto

        from 0 1 show ?thesis using \<open>l \<in> A - elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> \<open>w \<in> elim_set e (Max {e x A p |x. x \<in> A}) (<) A p\<close> by auto  
      qed qed qed
    next (* 3. No Not-Condorcet Winner is elected *)
    show "\<And>A p w l. condorcet_rating e \<Longrightarrow> condorcet_winner_in A p w \<Longrightarrow> finite A \<Longrightarrow> \<not> condorcet_winner_in A p l \<Longrightarrow> l \<in> elect (MAX_Eliminator e) A p \<Longrightarrow> False"
    proof -
      fix A p w l show "condorcet_rating e \<Longrightarrow> condorcet_winner_in A p w \<Longrightarrow> finite A \<Longrightarrow> \<not> condorcet_winner_in A p l \<Longrightarrow> l \<in> elect (MAX_Eliminator e) A p \<Longrightarrow> False"
      proof -
        (* assume rating : "condorcet_rating e"
        and    winner : "condorcet_winner_in A p w"
        and    loser  : "\<not> condorcet_winner_in A p l" *)
        assume l_elect: "l \<in> elect (MAX_Eliminator e) A p"
        show "False" by (metis (no_types, lifting) Elimination_module_def emptyE l_elect prod.sel(1))
      qed
    qed
  next (* 4. If a Condorcet Winner is elected, each other alternative gets rejected (\<Rightarrow> stays not in defer set) *)
    show "\<And>A p w l.
       condorcet_rating e \<Longrightarrow>
       condorcet_winner_in A p w \<Longrightarrow>
       finite A \<Longrightarrow> w \<in> elect (MAX_Eliminator e) A p \<Longrightarrow> \<not> condorcet_winner_in A p l \<Longrightarrow> l \<in> reject (MAX_Eliminator e) A p"
      by (metis (no_types, lifting) Elimination_module_def emptyE fst_conv)
  qed  
qed


lemma cr_eval_implies_max_elim_is_def_cc_helper1:
   assumes profile: "finite_profile A p" and
          rating : "condorcet_rating e" and
          winner : "condorcet_winner_in A p w"
   shows "elim_set e (Max {e x A p | x. x \<in> A}) (<) A p = A - {w}" 
proof (auto)
  show "w \<in> A \<Longrightarrow> e w A p < Max {e x A p |x. x \<in> A} \<Longrightarrow> False" using cwinner_has_max_value profile rating winner by fastforce 
next 
  show "\<And>x. x \<in> A \<Longrightarrow> x \<noteq> w \<Longrightarrow> e x A p < Max {e x A p |x. x \<in> A}" using cnotwinner_has_not_max_value profile rating winner by fastforce 
qed

(*** If the used Eval-Function is Condorcet Rating, MAX-Eliminator is Defer Condorcet Consistent***)
lemma cr_eval_implies_max_elim_is_def_cc:
  assumes rating : "condorcet_rating e"
        shows "defer_condorcet_consistent (MAX_Eliminator e)"
proof (unfold defer_condorcet_consistent_def, auto)
  show "electoral_module (MAX_Eliminator e)" using electoral_module_def elim_module_sound by blast
next
  fix A :: "'a set" and p :: "'a Profile" and w 
  assume finite : "finite A" and winner: "condorcet_winner_in A p w"
  show "MAX_Eliminator e A p = ({}, A - defer (MAX_Eliminator e) A p, {d \<in> A. condorcet_winner_in A p d})"
  proof (cases "elim_set e (Max {e x A p | x. x \<in> A}) (<) A p \<noteq> A")
    let ?trsh = "(Max {e x A p | x. x \<in> A})"
    case True
    have profile : "finite_profile A p" by (meson condorcet_winner_in_def winner)
    from this rating winner have 0 : "(elim_set e ?trsh (<) A p) = A - {w}"
      by (simp add: cr_eval_implies_max_elim_is_def_cc_helper1)
    
    have "MAX_Eliminator e A p = ({},(elim_set e ?trsh (<) A p),   A - (elim_set e ?trsh (<) A p)   )"
      by (simp add: Elimination_module_def True)
    also have "... = ({},A - {w}, A - (A - {w}))" by (simp add: "0")
    also have "... = ({},A - {w}, {w})" using condorcet_winner_in_def winner by fastforce
    also have "... = ({},A - defer (MAX_Eliminator e) A p, {w})" by (simp add: calculation)
    also have "... = ({},A - defer (MAX_Eliminator e) A p, {d \<in> A. condorcet_winner_in A p d})" using unique_condorcet_winner3 winner by fastforce
    finally show ?thesis by blast
  next
    case False
    then show ?thesis by (metis (mono_tags, lifting) Diff_iff condorcet_winner_in_def cr_eval_implies_max_elim_is_def_cc_helper1 rating singletonI winner)
  qed
qed