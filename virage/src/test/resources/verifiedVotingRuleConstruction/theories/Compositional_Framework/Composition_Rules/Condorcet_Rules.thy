theory Condorcet_Rules
  imports "../Properties/Condorcet_Properties"
          "../../Social_Choice_Properties/Condorcet_Consistency"
          "../Components/Compositional_Structures/Sequential_Composition"
          "../Components/Composites/Composite_Elimination_Modules"
          "../Components/Composites/Composite_Structures"
          "../Components/Basic_Modules/Elect_Module"
begin

(*
   If e is Condorcet-rating, the following holds:
   If a Condorcet Winner w exists, w has the maximum evaluation value.
*)
theorem cond_winner_imp_max_eval_val:
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p w"
  shows "e w A p = Max {e a A p | a. a \<in> A}"
proof -
  (*
    lemma eq_max_iff: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow>
        m = Max A  \<longleftrightarrow>  m \<in> A \<and> (\<forall>a \<in> A. a \<le> m)"
  *)
  let ?set = "{e a A p | a. a \<in> A}" and
      ?eMax = "Max {e a A p | a. a \<in> A}" and
      ?eW = "e w A p"
  (*finite A*)
  from f_prof have 0: "finite ?set"
    by simp
  (*2. non-empty A*)
  have 1: "?set \<noteq> {}"
    using condorcet_winner.simps winner
    by fastforce
  (*3. m \<in> A*)
  have 2: "?eW \<in> ?set"
    using CollectI condorcet_winner.simps winner
    by (metis (mono_tags, lifting))
  (*4. (\<forall>a \<in> A. a \<le> m)*)
  have 3: "\<forall> e \<in> ?set . e \<le> ?eW"
    using CollectD condorcet_rating_def eq_iff
          order.strict_implies_order rating winner
    by (smt (verit, best))
  (*Result*)
  from 2 3 have 4:
    "?eW \<in> ?set \<and> (\<forall>a \<in> ?set. a \<le> ?eW)"
    by blast
  from 0 1 4 Max_eq_iff show ?thesis
    by (metis (no_types, lifting))
qed

(*
   If e is Condorcet-rating, the following holds:
   If a Condorcet Winner w exists, a non-Condorcet
   winner has a value lower than the maximum
   evaluation value.
*)
theorem non_cond_winner_not_max_eval:
  assumes
    rating: "condorcet_rating e" and
    f_prof: "finite_profile A p" and
    winner: "condorcet_winner A p w" and
    linA: "l \<in> A" and
    loser: "w \<noteq> l"
  shows "e l A p < Max {e a A p | a. a \<in> A}"
proof -
  have "e l A p < e w A p"
    using condorcet_rating_def linA loser rating winner
    by metis
  also have "e w A p = Max {e a A p |a. a \<in> A}"
    using cond_winner_imp_max_eval_val f_prof rating winner
    by fastforce
  finally show ?thesis
    by simp
qed

(*** If the used evaluation function is Condorcet rating,
     max-eliminator is Condorcet compatible. ***)
theorem cr_eval_imp_ccomp_max_elim[simp]:
  assumes
    profile: "finite_profile A p" and
    rating: "condorcet_rating e"
  shows
    "condorcet_compatibility (max_eliminator e)"
  unfolding condorcet_compatibility_def
proof (auto)
  have f1:
    "\<And>A p w x. condorcet_winner A p w \<Longrightarrow>
      finite A \<Longrightarrow> w \<in> A \<Longrightarrow> e w A p < Max {e x A p |x. x \<in> A} \<Longrightarrow>
        x \<in> A \<Longrightarrow> e x A p < Max {e x A p |x. x \<in> A}"
    using rating
    by (simp add: cond_winner_imp_max_eval_val)
  thus
    "\<And>A p w x.
      profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
        \<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
              finite A \<Longrightarrow> e w A p < Max {e x A p | x. x \<in> A} \<Longrightarrow>
                x \<in> A \<Longrightarrow> e x A p < Max {e x A p | x. x \<in> A}"
    by simp
qed

(*If m is defer-Condorcet-consistent, then elector(m) is Condorcet consistent.*)
lemma dcc_imp_cc_elector:
  assumes dcc: "defer_condorcet_consistency m"
  shows "condorcet_consistency (elector m)"
proof (unfold defer_condorcet_consistency_def
              condorcet_consistency_def, auto)
  show "electoral_module (m \<triangleright> elect_module)"
    using dcc defer_condorcet_consistency_def
          elect_mod_sound seq_comp_sound
    by metis
next
  show
    "\<And>A p w x.
       finite A \<Longrightarrow> profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
         \<forall>x\<in>A - {w}. card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
        x \<in> elect m A p \<Longrightarrow> x \<in> A"
  proof -
    fix
      A :: "'a set" and
      p :: "'a Profile" and
      w :: "'a" and
      x :: "'a"
    assume
      finite: "finite A" and
      prof_A: "profile A p"
    show
      "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)} \<Longrightarrow>
             x \<in> elect m A p \<Longrightarrow> x \<in> A"
      using dcc defer_condorcet_consistency_def
            elect_in_alts subset_eq finite prof_A
      by metis
  qed
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a" and
    xa :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> elect m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "xa = x"
    using condorcet_winner.simps dcc fst_conv insert_Diff "1"
          defer_condorcet_consistency_def insert_not_empty
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    1: "x \<in> defer m A p"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "0"
    by simp
  thus "x \<in> A"
    using "0" "1" condorcet_winner.simps dcc defer_in_alts
          defer_condorcet_consistency_def order_trans
          subset_Compl_singleton
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a" and
    xa :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> defer m A p" and
    xa_in_A: "xa \<in> A" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<not> card {i. i < length p \<and> (x, xa) \<in> (p!i)} <
            card {i. i < length p \<and> (xa, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "xa = x"
    using "1" "2" condorcet_winner.simps dcc empty_iff xa_in_A
          defer_condorcet_consistency_def "3" DiffI
          cond_winner_unique3 insert_iff prod.sel(2)
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    x_in_A: "x \<in> A" and
    1: "x \<notin> defer m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}" and
    3: "\<forall>y\<in>A - {x}.
          card {i. i < length p \<and> (x, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, x) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  also have "condorcet_winner A p x"
    using finite prof_A x_in_A "3"
    by simp
  ultimately show "x \<in> elect m A p"
    using "1" condorcet_winner.simps dcc
          defer_condorcet_consistency_def
          cond_winner_unique3 insert_iff eq_snd_iff
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    1: "x \<in> reject m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "x \<in> A"
    using "1" dcc defer_condorcet_consistency_def finite
          prof_A reject_in_alts subsetD
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "x \<in> reject m A p" and
    1: "x \<in> elect m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "False"
    using "0" "1" condorcet_winner.simps dcc IntI empty_iff
          defer_condorcet_consistency_def result_disj
    by (metis (no_types, hide_lams))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    0: "x \<in> reject m A p" and
    1: "x \<in> defer m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "False"
    using "0" "1" dcc defer_condorcet_consistency_def IntI
          Diff_empty Diff_iff finite prof_A result_disj
    by (metis (no_types, hide_lams))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    x :: "'a"
  assume
    finite: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    x_in_A: "x \<in> A" and
    0: "x \<notin> reject m A p" and
    1: "x \<notin> defer m A p" and
    2: "\<forall>y\<in>A - {w}.
          card {i. i < length p \<and> (w, y) \<in> (p!i)} <
            card {i. i < length p \<and> (y, w) \<in> (p!i)}"
  have "condorcet_winner A p w"
    using finite prof_A w_in_A "2"
    by simp
  thus "x \<in> elect m A p"
    using "0" "1" condorcet_winner.simps dcc x_in_A
          defer_condorcet_consistency_def electoral_mod_defer_elem
    by (metis (no_types, lifting))
qed

lemma ccomp_and_dd_imp_def_only_winner:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m" and
          winner: "condorcet_winner A p w"
  shows "defer m A p = {w}"
proof (rule ccontr)
  assume not_w: "defer m A p \<noteq> {w}"
  from dd have def_1:
    "defers 1 m"
    using defer_deciding_def
    by metis
  hence c_win:
    "finite_profile A p \<and>  w \<in> A \<and> (\<forall>x \<in> A - {w} . wins w p x)"
    using winner
    by simp
  hence "card (defer m A p) = 1"
    using One_nat_def Suc_leI card_gt_0_iff
          def_1 defers_def equals0D
    by metis
  hence 0: "\<exists>x \<in> A . defer m A p ={x}"
    using card_1_singletonE dd defer_deciding_def
          defer_in_alts insert_subset c_win
    by metis
  with not_w have "\<exists>l \<in> A . l \<noteq> w \<and> defer m A p = {l}"
    by metis
  hence not_in_defer: "w \<notin> defer m A p"
    by auto
  have "non_electing m"
    using dd defer_deciding_def
    by metis
  hence not_in_elect: "w \<notin> elect m A p"
    using c_win equals0D non_electing_def
    by metis
  from not_in_defer not_in_elect have one_side:
    "w \<in> reject m A p"
    using ccomp condorcet_compatibility_def c_win
          electoral_mod_defer_elem
    by metis
  from ccomp have other_side: "w \<notin> reject m A p"
    using condorcet_compatibility_def c_win winner
    by (metis (no_types, hide_lams))
  thus False
    by (simp add: one_side)
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, auto)
  show "electoral_module m"
    using dd defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    finiteness: "finite A" and
    assm: "\<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}"
  have winner: "condorcet_winner A p w"
    using assm finiteness prof_A w_in_A
    by simp
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. condorcet_winner A p d})"
  proof -
    (*Elect*)
    from dd have 0:
      "elect m A p = {}"
      using defer_deciding_def non_electing_def
            winner
      by fastforce
    (*Defers*)
    from dd ccomp have 1: "defer m A p = {w}"
      using ccomp_and_dd_imp_def_only_winner winner
      by simp
    (*Reject*)
    from 0 1 have 2: "reject m A p = A - defer m A p"
      using Diff_empty dd defer_deciding_def
            reject_not_elec_or_def winner
      by fastforce
    from 0 1 2 have 3: "m A p = ({}, A - defer m A p, {w})"
      using combine_ele_rej_def
      by metis
    have "{w} = {d \<in> A. condorcet_winner A p d}"
      using cond_winner_unique3 winner
      by metis
    thus ?thesis
      using "3"
      by auto
  qed
  hence
    "m A p =
      ({},
        A - defer m A p,
        {d \<in> A. \<forall>x\<in>A - {d}. wins d p x})"
    using finiteness prof_A winner Collect_cong
    by auto
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            prefer_count p x d < prefer_count p d x})"
    by simp
  hence
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (let r = (p!i) in (d \<preceq>\<^sub>r x))} <
                card {i. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r d))}})"
    by simp
  thus
    "m A p =
        ({},
          A - defer m A p,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (d, x) \<in> (p!i)} <
              card {i. i < length p \<and> (x, d) \<in> (p!i)}})"
    by simp
qed

lemma cr_eval_imp_dcc_max_elim_helper1:
  assumes
    f_prof: "finite_profile A p" and
    rating: "condorcet_rating e" and
    winner: "condorcet_winner A p w"
  shows "elimination_set e (Max {e x A p | x. x \<in> A}) (<) A p = A - {w}"
proof (safe, simp_all, safe)
  assume
    w_in_A: "w \<in> A" and
    max: "e w A p < Max {e x A p |x. x \<in> A}"
  show "False"
    using cond_winner_imp_max_eval_val
          rating winner f_prof max
    by fastforce
next
  fix
    x :: "'a"
  assume
    x_in_A: "x \<in> A" and
    not_max: "\<not> e x A p < Max {e y A p |y. y \<in> A}"
  show "x = w"
    using non_cond_winner_not_max_eval x_in_A
          rating winner f_prof not_max
    by (metis (mono_tags, lifting))
qed

(*
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
*)
theorem cr_eval_imp_dcc_max_elim[simp]:
  assumes rating: "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
  unfolding defer_condorcet_consistency_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    finite: "finite A"
  let ?trsh = "(Max {e y A p | y. y \<in> A})"
  show
    "max_eliminator e A p =
      ({},
        A - defer (max_eliminator e) A p,
        {a \<in> A. condorcet_winner A p a})"
  proof (cases "elimination_set e (?trsh) (<) A p \<noteq> A")
    case True
    have profile: "finite_profile A p"
      using winner
      by simp
    with rating winner have 0:
      "(elimination_set e ?trsh (<) A p) = A - {w}"
      using cr_eval_imp_dcc_max_elim_helper1
      by (metis (mono_tags, lifting))
    have
      "max_eliminator e A p =
        ({},
          (elimination_set e ?trsh (<) A p),
          A - (elimination_set e ?trsh (<) A p))"
      using True
      by simp
    also have "... = ({}, A - {w}, A - (A - {w}))"
      using "0"
      by presburger
    also have "... = ({}, A - {w}, {w})"
      using winner
      by auto
    also have "... = ({},A - defer (max_eliminator e) A p, {w})"
      using calculation
      by auto
    also have
      "... =
        ({},
          A - defer (max_eliminator e) A p,
          {d \<in> A. condorcet_winner A p d})"
      using cond_winner_unique3 winner Collect_cong
      by (metis (no_types, lifting))
    finally show ?thesis
      using finite winner
      by metis
  next
    case False
    thus ?thesis
    proof -
      have f1:
        "finite A \<and> profile A p \<and> w \<in> A \<and> (\<forall>a. a \<notin> A - {w} \<or> wins w p a)"
        using winner
        by auto
      hence
        "?trsh = e w A p"
        using rating winner
        by (simp add: cond_winner_imp_max_eval_val)
      hence False
        using f1 False
        by auto
      thus ?thesis
        by simp
    qed
  qed
qed

lemma condorcet_consistency2:
  "condorcet_consistency m \<longleftrightarrow>
      electoral_module m \<and>
        (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
            (m A p =
              ({w}, A - (elect m A p), {})))"
proof (auto)
  show "condorcet_consistency m \<Longrightarrow> electoral_module m"
    using condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cc: "condorcet_consistency m"
  have assm0:
    "condorcet_winner A p w \<Longrightarrow> m A p = ({w}, A - elect m A p, {})"
    using cond_winner_unique3 condorcet_consistency_def cc
    by (metis (mono_tags, lifting))
  assume
    finite_A: "finite A" and
    prof_A: "profile A p" and
    w_in_A: "w \<in> A"
  also have
    "\<forall>x\<in>A - {w}.
      prefer_count p w x > prefer_count p x w \<Longrightarrow>
        condorcet_winner A p w"
    using finite_A prof_A w_in_A wins.elims
    by simp
  ultimately show
    "\<forall>x\<in>A - {w}.
        card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
                m A p = ({w}, A - elect m A p, {})"
    using assm0
    by auto
next
  have assm0:
    "electoral_module m \<Longrightarrow>
      \<forall>A p w. condorcet_winner A p w \<longrightarrow>
          m A p = ({w}, A - elect m A p, {}) \<Longrightarrow>
            condorcet_consistency m"
    using condorcet_consistency_def cond_winner_unique3
    by (smt (verit, del_insts))
  assume e_mod:
    "electoral_module m"
  thus
    "\<forall>A p w. finite A \<and> profile A p \<and> w \<in> A \<and>
       (\<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}) \<longrightarrow>
       m A p = ({w}, A - elect m A p, {}) \<Longrightarrow>
          condorcet_consistency m"
    using assm0 e_mod
    by simp
qed

end