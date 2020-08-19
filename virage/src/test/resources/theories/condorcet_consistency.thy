theory condorcet_consistency
imports electoral_modules

begin

(*************************************************)
(*** Condorcet consistency related definitions ***)
(*************************************************)

abbreviation prefer_count where "prefer_count p x y \<equiv> card{i::nat. i < size p \<and> smaller y (p!i) x}"

fun prefer_count_code :: "'a Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "prefer_count_code Nil x y = 0" |
  "prefer_count_code (p#ps) x y = (if smaller y p x then 1 else 0) + prefer_count_code ps x y"

export_code prefer_count_code in Haskell

definition wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins x p y \<equiv> prefer_count p x y > prefer_count p y x"

definition wins_code :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins_code x p y \<equiv> prefer_count_code p x y > prefer_count_code p y x"

export_code wins_code in Haskell

definition condorcet_winner_in :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner_in A p w \<equiv> finite_profile A p \<and>  w \<in> A \<and>
  (\<forall>x \<in> A - {w} . wins w p x)"

definition condorcet_winner_in_code :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner_in_code A p w \<equiv> finite_profile A p \<and>  w \<in> A \<and>
  (\<forall>x \<in> A - {w} . wins_code w p x)"

export_code condorcet_winner_in_code in Haskell

definition condorcet_consistent :: "'a Electoral_module \<Rightarrow> bool" where
"condorcet_consistent m \<equiv> electoral_module m \<and> (
    \<forall> A p w. condorcet_winner_in A p w \<longrightarrow> (
      m A p = ({e \<in> A. condorcet_winner_in A p e},
               A - (elect m A p),
               {})))"

definition defer_condorcet_consistent :: "'a Electoral_module \<Rightarrow> bool" where
  "defer_condorcet_consistent m \<equiv> electoral_module m \<and> (
    \<forall> A p w. condorcet_winner_in A p w \<and> finite A \<longrightarrow> (
      m A p = ({},
               A - (defer m A p),
               {d \<in> A. condorcet_winner_in A p d})))"

definition condorcet_compatible :: "'a Electoral_module \<Rightarrow> bool" where
  "condorcet_compatible m \<equiv> electoral_module m \<and> (
    \<forall> A p w. condorcet_winner_in A p w \<and> finite A \<longrightarrow> (
      w \<notin> reject m A p \<and>
      (\<forall>l. \<not>condorcet_winner_in A p l \<longrightarrow> l \<notin> elect m A p) \<and>
      (w \<in> elect m A p \<longrightarrow> (\<forall>l. \<not>condorcet_winner_in A p l \<longrightarrow> l \<in> reject m A p))))"

(***************)
(*** Lemmata ***)
(***************)

lemma prefer_count_mirrored:
  assumes profile_on : "profile_on A p"
  assumes x_in_A : "x \<in> A"
  assumes y_in_A : "y \<in> A"
  assumes neq : "x \<noteq> y"
  shows "prefer_count p x y = (size p) - (prefer_count p y x)"
proof -
  have 00 :"card {i::nat. i < size p} = size p" by simp

  have 10 : "{i::nat. i < size p \<and> smaller y (p!i) x} = {i::nat. i < size p} - {i::nat. i < size p \<and> \<not> smaller y (p!i) x}"
    by blast

  have 0 : "\<forall> i::nat . i < size p \<longrightarrow> linear_order_on A (p!i)" using nth_mem profile_on profile_on_def by blast
  hence "\<forall> i::nat . i < size p \<longrightarrow> connex_on A (p!i)" by (simp add: linear_order_impl_connex)
  hence 1 :"\<forall> i::nat . i < size p \<longrightarrow> \<not> smaller y (p!i) x \<longrightarrow> smaller x (p!i) y"
    by (meson connex_on_def x_in_A y_in_A)

  from 0 have "\<forall> i::nat . i < size p \<longrightarrow> antisym  (p!i)" using lin_imp_antisym by blast
  hence "\<forall> i::nat . i < size p \<longrightarrow> (smaller y (p!i) x \<longrightarrow> \<not> smaller x (p!i) y)" by (meson antisymD neq)

  from this 1 have "\<forall> i::nat . i < size p \<longrightarrow> \<not> smaller y (p!i) x = smaller x (p!i) y"
    by blast
  hence 2 : "{i::nat. i < size p \<and> \<not> smaller y (p!i) x} = {i::nat. i < size p \<and> smaller x (p!i) y}" by blast

  then have 20: "{i::nat. i < size p \<and> smaller y (p!i) x} = {i::nat. i < size p} - {i::nat. i < size p \<and> smaller x (p!i) y}"
    by (simp add: "10" "2") 

  have " {i::nat. i < size p \<and> smaller x (p!i) y} \<subseteq> {i::nat. i < size p}"
    by blast
  hence 30 : "card ({i::nat. i < size p} - {i::nat. i < size p \<and> smaller x (p!i) y}) = (card {i::nat. i < size p}) - card({i::nat. i < size p \<and> smaller x (p!i) y})"
    by (simp add: card_Diff_subset)

  have "prefer_count p x y = card{i::nat. i < size p \<and> smaller y (p!i) x}" by blast
  also have "... = card({i::nat. i < size p} - {i::nat. i < size p \<and> smaller x (p!i) y})" by (simp add: "20")
  also have "... = (card {i::nat. i < size p}) - card({i::nat. i < size p \<and> smaller x (p!i) y})" using "30" by blast
  also have "... = size p - (prefer_count p y x)" by simp

  finally show ?thesis
    by (simp add: "20" "30")
qed


lemma prefer_count_symmetry:
    assumes p1 : "prefer_count p a x \<ge> prefer_count p x b"
    assumes profile_on : "profile_on A p"
    assumes a_in_A : "a \<in> A"
    assumes b_in_A : "b \<in> A"
    assumes x_in_A : "x \<in> A"
    assumes neq1 : "a \<noteq> x"
    assumes neq2 : "x \<noteq> b"
    shows "prefer_count p b x \<ge> prefer_count p x a" 
proof -
  from profile_on a_in_A x_in_A neq1 have 0 : "prefer_count p a x = (size p) - (prefer_count p x a)"
    by (metis (no_types, lifting) Collect_cong prefer_count_mirrored)
  moreover from profile_on x_in_A b_in_A  neq2 have 1 : "prefer_count p x b = (size p) - (prefer_count p b x)"
    by (metis (mono_tags, lifting) prefer_count_mirrored)
  hence 2 : "(size p) - (prefer_count p x a) \<ge> (size p) - (prefer_count p b x)"
    using calculation p1 by auto
  hence 3 :"(prefer_count p x a) - (size p) \<le> (prefer_count p b x) - (size p)"
    sorry 
  then have "(prefer_count p x a)  \<le> (prefer_count p b x) "
    using "1" "3" calculation p1 by linarith
  thus ?thesis
    by linarith
qed  


(* a wins against b implies b does not win against a *)
lemma only_one_can_win:
  shows "wins a p b \<Longrightarrow> \<not> wins b p a"
  by (simp add: wins_def)


lemma one_cant_win_against_himself:
  shows "\<not> wins w p w"
  by (meson only_one_can_win)


lemma unique_condorcet_winner:
  assumes winner_c: "condorcet_winner_in A p c" and
          winner_w: "condorcet_winner_in A p w"
  shows "w = c"
proof (rule ccontr)
  assume assumption: "w \<noteq> c"
  from winner_w have  "wins w p c" by (metis assumption condorcet_winner_in_def insert_Diff insert_iff winner_c) 
  hence "\<not> wins c p w" by (simp add: only_one_can_win)
  moreover from winner_c have c_wins_against_w : "wins c p w" by (meson Diff_iff assumption condorcet_winner_in_def singletonD winner_w)
  ultimately show False by simp
qed


lemma unique_condorcet_winner2:
  assumes winner: "condorcet_winner_in A p w" and
          not_w:  "x \<noteq> w" and
          in_A:   "x \<in> A"
  shows "\<not> condorcet_winner_in A p x"
  by (meson not_w unique_condorcet_winner winner)

lemma unique_condorcet_winner3:
  assumes "condorcet_winner_in A p w"
  shows "{a \<in> A. condorcet_winner_in A p a} = {w}"
  by (metis (mono_tags, lifting) Collect_cong assms condorcet_winner_in_def singleton_conv unique_condorcet_winner)

lemma condorcet_consistent_single_winner:
  shows "condorcet_consistent m \<longleftrightarrow> electoral_module m \<and> (
    \<forall> A p w. condorcet_winner_in A p w \<longrightarrow> (
      m A p = ({w},
               A - (elect m A p),
               {})))"
proof (auto)
  show "condorcet_consistent m \<Longrightarrow> electoral_module m"
    using condorcet_consistent_def by blast
next
  show "\<And>A p w.
       condorcet_consistent m \<Longrightarrow> condorcet_winner_in A p w \<Longrightarrow> m A p = ({w}, A - elect m A p, {})" by (simp add: condorcet_consistent_def unique_condorcet_winner3)
next
  show "electoral_module m \<Longrightarrow>
    \<forall>A p w. condorcet_winner_in A p w \<longrightarrow> m A p = ({w}, A - elect m A p, {}) \<Longrightarrow>
    condorcet_consistent m"
    by (simp add: condorcet_consistent_def unique_condorcet_winner3)
qed

lemma condorcet_compatibility_and_defer_deciding_implies_defer_only_winner:
  assumes ccomp : "condorcet_compatible m" and
          dd   : "defer_deciding m" and
          winner : "condorcet_winner_in A p w"
        shows "defer m A p = {w}"
proof (rule ccontr)
  assume not_w : "defer m A p \<noteq> {w}"

  from dd have "defers 1 m" using defer_deciding_def by blast
  then have "card (defer m A p) = 1" by (metis One_nat_def Suc_leI card_gt_0_iff condorcet_winner_in_def defers_def equals0D winner) 
  then have 0 : "\<exists>x \<in> A . defer m A p ={x}" by (metis card_1_singletonE condorcet_winner_in_def dd defer_deciding_def defer_from_input insert_subset winner)
  from this not_w have "\<exists>l \<in> A . l \<noteq> w \<and> defer m A p = {l}" by auto
  from this have not_in_defer : "w \<notin> defer m A p" by auto 

  have "non_electing m" using dd defer_deciding_def by blast
  from this have not_in_elect : "w \<notin> elect m A p" by (metis condorcet_winner_in_def equals0D non_electing_def winner) 

  from not_in_defer not_in_elect have one_side : "w \<in> reject m A p" by (metis ccomp condorcet_compatible_def condorcet_winner_in_def electoral_module_element_in_defer winner) 
  from ccomp have other_side : "w \<notin> reject m A p"
    by (metis (no_types, hide_lams) condorcet_compatible_def condorcet_winner_in_def winner) 
  
  then show False  by (simp add: one_side)   
qed

lemma condorcet_compatibility_and_defer_deciding_implies_defer_condorcet_consistency:
  assumes ccomp : "condorcet_compatible m" and
          dd   : "defer_deciding m"
        shows "defer_condorcet_consistent m"
proof (unfold defer_condorcet_consistent_def, auto)
  show "electoral_module m" using dd defer_deciding_def by blast
next
  fix A :: "'a set" and p :: "'a Profile" and w
  assume finiteness : "finite A" and winner : "condorcet_winner_in A p w"
  show "m A p = ({}, A - defer m A p, {d \<in> A. condorcet_winner_in A p d})"
  proof -
    (* Elect *)
    from dd have 0 : "elect m A p = {}" by (meson condorcet_winner_in_def defer_deciding_def non_electing_def winner) 

    (* Defers *)
    from dd ccomp have 1 : "defer m A p = {w}" by (simp add: condorcet_compatibility_and_defer_deciding_implies_defer_only_winner winner) 

    (* Reject *)
    from 0 1 have 2 : "reject m A p = A - defer m A p" by (metis Diff_empty condorcet_winner_in_def dd defer_deciding_def reject_alternative_representation winner)

    from 0 1 2 have 3 : "m A p = ({}, A - defer m A p, {w})" by (metis combine_ele_rej_def)

    have "{w} = {d \<in> A. condorcet_winner_in A p d}"
      using unique_condorcet_winner3 winner by fastforce

    thus ?thesis using "3" by auto
  qed
qed

end