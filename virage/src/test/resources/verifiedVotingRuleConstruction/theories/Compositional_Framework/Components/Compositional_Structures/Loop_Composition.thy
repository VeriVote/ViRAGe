(*  File:       Loop_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Loop Composition\<close>

theory Loop_Composition
  imports "../Termination_Condition"
          "../Basic_Modules/Defer_Module"
          Sequential_Composition

begin

text
\<open>The loop composition uses the same module in sequence,
combined with a termination condition, until either
  (1) the termination condition is met or
  (2) no new decisions are made (i.e., a fixed point is reached).\<close>

subsection \<open>Definition\<close>

lemma loop_termination_helper:
  assumes
    not_term: "\<not>t (acc A p)" and
    subset: "defer (acc \<triangleright> m) A p \<subset> defer acc A p" and
    not_inf: "\<not>infinite (defer acc A p)"
  shows
    "((acc \<triangleright> m, m, t, A, p), (acc, m, t, A, p)) \<in>
        measure (\<lambda>(acc, m, t, A, p). card (defer acc A p))"
  using assms psubset_card_mono
  by auto

(*
   This function handles the accumulator for the following loop composition
   function.
*)
function loop_comp_helper ::
    "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module" where
  "t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p) \<Longrightarrow>
      loop_comp_helper acc m t A p = acc A p" |
  "\<not>(t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
    infinite (defer acc A p)) \<Longrightarrow>
      loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
proof -
  fix
    P :: bool and
    x :: "('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
          ('a Termination_Condition) \<times> 'a set \<times> 'a Profile"
  assume
    a1: "\<And>t acc A p m.
          \<lbrakk>t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p);
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P" and
    a2: "\<And>t acc A p m.
          \<lbrakk>\<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
              infinite (defer acc A p));
            x = (acc, m, t, A, p)\<rbrakk> \<Longrightarrow> P"
  have "\<exists>f A p rs fa. (fa, f, p, A, rs) = x"
    using prod_cases5
    by metis
  then show P
    using a2 a1
    by (metis (no_types))
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = acca Aa pa"
    by fastforce
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
        infinite (defer acc A p) \<Longrightarrow>
          \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
          infinite (defer acca Aa pa)) \<Longrightarrow>
           (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
              acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
  proof -
    fix
      t :: "'a Termination_Condition" and
      acc :: "'a Electoral_Module" and
      A :: "'a set" and
      p :: "'a Profile" and
      m :: "'a Electoral_Module" and
      ta :: "'a Termination_Condition" and
      acca :: "'a Electoral_Module" and
      Aa :: "'a set" and
      pa :: "'a Profile" and
      ma :: "'a Electoral_Module"
    assume
      a1: "t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
            infinite (defer acc A p)" and
      a2: "\<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa))" and
      "(acc, m, t, A, p) = (acca, ma, ta, Aa, pa)"
    hence False
      using a2 a1
      by force
  thus "acc A p = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by auto
qed
next
  show
    "\<And>t acc A p m ta acca Aa pa ma.
       \<not> (t (acc A p) \<or> \<not> defer (acc \<triangleright> m) A p \<subset> defer acc A p \<or>
          infinite (defer acc A p)) \<Longrightarrow>
           \<not> (ta (acca Aa pa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa \<subset> defer acca Aa pa \<or>
            infinite (defer acca Aa pa)) \<Longrightarrow>
             (acc, m, t, A, p) = (acca, ma, ta, Aa, pa) \<Longrightarrow>
                loop_comp_helper_sumC (acc \<triangleright> m, m, t, A, p) =
                  loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa)"
    by force
qed
termination
proof -
  have f0:
    "\<exists>r. wf r \<and>
        (\<forall>p f A rs fa.
          p (f (A::'a set) rs) \<or>
          \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<or>
          infinite (defer f A rs) \<or>
          ((f \<triangleright> fa, fa, p, A, rs), (f, fa, p, A, rs)) \<in> r)"
    using loop_termination_helper wf_measure "termination"
    by (metis (no_types))
  hence
    "\<forall>r p.
      Ex ((\<lambda>ra. \<forall>f A rs pa fa. \<exists>ra pb rb pc pd fb Aa rsa fc pe.
        \<not> wf r \<or>
          loop_comp_helper_dom
            (p::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
              (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          infinite (defer f (A::'a set) rs) \<or>
          pa (f A rs) \<and>
            wf
              (ra::((
                ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
                ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times> _) set) \<and>
            \<not> loop_comp_helper_dom (pb::
                ('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
          wf rb \<and> \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<and>
            \<not> loop_comp_helper_dom
                (pc::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            ((f \<triangleright> fa, fa, pa, A, rs), f, fa, pa, A, rs) \<in> rb \<and> wf rb \<and>
            \<not> loop_comp_helper_dom
                (pd::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile) \<or>
            finite (defer fb (Aa::'a set) rsa) \<and>
            defer (fb \<triangleright> fc) Aa rsa \<subset> defer fb Aa rsa \<and>
            \<not> pe (fb Aa rsa) \<and>
            ((fb \<triangleright> fc, fc, pe, Aa, rsa), fb, fc, pe, Aa, rsa) \<notin> r)::
          ((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
            ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set \<Rightarrow> bool)"
    by metis
  obtain
    rr ::  "((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
             ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) \<times>
             ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
             ('a Termination_Condition) \<times> 'a set \<times> 'a Profile) set" where
      "wf rr \<and>
        (\<forall>p f A rs fa. p (f A rs) \<or>
          \<not> defer (f \<triangleright> fa) A rs \<subset> defer f A rs \<or>
          infinite (defer f A rs) \<or>
          ((f \<triangleright> fa, fa, p, A, rs), f, fa, p, A, rs) \<in> rr)"
    using f0
    by presburger
  thus ?thesis
    using "termination"
    by metis
qed

lemma loop_comp_code_helper[code]:
  "loop_comp_helper acc m t A p =
    (if (t (acc A p) \<or> \<not>((defer (acc \<triangleright> m) A p) \<subset> (defer acc A p)) \<or>
      infinite (defer acc A p))
    then (acc A p) else (loop_comp_helper (acc \<triangleright> m) m t A p))"
  by simp

function loop_composition ::
    "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow>
        'a Electoral_Module" where
  "t ({}, {}, A) \<Longrightarrow>
    loop_composition m t A p = defer_module A p" |
  "\<not>(t ({}, {}, A)) \<Longrightarrow>
    loop_composition m t A p = (loop_comp_helper m m t) A p"
  by (fastforce, simp_all)
termination
  using  "termination" wf_empty
  by blast

abbreviation loop ::
  "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow> 'a Electoral_Module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_composition m t"

lemma loop_comp_code[code]:
  "loop_composition m t A p =
    (if (t ({},{},A))
    then (defer_module A p) else (loop_comp_helper m m t) A p)"
  by simp

lemma loop_comp_helper_imp_partit:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "electoral_module acc \<and> (n = card (defer acc A p)) \<Longrightarrow>
        well_formed A (loop_comp_helper acc m t A p)"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    using electoral_module_def loop_comp_helper.simps(1)
          loop_comp_helper.simps(2) module_m profile
          psubset_card_mono seq_comp_sound
    by (smt (verit))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  assumes m_module: "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound electoral_module_def loop_composition.simps(1)
        loop_composition.simps(2) loop_comp_helper_imp_partit m_module
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(electoral_module acc \<and> n = card (defer acc A p)) \<Longrightarrow>
        defer (loop_comp_helper acc m t) A p \<subseteq> defer acc A p"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  thus ?case
    using dual_order.trans eq_iff less_imp_le loop_comp_helper.simps(1)
          loop_comp_helper.simps(2) module_m psubset_card_mono
          seq_comp_sound
    by (smt (verit, ccfv_SIG))
qed

subsection \<open>Lemmata\<close>



end
