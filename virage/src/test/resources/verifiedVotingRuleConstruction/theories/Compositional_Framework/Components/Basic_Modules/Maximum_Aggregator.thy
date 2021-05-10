(*  File:       Maximum_Aggregator.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Maximum Aggregator\<close>

theory Maximum_Aggregator
  imports "../Aggregator"
begin

text
\<open>The max(imum) aggregator takes two partitions of an alternative set A as
input. It returns a partition where every alternative receives the maximum
result of the two input partitions.\<close>

subsection \<open>Definition\<close>

fun max_aggregator :: "'a Aggregator" where
  "max_aggregator A (e1, r1, d1) (e2, r2, d2) =
    (e1 \<union> e2,
     A - (e1 \<union> e2 \<union> d1 \<union> d2),
     (d1 \<union> d2) - (e1 \<union> e2))"

subsection \<open>Auxiliary Lemma\<close>

lemma max_agg_rej_set: "(well_formed A (e1, r1, d1) \<and>
                          well_formed A (e2, r2, d2)) \<longrightarrow>
           reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
proof -
  have "well_formed A (e1, r1, d1) \<longrightarrow>  A - (e1 \<union> d1) = r1"
    by (simp add: result_imp_rej)
  moreover have
    "well_formed A (e2, r2, d2) \<longrightarrow>  A - (e2 \<union> d2) = r2"
    by (simp add: result_imp_rej)
  ultimately have
    "(well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
        A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by blast
  moreover have
    "{l \<in> A. l \<notin> e1 \<union> e2 \<union> d1 \<union> d2} = A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by (simp add: set_diff_eq)
  ultimately show ?thesis
    by simp
qed

subsection \<open>Soundness\<close>

theorem max_agg_sound[simp]: "aggregator max_aggregator"
  unfolding aggregator_def
proof (simp, safe)
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    asm1: "e2 \<union> r2 \<union> d2 = e1 \<union> r1 \<union> d1" and
    asm2: "x \<notin> d1" and
    asm3: "x \<notin> r1" and
    asm4: "x \<in> e2"
  show "x \<in> e1"
    using asm1 asm2 asm3 asm4
    by auto
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set" and
    x :: "'a"
  assume
    asm1: "e2 \<union> r2 \<union> d2 = e1 \<union> r1 \<union> d1" and
    asm2: "x \<notin> d1" and
    asm3: "x \<notin> r1" and
    asm4: "x \<in> d2"
  show "x \<in> e1"
    using asm1 asm2 asm3 asm4
    by auto
qed

end
