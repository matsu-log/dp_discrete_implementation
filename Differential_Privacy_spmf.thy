section \<open>Differential Privacy\<close>

theory Differential_Privacy_spmf
  imports "HOL-Probability.Probability"
    "Differential_Privacy.Differential_Privacy_Standard"
begin

subsection \<open>Auxiliary Lemmas\<close>


lemma emeasure_spmf_bound:
  fixes A
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
    and "0<c"
  shows "emeasure (measure_spmf p) A \<le> c * emeasure (measure_spmf q) A"
proof -
  have "emeasure (measure_spmf p) A = \<integral>\<^sup>+ x. ennreal (spmf p x) \<partial>count_space A"
    by (simp add: nn_integral_spmf)
  moreover have "emeasure (measure_spmf q) A = \<integral>\<^sup>+ x. ennreal (spmf q x) \<partial>count_space A"
    by (simp add: nn_integral_spmf)
  ultimately show ?thesis
  proof (simp)
    have "(\<integral>\<^sup>+ x. ennreal (spmf p x) \<partial>count_space A)
        \<le> (\<integral>\<^sup>+ x. ennreal (c * spmf q x) \<partial>count_space A)"
      by (meson assms(1) ennreal_leI nn_integral_mono)
    also have "(\<integral>\<^sup>+ x. ennreal (c * spmf q x) \<partial>count_space A)
       =  (\<integral>\<^sup>+ x. ennreal c * ennreal (spmf q x) \<partial>count_space A)"
      using ennreal_mult'' by auto
    also have "... = ennreal c *  \<integral>\<^sup>+ x. ennreal (spmf q x) \<partial>count_space A"
    proof (rule nn_integral_cmult)
      show "(\<lambda>x. ennreal (spmf q x)) \<in> borel_measurable (count_space A)"
        by simp
    qed
    finally show "(\<integral>\<^sup>+ x. ennreal (spmf p x) \<partial>count_space A)
               \<le> ennreal c * \<integral>\<^sup>+ x. ennreal (spmf q x) \<partial>count_space A"
      by simp
  qed
qed

lemma measure_spmf_bound:
  fixes p q:: "'a spmf"
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
    and "0<c"
  shows "measure (measure_spmf p) A \<le> c * measure (measure_spmf q) A"
proof -
  have 1:"emeasure (measure_spmf p) A  \<le>  c * emeasure (measure_spmf q) A"
    using emeasure_spmf_bound assms by auto
  have 2:"emeasure (measure_spmf q) A < \<top>"
    using measure_spmf.emeasure_finite[of "q" "A"] less_top
    by blast
  then show ?thesis
    unfolding measure_def
    using 1 2 assms
    by (simp add: enn2real_leI ennreal_mult')
qed

lemma lossless_spmf_imp_measurable_as_measure:
  assumes "\<And>x. lossless_spmf (M x)"
  shows "measure_spmf \<circ> M \<in> (count_space UNIV) \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
proof(rewrite measurable_count_space_eq1)
  show "measure_spmf \<circ> M \<in> UNIV \<rightarrow> space (prob_algebra (count_space UNIV))"
  proof
    fix x
    have "emeasure (measure_spmf (M x)) (space (measure_spmf (M x))) = 1"
      using assms space_measure_spmf[of "M x"]
      unfolding lossless_spmf_def weight_spmf_def
      by (simp add: measure_spmf.emeasure_eq_measure)
    then have "prob_space (measure_spmf (M x))"
      by (rule prob_spaceI)
    then show "(measure_spmf \<circ> M) x \<in> space (prob_algebra (count_space UNIV))"
      apply(rewrite space_prob_algebra)
      by(auto)
  qed
qed

subsection \<open>Define pure_dp\<close>

paragraph \<open>type_synonym for query, mechanism.\<close>

text \<open>Regarding lists as datasets\<close>

type_synonym ('a, 'b) query = "'a list \<Rightarrow> 'b"

type_synonym ('a, 'b) mechanism = "'a list \<Rightarrow> 'b spmf"

paragraph \<open>Adjacency of Datasets.\<close>
  (*
  Adjacency of two lists has 3 patterns.
    Addition: l2 has an additional element than l1
    Deletion: l2 miss an element than l2
    Update: l2 differs by one element compared to l1
*)
inductive neighbour :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  Addition: "l1 = a @ b \<Longrightarrow> l2= a @ [n] @ b \<Longrightarrow> neighbour l1 l2" |
  Deletion: "l1 = a @ [n] @ b \<Longrightarrow> l2 = a @ b \<Longrightarrow> neighbour l1 l2" |
  Update:   "l1= a @ [n] @ b \<Longrightarrow> l2= a @ [m] @ b \<Longrightarrow> neighbour l1 l2"

definition adj :: "('a list) rel" where
  "adj = {(l1,l2). neighbour l1 l2}"

paragraph \<open>Definition of pure differential privacy with adjacency, and its basic properties\<close>

definition pure_dp_inequality :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> real \<Rightarrow> bool" where
  "pure_dp_inequality M N \<epsilon> = DP_inequality (measure_spmf M) (measure_spmf N) \<epsilon> 0"

definition pure_dp :: "('a,'b) mechanism \<Rightarrow> real \<Rightarrow> bool" where
  "pure_dp M \<epsilon> = differential_privacy (measure_spmf \<circ> M) adj \<epsilon> 0"

definition is_sensitivity :: "('a, int) query \<Rightarrow> nat \<Rightarrow> bool" where
  "is_sensitivity q \<Delta> = (\<forall>(l1, l2)\<in>adj. \<bar>q l1 - q l2\<bar>\<le> \<Delta>)"

definition postprocess :: "('a, 'b) mechanism \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>  'a list \<Rightarrow> 'c spmf" where
  "postprocess M pp l = do {
  A \<leftarrow> M l;
  return_spmf (pp A)
}"

subsection \<open>lemmas for pure_dp\<close>

lemma adj_sym: "sym adj"
  unfolding adj_def neighbour.simps sym_def
  by fast

lemma pure_dp_inequality_imp_pure_dp:
  assumes "\<forall>(l1, l2)\<in>adj. pure_dp_inequality (M l1) (M l2) \<epsilon>"
  shows "pure_dp M \<epsilon>"
  unfolding pure_dp_def
proof(rewrite differential_privacy_adj_sym)
  show "sym adj" by (simp add: adj_sym)
  show "\<forall>(d1, d2)\<in>adj. DP_inequality ((measure_spmf \<circ> M) d1) ((measure_spmf \<circ> M) d2) \<epsilon> 0"
    using assms
    unfolding pure_dp_inequality_def o_def
    by auto
qed

lemma sensitivity:
  assumes "is_sensitivity q \<Delta>"
    and "(l1, l2)\<in>adj"
  shows "\<bar>q l1 - q l2\<bar>\<le> \<Delta>"
  using assms
  unfolding is_sensitivity_def
  by auto

lemma pointwise_spmf_bound_imp_pure_dp:
  fixes M::"('a, 'b) mechanism"
  assumes "\<And>z l1 l2. (l1, l2)\<in>adj \<Longrightarrow> spmf (M l1)z \<le> exp (\<epsilon>) * spmf (M l2)z"
  shows "pure_dp M \<epsilon>"
proof(rule pure_dp_inequality_imp_pure_dp,clarify)
  fix h1 h2:: "'a list"
  assume adj:"(h1, h2)\<in> adj"
  show "pure_dp_inequality (M h1) (M h2) \<epsilon>"
    unfolding pure_dp_inequality_def DP_inequality_def
  proof
    fix A
    show "Sigma_Algebra.measure (measure_spmf (M h1)) A \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M h2)) A+0"
      using measure_spmf_bound[of "M h1" "exp(\<epsilon>)" "M h2"] assms[of "h1" "h2"] exp_gt_zero adj
      by simp
  qed
qed

lemma dp_postprocess_theorem:
  assumes "pure_dp M \<epsilon>"
  shows "pure_dp (postprocess M pp) \<epsilon>"
  unfolding pure_dp_def
proof(rewrite differential_privacy_adj_sym)
  show "sym adj" by (rule adj_sym)
  show "\<forall>(d1, d2)\<in>adj. DP_inequality ((measure_spmf \<circ> postprocess M pp) d1) ((measure_spmf \<circ> postprocess M pp) d2) \<epsilon> 0"
  proof clarify
    fix l1 l2:: "'a list"
    assume adj:"(l1, l2) \<in> adj"
    have p:"DP_inequality (measure_spmf (M l1)) (measure_spmf (M l2)) \<epsilon> 0"
      using assms pure_dp_def[of "M" "\<epsilon>"] adj
      unfolding o_def differential_privacy_def
      by auto
    show " DP_inequality ((measure_spmf \<circ> postprocess M pp) l1) ((measure_spmf \<circ> postprocess M pp) l2) \<epsilon> 0"
      unfolding DP_inequality_def postprocess_def
    proof
      fix A
      have l1:"Sigma_Algebra.measure (measure_spmf (M l1 \<bind> (\<lambda>A. return_spmf (pp A)))) A
          = measure (measure_spmf (map_spmf pp (M l1))) A"
        using map_spmf_conv_bind_spmf by metis
      have l2:"Sigma_Algebra.measure (measure_spmf (M l2 \<bind> (\<lambda>A. return_spmf (pp A)))) A
          = measure (measure_spmf (map_spmf pp (M l2))) A"
        using map_spmf_conv_bind_spmf by metis
      have "measure (measure_spmf (map_spmf pp (M l1))) A \<le> exp \<epsilon> * measure (measure_spmf (map_spmf pp (M l2))) A"
        apply(rewrite measure_map_spmf)
        apply(rewrite measure_map_spmf)
        using p unfolding DP_inequality_def
        by auto
      then show "Sigma_Algebra.measure ((measure_spmf \<circ> (\<lambda>l. M l \<bind> (\<lambda>A. return_spmf (pp A)))) l1) A \<le> exp \<epsilon> * Sigma_Algebra.measure ((measure_spmf \<circ> (\<lambda>l. M l \<bind> (\<lambda>A. return_spmf (pp A)))) l2) A + 0"
        using l1 l2 by simp
    qed
  qed
qed

(*
(* use differential_privacy_postprocess, but proof is incomplete due to differences in definitions of postprocess.*)

lemma dp_postprocess_theorem':
  assumes "pure_dp M \<epsilon>" and "0 \<le> \<epsilon>"
and lossless_M:"\<And>x. lossless_spmf (M x)"
  shows "pure_dp (postprocess M pp) \<epsilon>"
proof -
  have 1:"measure_spmf \<circ> M \<in> count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using lossless_M lossless_spmf_imp_measurable_as_measure by auto
  have 2:"(\<lambda>x. measure_pmf (return_pmf (pp x))) \<in> count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    sorry
  have 3:"(\<lambda>x. measure_spmf (M x) \<bind> (\<lambda>y. measure_pmf (return_pmf (pp y)))) =(\<lambda>x. measure_spmf (M x \<bind> (\<lambda>A. return_spmf (pp A))))"
    sorry
  show ?thesis
    using differential_privacy_postprocessing[of "\<epsilon>" "measure_spmf \<circ> M" "adj" "0" "count_space UNIV" "count_space UNIV" "\<lambda>A. return_pmf (pp A)" "count_space UNIV"]
          assms 1 2 3
    unfolding pure_dp_def o_def postprocess_def
    by simp
qed
*)

lemma prod_measurable:
  fixes N::"'a list \<times>'b \<Rightarrow> 'c spmf"
  assumes "\<And>x y. lossless_spmf (N (x,y))"
    and "countable (UNIV:: ('a list) set)"
    and "countable (UNIV::'b set)"
  shows "measure_spmf \<circ> N \<in> count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
  unfolding o_def
  apply(rewrite pair_measure_countable)
  using assms apply simp_all
  using  lossless_spmf_imp_measurable_as_measure assms
  by force

lemma pure_dp_comp:
  fixes M::"('a, 'b) mechanism" and N::"'a list \<times> 'b \<Rightarrow>'c spmf"
  assumes M:"pure_dp M \<epsilon>"
    and N:"\<And>y. pure_dp (\<lambda> x. N (x,y)) \<epsilon>'"
    and lossless_M:"\<And>x. lossless_spmf (M x)"
    and lossless_N:"\<And>x y. lossless_spmf (N (x,y))"
    and "0\<le>\<epsilon>" and "0\<le>\<epsilon>'"
    and "countable (UNIV::'a list set)" and "countable (UNIV::'b set)"
  shows "pure_dp (\<lambda>x. bind_spmf  (M x) (\<lambda>y. N (x, y))) (\<epsilon>+\<epsilon>')"
  unfolding pure_dp_def
proof -
  have 1:" \<And>y. (\<lambda>x. (measure_spmf \<circ> N) (x, y)) = (measure_spmf \<circ> (\<lambda>x. N (x, y)))"
    unfolding o_def
    by simp
  have 2:"(\<lambda>x. (measure_spmf \<circ> M) x \<bind> (\<lambda>y. (measure_spmf \<circ> N) (x, y))) = (measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y))))"
    using measure_spmf_bind
    unfolding o_def
    by metis
  have 3:"measure_spmf \<circ> M \<in> (count_space UNIV) \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using lossless_M lossless_spmf_imp_measurable_as_measure
    by auto
  have 4:"measure_spmf \<circ> N \<in> count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using assms prod_measurable by blast
  have 5:"differential_privacy (measure_spmf \<circ> M) adj \<epsilon> 0 "
    using M unfolding pure_dp_def by simp
  have 6:"\<forall>y\<in>space (count_space UNIV). differential_privacy (\<lambda>x. (measure_spmf \<circ> N) (x, y)) adj \<epsilon>' 0"
    using N unfolding pure_dp_def
    by (simp add: o_def)
  have "differential_privacy (\<lambda>x. (measure_spmf \<circ> M) x \<bind> (\<lambda>y. (measure_spmf \<circ> N) (x, y))) adj (\<epsilon> + \<epsilon>') (0 + 0)"
    using differential_privacy_composition_adaptive[of "\<epsilon>" "\<epsilon>'" "measure_spmf \<circ> M" "count_space UNIV" "count_space UNIV" "adj" "0"
        "measure_spmf \<circ> N" "count_space UNIV"]
      3 4 5 6 assms
    by auto
  then show "differential_privacy (measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y)))) adj (\<epsilon> + \<epsilon>') 0"
    using 2 by simp
qed

(* use differential_privacy_composition_adaptive' and without the assumption of countability*)

lemma pure_dp_comp':
  fixes M::"('a, 'b) mechanism" and N::"'a list \<times> 'b \<Rightarrow>'c spmf"
  assumes M:"pure_dp M \<epsilon>"
    and N:"\<And>y. pure_dp (\<lambda> x. N (x,y)) \<epsilon>'"
    and lossless_M:"\<And>x. lossless_spmf (M x)"
    and lossless_N:"\<And>x y. lossless_spmf (N (x,y))"
    and "0\<le>\<epsilon>" and "0\<le>\<epsilon>'"
  shows "pure_dp (\<lambda>x. bind_spmf  (M x) (\<lambda>y. N (x, y))) (\<epsilon>+\<epsilon>')"
  unfolding pure_dp_def
proof -
  have 1:"(measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y)))) = (\<lambda>x. (measure_spmf \<circ> M) x \<bind> (\<lambda>y. (measure_spmf \<circ> N) (x, y)))"
    using measure_spmf_bind unfolding o_def by metis
  have 2:"measure_spmf \<circ> M \<in> count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using lossless_M lossless_spmf_imp_measurable_as_measure by auto
  have 3:"\<forall>x\<in>space (count_space UNIV). (\<lambda>y. (measure_spmf \<circ> N) (x, y)) \<in> count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using lossless_N lossless_spmf_imp_measurable_as_measure unfolding o_def by metis
  have 4:"differential_privacy (measure_spmf \<circ> M) adj \<epsilon> 0"
    using assms unfolding pure_dp_def by simp
  have 5:"\<forall>y\<in>space (count_space UNIV). differential_privacy (\<lambda>x. (measure_spmf \<circ> N) (x, y)) adj \<epsilon>' 0 "
    using assms unfolding pure_dp_def o_def by simp
  show "differential_privacy (measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y)))) adj (\<epsilon> + \<epsilon>') 0 "
    using differential_privacy_composition_adaptive'[of "\<epsilon>" "\<epsilon>'" "measure_spmf \<circ> M" "count_space UNIV" "count_space UNIV" "adj" "0" "measure_spmf \<circ> N" "count_space UNIV" "0"]
      assms 1 2 3 4 5
    by simp
qed

end