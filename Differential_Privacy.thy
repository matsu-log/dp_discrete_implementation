section \<open>Differential Privacy\<close>

theory Differential_Privacy
  imports "HOL-Probability.Probability"
begin

(*
This section is based on SampCert
*)

type_synonym ('a, 'b) query = "'a list \<Rightarrow> 'b"

type_synonym ('a, 'b) mechanism = "'a list \<Rightarrow> 'b spmf"

(*
  Adjacency of two lists has 3 patterns.
    Addition: l2 has an additional element than l1
    Deletion: l2 miss an element than l2
    Update: l2 differs by one element compared to l1
*)
inductive Neighbour :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  Addition: "l1 = a @ b \<Longrightarrow> l2= a @ [n] @ b \<Longrightarrow> Neighbour l1 l2" |
  Deletion: "l1 = a @ [n] @ b \<Longrightarrow> l2 = a @ b \<Longrightarrow> Neighbour l1 l2" |
  Update:   "l1= a @ [n] @ b \<Longrightarrow> l2= a @ [m] @ b \<Longrightarrow> Neighbour l1 l2"

definition is_sensitivity :: "('a, int) query \<Rightarrow> nat \<Rightarrow> bool" where
"is_sensitivity q \<Delta> = (\<forall>l1 l2. Neighbour l1 l2 \<longrightarrow> \<bar>q l1 - q l2\<bar>\<le> \<Delta>)"

definition Pure_DP_inequality :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> real \<Rightarrow> bool" where
"Pure_DP_inequality M N \<epsilon> = (\<forall>A::'a set. measure (measure_spmf M) A \<le> exp( \<epsilon>) * measure (measure_spmf N) A)"

definition Pure_DP :: "('a,'b) mechanism \<Rightarrow> real \<Rightarrow> bool" where
"Pure_DP M \<epsilon> = (\<forall>l1 l2. Neighbour l1 l2 \<longrightarrow> Pure_DP_inequality (M l1) (M l2) \<epsilon>)"

definition postprocess :: "('a, 'b) mechanism \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>  'a list \<Rightarrow> 'c spmf" where
"postprocess M pp l = do {
  A \<leftarrow> M l;
  return_spmf (pp A)
}"

lemma sensitivity:
  assumes "is_sensitivity q \<Delta>"
and "Neighbour l1 l2"
shows "\<bar>q l1 - q l2\<bar>\<le> \<Delta>"
  using assms 
  unfolding is_sensitivity_def
  by simp



lemma pure_dp:
  fixes M::"('a,'b) mechanism"
  assumes "\<And>z l1 l2. Neighbour l1 l2 \<Longrightarrow> spmf (M l1)z \<le> exp (\<epsilon>) * spmf (M l2)z"
shows "Pure_DP M \<epsilon>"
  unfolding Pure_DP_def
proof (rule+)
  fix h1 h2:: "'a list"
  assume neighbour:"Neighbour h1 h2"
  show "Pure_DP_inequality (M h1) (M h2) \<epsilon>"
    unfolding Pure_DP_inequality_def
  proof
    fix A::"'b set"
    show "Sigma_Algebra.measure (measure_spmf (M h1)) A \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M h2)) A"
    
      term"countably_additive"
      term "pmf"
      find_theorems "countable"
      term "countable"
      term "prob_space"
      term "sigma_finite_measure"
      term "almost_everywhere"

lemma dp_postprocess_theorem:
  assumes "Pure_DP M \<epsilon>"
  shows "Pure_DP (postprocess M pp) \<epsilon>"
  unfolding Pure_DP_def
proof (rule+)
  fix l1 l2:: "'a list" 
  assume neighbour:"Neighbour l1 l2"
  have p:"Pure_DP_inequality (M l1) (M l2) \<epsilon>"
    using assms Pure_DP_def[of "M" "\<epsilon>"] neighbour
    by blast
  show "Pure_DP_inequality (postprocess M pp l1) (postprocess M pp l2) \<epsilon>"
    unfolding Pure_DP_inequality_def postprocess_def 
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
      using p unfolding Pure_DP_inequality_def
      by auto
    then show "Sigma_Algebra.measure (measure_spmf (M l1 \<bind> (\<lambda>A. return_spmf (pp A)))) A
         \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M l2 \<bind> (\<lambda>A. return_spmf (pp A)))) A"
      using l1 l2 by simp
  qed
qed
 



end