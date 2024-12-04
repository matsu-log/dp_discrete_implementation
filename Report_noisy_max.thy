section \<open>Report Noisy Max with discrete laplace distribution\<close>

theory Report_noisy_max
  imports Discrete_laplace_rat
          Differential_Privacy2
          formalization.Differential_Privacy_Example_Report_Noisy_Max
          Discrete_laplace_mechanism
begin

primrec argmax_int_list :: "int list \<Rightarrow> (int \<times> nat)" where
"argmax_int_list [] = (0,0)"|
"argmax_int_list (x#xs) = (if xs = [] then (x,0) else (let (m,i) = argmax_int_list xs in (if x>m then (x,0) else (m,i+1))))"

primrec discrete_laplace_noise_add_list :: "(('a, int) query) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (int list) spmf" where
"discrete_laplace_noise_add_list [] epsilon1 epsilon2  ls = return_spmf []"|
"discrete_laplace_noise_add_list (c#cs) epsilon1 epsilon2 ls = 
do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list cs epsilon1 epsilon2 ls;
  noisy_c \<leftarrow> discrete_laplace_mechanism c 1 epsilon1 epsilon2 ls;
  return_spmf (noisy_c  # noisy_cs)
}"

definition report_noisy_max:: "(('a, int) query) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat spmf" where
"report_noisy_max cs epsilon1 epsilon2 x = do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list cs epsilon1 epsilon2 x;
  return_spmf (snd (argmax_int_list noisy_cs))
}
"

primrec is_count_queries :: "(('a, int) query) list \<Rightarrow> bool" where
"is_count_queries [] = True" |
"is_count_queries (c#cs) = (if is_sensitivity c 1 then is_count_queries cs else False)"

subsection \<open>component function\<close>
lemma argmax_int_list_index_le_length:
"snd (argmax_int_list list) \<le>length list"
proof (induct list)
  case Nil
  then show ?case 
    unfolding argmax_int_list.simps by simp
next
  case (Cons a list)
  then show ?case 
    unfolding argmax_int_list.simps Let_def snd_def
    by (simp add: prod.case_eq_if)
qed

lemma argmax_int_list_fst: 
shows "length list > 0 \<Longrightarrow>fst (argmax_int_list list)= Max (set list)"
proof(induct list)
  case Nil
  then show ?case
    by simp
next
  case (Cons a list)
  then show ?case
    unfolding argmax_int_list.simps fst_def
    apply (simp add: prod.case_eq_if)
    by (metis List.finite_set Max_ge_iff max.absorb_iff2 not_le_imp_less set_empty2)
qed

lemma argmax_int_list_snd:
  shows "length list > 0 \<Longrightarrow>nth list (snd (argmax_int_list list)) =  fst (argmax_int_list list)"
proof(induct list)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case 
    unfolding argmax_int_list.simps snd_def fst_def
    by(simp add: prod.case_eq_if)
qed

lemma count_queries:
  shows "is_count_queries cs \<Longrightarrow> \<forall> c\<in> (set cs). is_sensitivity c 1"
proof (induct cs)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
  proof(clarify)
    fix c
    assume c:"c \<in> set (a # cs)"
    then show "is_sensitivity c 1"
      apply(cases "c \<in> set cs")
      using Cons is_count_queries.simps(2)[of "a" "cs"]
       apply(presburger)
      apply(cases "a\<in> set cs",simp)
      using Cons is_count_queries.simps(2)[of "a" "cs"]
      by(simp,argo)
  qed
qed


  
lemma lossless_discrete_laplace_noise_add_list:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
  shows "lossless_spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 ls)"
proof (induct cs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)
  then show ?case
    using lossless_discrete_laplace_mechanism[of"epsilon1" "epsilon2" "1"] assms
    by(auto)
qed

lemma lossless_report_noisy_max:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
  shows "lossless_spmf (report_noisy_max cs epsilon1 epsilon2 x)"
  unfolding report_noisy_max_def
  using lossless_discrete_laplace_noise_add_list assms
  by simp

lemma pointwise_pure_dp_inequality_report_noisy_max:
  assumes "is_count_queries cs"
and "(x,y)\<in>adj"
and "n = length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
shows "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z\<le> exp(epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
proof -
  fix z::nat
  show "spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
    unfolding report_noisy_max_def
  proof -

    sorry
qed

lemma pure_dp_report_noisy_max:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "is_count_queries cs"
  shows "pure_dp (report_noisy_max cs epsilon1 epsilon2) (epsilon1/epsilon2)"
  using pointwise_pure_dp_inequality_report_noisy_max[of "cs" _ _ "epsilon1" "epsilon2"]
        pointwise_spmf_bound_imp_pure_dp_nat[of "(\<lambda>l. report_noisy_max cs epsilon1 epsilon2 l)" "epsilon1/epsilon2"] 
        assms
  by simp
  
  
  





end
