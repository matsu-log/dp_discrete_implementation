section \<open>Discrete Laplace Mechanism\<close>

theory Discrete_laplace_mechanism
  imports "sampler/Discrete_Laplace_rat"
          Differential_Privacy_spmf
begin 

subsection \<open>Integer Query: SampCert Implementation\<close>
(* 
  query returns integar value
  epsilon = epsilon1/epsilon2 (1\<le>epsilon1,epsilon2)
  \<Delta> is sensitivity of f:: nat
  this is same as implementation of SampCert
*)

definition discrete_laplace_mechanism :: "('a list \<Rightarrow> int) \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> int spmf" where
"discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x = 
  do { noise \<leftarrow> discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1;
       return_spmf (noise + f x)
    }"

lemma lossless_discrete_laplace_mechanism:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le> \<Delta>"
shows "lossless_spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x)"
  unfolding discrete_laplace_mechanism_def
  using lossless_discrete_laplace_rat[of "epsilon2 * \<Delta>" "epsilon1"] assms
  by simp
  
lemma spmf_discrete_laplace_mechanism:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le> \<Delta>"
shows "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1)/(exp (epsilon1/(epsilon2*\<Delta>))+1) * exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))"
proof -
  have "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z 
        = spmf (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1 \<bind> (\<lambda>noise. return_spmf (noise + f x))) z"
    unfolding discrete_laplace_mechanism_def by simp
  also have "... = spmf (map_spmf (\<lambda>noise. noise + f x) (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1)) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z = spmf (map_spmf (\<lambda>noise. noise + f x) (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1)) z"
    by simp
  have "(\<lambda>noise. noise + f x) -` {z} = {z - f x}"
    by auto
  then have 2:"spmf (map_spmf (\<lambda>noise. noise + f x) (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1)) z = spmf (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1) (z-f x)"  
    apply(simp add: spmf_map)
    by(simp add: spmf_conv_measure_spmf)    
  have 3:"... = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
    using assms spmf_discrete_laplace_rat    
    by simp
  show ?thesis
    using 1 2 3 by simp
qed

lemma pointwise_pure_dp_inequality_discrete_laplace_mechanism:
  assumes "is_sensitivity f \<Delta>"
and "(x, y)\<in> adj"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le> \<Delta>"
shows "\<And>z. spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z"
proof -
  fix z::int
  have 1:"spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
    using assms spmf_discrete_laplace_mechanism[of "epsilon1" "epsilon2" "\<Delta>" "f" "x" "z"]
    by(simp)
  have 2:"spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
    using assms spmf_discrete_laplace_mechanism[of "epsilon1" "epsilon2" "\<Delta>" "f" "y" "z"]
    by simp
  have 3:"spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z/spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z = exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/exp (-(epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)))"
    apply(rewrite 1)
    apply(rewrite 2)
    apply(auto)
    using assms apply(simp_all)
  proof -
    have "exp (real epsilon1 / (real epsilon2 * real \<Delta>)) + 1 > 0"
      using exp_gt_zero add_pos_pos zero_less_one
      by blast
    then show "exp (real epsilon1 / (real epsilon2 * real \<Delta>)) + 1 = 0 \<Longrightarrow> False"
      by simp
  qed
  also have "... = exp (-epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>) - (-epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)))"
    using exp_diff[of"-epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)" "-epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)"]
    by simp
  also have "... = exp ((epsilon1*\<bar>z-(f y)\<bar>-epsilon1*\<bar>z-(f x)\<bar>)/(epsilon2*\<Delta>))"
    using diff_divide_distrib[of "-epsilon1*\<bar>z-(f x)\<bar>" "-epsilon1*\<bar>z-(f y)\<bar>" "(epsilon2*\<Delta>)"]
    by simp
  also have "... = exp ((epsilon1*(\<bar>z-(f y)\<bar>-\<bar>z-(f x)\<bar>))/(epsilon2*\<Delta>))"
    using int_distrib(4) by presburger
  also have "... \<le> exp ((epsilon1*\<bar>f x - f y\<bar>)/(epsilon2*\<Delta>))"
  proof -
    have "\<bar>z-(f y)\<bar>-\<bar>z-(f x)\<bar> \<le> \<bar>f x - f y\<bar>"
      by simp
    then have 1:"epsilon1*(\<bar>z-(f y)\<bar>-\<bar>z-(f x)\<bar>) \<le> epsilon1*\<bar>f x - f y\<bar>"
      using assms by simp
    have 2:"0 \<le> epsilon2*\<Delta>"
      using assms by simp
    have "(epsilon1*(\<bar>z-(f y)\<bar>-\<bar>z-(f x)\<bar>))/(epsilon2*\<Delta>) \<le> (epsilon1*\<bar>f x - f y\<bar>)/(epsilon2*\<Delta>)"
      using 1 2 divide_right_mono[of "epsilon1*(\<bar>z-(f y)\<bar>-\<bar>z-(f x)\<bar>)" "epsilon1*\<bar>f x - f y\<bar>" "(epsilon2*\<Delta>)"] 
      by linarith
    then show ?thesis 
      by simp
  qed
  also have "... \<le> exp ((epsilon1*\<Delta>)/(epsilon2*\<Delta>))"
  proof 
    have 1:"epsilon1 * \<bar>f x - f y\<bar> \<le> epsilon1 * \<Delta>"
      using assms sensitivity by simp
    have 2:"0 \<le> epsilon2*\<Delta>"
      using assms by simp
    show "epsilon1 * \<bar>f x - f y\<bar>/(epsilon2*\<Delta>) \<le> epsilon1 * \<Delta>/(epsilon2*\<Delta>)"
      using 1 2 divide_right_mono[of "epsilon1 * \<bar>f x - f y\<bar>" "epsilon1 * \<Delta>" "epsilon2*\<Delta>"]
      by linarith
  qed
  also have "... = exp(epsilon1/epsilon2)"
    using assms by simp
  finally have p:"spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z / spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z \<le> exp (epsilon1 /epsilon2)"
    by simp
  show "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z"
  proof -
    have "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z = spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z * (spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z/ spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z)"
    proof -
      have "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z / spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z = 1"
      using divide_self[of "spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z"] 
      apply(simp)
      using 3
      by auto
      then show ?thesis by auto
    qed
    also have "... = spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x) z / spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z * spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z"
      by simp      
    also have "... \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 y) z"
      apply(rewrite mult_right_mono)
      using p 
      by(simp_all)
    finally show ?thesis
      by simp
  qed
qed

lemma pure_dp_discrete_laplace_mechanism:
  assumes "is_sensitivity f \<Delta>"
and "1 \<le> epsilon1"
and "1 \<le> epsilon2"
and "1 \<le> \<Delta>"
shows "pure_dp (discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2) (epsilon1/epsilon2)"
  using pointwise_pure_dp_inequality_discrete_laplace_mechanism[of "f" "\<Delta>" "_" "_" "epsilon1" "epsilon2"]
        pointwise_spmf_bound_imp_pure_dp[of "(\<lambda>l. discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 l)" "epsilon1/epsilon2"] 
        assms 
  by simp
      


end