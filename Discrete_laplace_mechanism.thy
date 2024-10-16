section \<open>Discrete Laplace Mechanism\<close>

theory Discrete_laplace_mechanism
  imports Discrete_laplace_rat
begin 

subsection \<open>Integer Query: SampCert Implementation\<close>
(*
  Reference:
  https://github.com/leanprover/SampCert/blob/main/SampCert/DifferentialPrivacy/Pure/Mechanism/Code.lean
*)

(* 
  query returns integar value
  epsilon = epsilon1/epsilon2 (1\<le>epsilon1,epsilon2)
  \<Delta> is sensitivity of f:: nat
  this is same as implementation of SampCert
*)

definition discrete_laplace_mechanism :: "('a list \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int spmf" where
"discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2  = do { 
                                                            noise \<leftarrow> discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1;
                                                            return_spmf (noise + f x)
}"

lemma spmf_discrete_laplace_mechanism:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le> \<Delta>"
shows "spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
proof -
  have "spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z 
        = spmf (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1 \<bind> (\<lambda>noise. return_spmf (noise + f x))) z"
    unfolding discrete_laplace_mechanism_def by simp
  also have "... = spmf (map_spmf (\<lambda>noise. noise + f x) (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1)) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z = spmf (map_spmf (\<lambda>noise. noise + f x) (discrete_laplace_rat (epsilon2 * \<Delta>) epsilon1)) z"
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

lemma pure_dp_discrete_laplace_mechanism:
  assumes "\<bar>f x - f y\<bar> \<le> \<Delta>"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le> \<Delta>"
  shows "\<And>z. spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z"
proof -
  fix z::int
  have 1:"spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
    using assms spmf_discrete_laplace_mechanism[of "epsilon1" "epsilon2" "\<Delta>" "f" "x" "z"]
    by(simp)
  have 2:"spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z = (exp (epsilon1 /(epsilon2*\<Delta>))-1) * exp (-(epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)))/(exp (epsilon1/(epsilon2*\<Delta>))+1)"
    using assms spmf_discrete_laplace_mechanism[of "epsilon1" "epsilon2" "\<Delta>" "f" "y" "z"]
    by simp
  have 3:"spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z/spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z = exp (-(epsilon1*\<bar>z-(f x)\<bar>/(epsilon2*\<Delta>)))/exp (-(epsilon1*\<bar>z-(f y)\<bar>/(epsilon2*\<Delta>)))"
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
      using assms by simp
    have 2:"0 \<le> epsilon2*\<Delta>"
      using assms by simp
    show "epsilon1 * \<bar>f x - f y\<bar>/(epsilon2*\<Delta>) \<le> epsilon1 * \<Delta>/(epsilon2*\<Delta>)"
      using 1 2 divide_right_mono[of "epsilon1 * \<bar>f x - f y\<bar>" "epsilon1 * \<Delta>" "epsilon2*\<Delta>"]
      by linarith
  qed
  also have "... = exp(epsilon1/epsilon2)"
    using assms by simp
  finally have p:"spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z / spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z \<le> exp (epsilon1 /epsilon2)"
    by simp
  show "spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z \<le> exp (real epsilon1 / real epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z"
  proof -
    have "spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z = spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z * (spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z/ spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z)"
    proof -
      have "spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z / spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z = 1"
      using divide_self[of "spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z"] 
      apply(simp)
      using 3
      by auto
      then show ?thesis by auto
    qed
    also have "... = spmf (discrete_laplace_mechanism f \<Delta> x epsilon1 epsilon2) z / spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z * spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z"
      by simp      
    also have "... \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism f \<Delta> y epsilon1 epsilon2) z"
      apply(rewrite mult_right_mono)
      using p 
      by(simp_all)
    finally show ?thesis
      by simp
  qed
qed
      
subsection \<open>granularity:multiples of 2^k\<close>
(*
  Reference:
  https://github.com/opendp/opendp/blob/main/rust/src/measurements/laplace/float/mod.rs
*)

(*
  query returns floating-point value (that is rounded to the nearst multiples of 2^k)
  noise from discrete laplace on (2^k * \<int>)
*)



      

end