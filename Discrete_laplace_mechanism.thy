section \<open>Discrete Laplace Mechanism\<close>

theory Discrete_laplace_mechanism
  imports Discrete_laplace_rat
          IEEE_Floating_Point.Double
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
  f: query 
  \<Delta> is sensitivity of f 
  x: dataset
  epsilon = epsilon1/epsilon2 (1\<le>epsilon1,epsilon2)
  k: noise granularity in terms of 2^k
*)

lift_definition valof :: "double \<Rightarrow> real" is IEEE.valof.

definition x_div_2k :: "real \<Rightarrow> int \<Rightarrow> real" where
"x_div_2k x k = (if 0\<le>k then x/(2^(nat k)) else x * 2^(nat (-k)))"

definition findUpperBoundMultiple_2k :: "double \<Rightarrow> int \<Rightarrow> int" where
"findUpperBoundMultiple_2k d k = (if 0\<le>k then ceiling (x_div_2k (valof d) k)
                                  else ceiling (x_div_2k (valof d) k))"

definition findNearstMultiple_2k :: "double \<Rightarrow> int \<Rightarrow> int" where
"findNearstMultiple_2k d k = (let x = findUpperBoundMultiple_2k d k in 
                             (if ((x - (x_div_2k (valof d) k)) \<le> (x_div_2k (valof d) k)- (x-1)) then x else x-1)
)"


definition discrete_laplace_mechanism_Z2k_unit :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int spmf" where
"discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k = do {
  noise::int \<leftarrow> discrete_laplace_rat (epsilon2 * i) epsilon1;
  return_spmf (noise  + (findNearstMultiple_2k (f x) k))
}
"

definition power_2 :: "int \<Rightarrow> real" where
"power_2 k = (if 0\<le>k then 2^(nat k) else 1/(2^(nat (-k))))"

definition power_2_double :: "int \<Rightarrow> double" where 
"power_2_double k = (if 0\<le>k then double_of_int (2^(nat k)) else 1 / double_of_int(2^nat(-k)))"

definition x_mul_2k :: "int \<Rightarrow> int \<Rightarrow> double" where
"x_mul_2k x k = (if 0\<le>k then double_of_int (x * 2^(nat k)) else double_of_int (x) /double_of_int (2^(nat(-k))))"

definition discrete_laplace_mechanism_Z2k :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real spmf" where
"discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k = do {
  ans::int \<leftarrow> discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k;
  return_spmf (ans * power_2 k)
}
"

lemma findUpperBoundMultiple_2k_ub:
  shows "valof x \<le> power_2 k * findUpperBoundMultiple_2k x k"
proof (cases "0\<le>k")
  case True
  then show ?thesis
    unfolding findUpperBoundMultiple_2k_def x_div_2k_def power_2_def
    apply(simp)
  proof -
    have "0 < (2::nat) ^ nat k"
      by simp
    then show "valof x \<le> 2 ^ nat k * real_of_int \<lceil>valof x / 2 ^ nat k\<rceil>"
      using ceiling_divide_upper[of "2 ^ nat k" "valof x"]
      by (simp add: mult.commute)
  qed
next
  case False
  then show ?thesis 
    unfolding findUpperBoundMultiple_2k_def x_div_2k_def power_2_def
    apply(simp)
  proof -
    have 1:"valof x * 2 ^ nat (- k)\<le> real_of_int \<lceil>valof x * 2 ^ nat (- k)\<rceil>"
      by simp
    have 2:"0 < (2::nat) ^ nat (- k)"
      by simp
    have 3:"valof x * 2 ^ nat (- k) / 2 ^ nat (- k)\<le> real_of_int \<lceil>valof x * 2 ^ nat (- k)\<rceil> / 2 ^ nat (- k)"     
      using 1 2 divide_right_mono[of "valof x * 2 ^ nat (- k)" "real_of_int \<lceil>valof x * 2 ^ nat (- k)\<rceil>" "2 ^ nat (- k)"]
      by simp
    have 4:"valof x = valof x * 2 ^ nat (- k) / 2 ^ nat (- k)"
      by simp
    show "valof x \<le> real_of_int \<lceil>valof x * 2 ^ nat (- k)\<rceil> / 2 ^ nat (- k)"
      using 3 4
      by simp
  qed
qed

lemma findUpperBoundMultiple_2k_ub2:
  fixes z::int
  assumes "valof x \<le> power_2 k * z"
  shows "findUpperBoundMultiple_2k x k \<le> z"
proof (cases "0\<le>k")
  case True
  then show ?thesis
    unfolding findUpperBoundMultiple_2k_def
    using True apply(simp)
    unfolding x_div_2k_def
    using True apply(simp)
  proof -
    have 1:"valof x \<le> 2 ^ nat k * z"
      using assms True 
      unfolding power_2_def
      by simp
    have "valof x / 2^ nat k \<le> z"
    proof -
      have "0 < (2::nat)^nat k" 
        by simp
      then show ?thesis
        using 1 divide_right_mono[of"valof x" "2^nat k * z" "2^nat k"]
        by simp
    qed
    then show"\<lceil>valof x / 2 ^ nat k\<rceil>  \<le> z"
      by linarith
  qed
next
  case False
  then show ?thesis 
    unfolding findUpperBoundMultiple_2k_def
    using False apply(simp)
    unfolding x_div_2k_def
    using False apply(simp)
  proof -
    have 1:"valof x \<le> z / 2 ^ nat (- k)"
      using assms 
      unfolding power_2_def
      using False by(simp)
    have "valof x * 2^nat(-k) \<le> z"
    proof -
      have "0 < (2::nat)^nat (-k)"
        by simp
      then show ?thesis 
        using 1 mult_right_mono[of"valof x" "z/2^nat(-k)" "2^nat(-k)"]
        by simp
    qed
    then show "\<lceil>valof x * 2 ^ nat (- k)\<rceil> \<le> z"
      by linarith
  qed
qed

lemma findUpperBoundMultiple_2k_ub3:
  fixes z::int
  assumes "findUpperBoundMultiple_2k x k \<le> z"
  shows "valof x \<le> power_2 k * z"
proof -
  have "valof x \<le> power_2 k * real_of_int (findUpperBoundMultiple_2k x k)"
    using findUpperBoundMultiple_2k_ub[of "x" "k"]
    by simp
  also have "... \<le> power_2 k * z"
  proof -
    have "0 < power_2 k"
      unfolding power_2_def by simp
    then show ?thesis
      using assms by simp
  qed
  finally show ?thesis by simp
qed

lemma div_2k_power_2k:
  shows "x_div_2k (valof x) k * power_2 k = valof x"
  unfolding x_div_2k_def power_2_def
  by simp
  

lemma findNearstMultiple_2k:
  fixes z::int
  shows "\<bar>valof x - power_2 k * findNearstMultiple_2k x k\<bar> \<le> \<bar>valof x - power_2 k * z\<bar>"
proof(cases "0\<le>k")
  case True
  then show ?thesis
    unfolding findNearstMultiple_2k_def Let_def
  proof(auto)
    assume H:"2 * real_of_int (findUpperBoundMultiple_2k x k) \<le> 2 * x_div_2k (Discrete_laplace_mechanism.valof x) k + 1"
      and k:"0\<le>k"
    show "\<bar>valof x - power_2 k * real_of_int (findUpperBoundMultiple_2k x k)\<bar>
       \<le> \<bar>valof x - power_2 k * z\<bar>"
    proof(cases "findUpperBoundMultiple_2k x k \<le>z")
      case True
      then show ?thesis
      proof -
        have "valof x - power_2 k * real_of_int (findUpperBoundMultiple_2k x k) \<le> 0"
          using findUpperBoundMultiple_2k_ub
          by simp
        then have "\<bar>valof x - power_2 k * real_of_int (findUpperBoundMultiple_2k x k)\<bar> 
                 =  power_2 k * real_of_int (findUpperBoundMultiple_2k x k) - valof x"
          by simp
        also have "... \<le> power_2 k * z - valof x"
        proof(rule diff_right_mono[of "power_2 k * real_of_int (findUpperBoundMultiple_2k x k)"])
          have "0< power_2 k"
            unfolding power_2_def by simp
          then show "power_2 k * real_of_int (findUpperBoundMultiple_2k x k) \<le> power_2 k * z"
            using True by simp
        qed
        also have "... = \<bar>valof x - power_2 k * z\<bar>"
        proof -
          have "0\<le> power_2 k * z - valof x"
            using True findUpperBoundMultiple_2k_ub3
            by simp
          then show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed     
    next
      case False
      then show ?thesis 
      proof -
        have "0 \<le> power_2 k * (findUpperBoundMultiple_2k x k) - valof x"
          using findUpperBoundMultiple_2k_ub
          by simp
        then have 1:"\<bar>valof x - power_2 k * (findUpperBoundMultiple_2k x k)\<bar> = power_2 k * (findUpperBoundMultiple_2k x k) - valof x"
          by simp
        have "0 \<le> valof x - power_2 k * z"
          using False findUpperBoundMultiple_2k_ub2
          by force
        then have 2:"\<bar>valof x - power_2 k * z\<bar> = valof x - power_2 k * z"
          by simp
        have 3:"\<bar>valof x - power_2 k * z\<bar> -\<bar>valof x - power_2 k * (findUpperBoundMultiple_2k x k)\<bar> 
            = 2 * valof x - power_2 k * z - power_2 k * (findUpperBoundMultiple_2k x k)"
          using 1 2 by simp
        then have 4:"... = 2 * valof x - power_2 k * (z+ (findUpperBoundMultiple_2k x k))"
        proof -
          have "- power_2 k * z - power_2 k * (findUpperBoundMultiple_2k x k) = - (power_2 k * z + power_2 k * (findUpperBoundMultiple_2k x k))"
            by simp
          also have "... = - (power_2 k * (z+ (findUpperBoundMultiple_2k x k)))"
            using distrib_left[of "power_2 k" "z" "(findUpperBoundMultiple_2k x k)"]
            by simp
          finally show ?thesis
            by simp
        qed
        have 5:"2 * (findUpperBoundMultiple_2k x k) - 1 \<le> 2 * x_div_2k (valof x) k"
          using H by simp
        have 6:"(2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k \<le> 2 * valof x"
        proof -
          have "0< power_2 k"
            unfolding power_2_def by simp
          then show ?thesis
            using 5 div_2k_power_2k[of "x" "k"] mult_right_mono[of "2 * (findUpperBoundMultiple_2k x k) - 1" "2 * x_div_2k (valof x) k" "power_2 k"]
            by argo
        qed
        have 7:"power_2 k * (z+ (findUpperBoundMultiple_2k x k)) \<le> (2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k"
        proof -
          have "z \<le> findUpperBoundMultiple_2k x k - 1"
            using False by simp
          then have 1:"z+ (findUpperBoundMultiple_2k x k) \<le> 2 * (findUpperBoundMultiple_2k x k) - 1"
            by simp
          have "0 < power_2 k"
            unfolding power_2_def by simp
          then show ?thesis
            using 1 by simp
        qed
        have "0 \<le> 2 * valof x - power_2 k * (z+ (findUpperBoundMultiple_2k x k))"
          using 6 7 by simp
        then show "\<bar>valof x - power_2 k * (findUpperBoundMultiple_2k x k)\<bar> \<le> \<bar>valof x - power_2 k * z\<bar>"
          using 3 4 by simp
      qed
    qed
  next
    assume H:"\<not> 2 * real_of_int (findUpperBoundMultiple_2k x k) \<le> 2 * x_div_2k (valof x) k + 1"
      and k: "0\<le>k" 
    show "\<bar>valof x - power_2 k * (real_of_int (findUpperBoundMultiple_2k x k) - 1)\<bar>
       \<le> \<bar>valof x - power_2 k * real_of_int z\<bar> "
    proof (cases "findUpperBoundMultiple_2k x k \<le>z")
      case True
      then show ?thesis  
      proof -
        have 1:"\<bar>valof x - power_2 k * ((findUpperBoundMultiple_2k x k) - 1)\<bar> = valof x - power_2 k * ((findUpperBoundMultiple_2k x k) - 1)"
        proof -
          have "power_2 k * ((findUpperBoundMultiple_2k x k) - 1) \<le> valof x"
          proof -
            have "\<not> findUpperBoundMultiple_2k x k \<le> findUpperBoundMultiple_2k x k - 1"
              by simp
            then have "\<not> valof x \<le> power_2 k * ((findUpperBoundMultiple_2k x k) - 1)"
              using findUpperBoundMultiple_2k_ub2
              by blast
            then show ?thesis by simp
          qed 
          then show ?thesis by simp
        qed
        have 2:"\<bar>valof x - power_2 k * z\<bar> = power_2 k * z - valof x"
          using True findUpperBoundMultiple_2k_ub3
          by simp
        have 3:"\<bar>valof x - power_2 k * z\<bar> - \<bar>valof x - power_2 k * ((findUpperBoundMultiple_2k x k) - 1)\<bar> 
            = power_2 k * z + power_2 k * ((findUpperBoundMultiple_2k x k) - 1) - 2* valof x"
          using 1 2 by simp
        have "0 \<le> power_2 k * z + power_2 k * ((findUpperBoundMultiple_2k x k) - 1) - 2* valof x"
          sorry
        then show ?thesis using 3 by auto
      qed              
    next
      case False
      then show ?thesis sorry
    qed
  qed
next
  case False
  then show ?thesis sorry
qed

lemma power_2_gt_zero:
"0<power_2 k"
  unfolding power_2_def
  by simp


lemma spmf_discrete_laplace_mechanism_Z2k_unit:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
  shows "spmf (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k) z 
       = (exp(epsilon1/(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
proof - 
  have "spmf (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k) z  = spmf (discrete_laplace_rat (epsilon2 * i) epsilon1 \<bind> (\<lambda>noise. return_spmf (noise + findNearstMultiple_2k (f x) k))) z "
    unfolding discrete_laplace_mechanism_Z2k_unit_def by simp
  also have "... = spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k) z = spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z"
    by simp
  have "(\<lambda>noise. noise + findNearstMultiple_2k (f x) k) -` {z} = {z - findNearstMultiple_2k (f x) k}"
    by auto
  then have 2:"spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z = spmf (discrete_laplace_rat (epsilon2 * i) epsilon1) (z-findNearstMultiple_2k (f x) k)"  
    apply(simp add: spmf_map)
    by(simp add: spmf_conv_measure_spmf)    
  have 3:"... = (exp (epsilon1 /(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-findNearstMultiple_2k (f x) k\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
    using assms spmf_discrete_laplace_rat    
    by simp
  show ?thesis
    using 1 2 3 by simp
qed

lemma spmf_discrete_laplace_mechanism_Z2k_in_Z2k:
  fixes z::real and n::int
  assumes scale1:"1\<le>epsilon1" and scale2:"1\<le>epsilon2"
and seinsitivity:"1\<le>i" and delta:"\<Delta> = power_2 k * i"
and z:"z = power_2 k * n"
shows "spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z 
      = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
proof -
  have "spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z = spmf (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k \<bind> (\<lambda>x. return_spmf (real_of_int x * power_2 k))) z"
    unfolding discrete_laplace_mechanism_Z2k_def by simp
  also have "... = spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k )) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z = spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k)) z"
    by simp
  term "(\<lambda>x. real_of_int x * power_2 k) -` {z}"
  have "(\<lambda>x. real_of_int x * power_2 k) -` {z} = {n}"
    unfolding vimage_def
    apply(rewrite z)
    unfolding power_2_def 
    by simp
  then have "spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k)) z = spmf (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k) n"
    apply(rewrite spmf_map)
    by(simp add: spmf_conv_measure_spmf)
  also have "... = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>n - findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * i)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
    apply(rewrite spmf_discrete_laplace_mechanism_Z2k_unit)
    using assms by(simp_all)
  also have "... = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
  proof -
    have "(epsilon1 * \<bar>n - findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * i) = (epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)"
    proof -
      have "(epsilon1 * \<bar>n - findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * i) = (power_2 k * epsilon1 * \<bar>n - findNearstMultiple_2k (f x) k\<bar>) / (power_2 k * epsilon2 * i)"
        using mult_divide_mult_cancel_left[of "power_2 k"] assms
        unfolding power_2_def
        by(simp)
      also have "... = (epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)"
      proof -
        have 1:"power_2 k * epsilon1 * \<bar>n - findNearstMultiple_2k (f x) k\<bar> = epsilon1 * \<bar>z - power_2 k * (findNearstMultiple_2k (f x) k)\<bar>"
          apply(rewrite mult.commute[of "power_2 k" "epsilon1"])
          using scale1
          apply(simp)
          apply(rewrite abs_mult_pos'[of "power_2 k" "real_of_int n - findNearstMultiple_2k (f x) k"])
          using power_2_gt_zero[of "k"]
          apply(simp)
          using right_diff_distrib[of "power_2 k" "n" "findNearstMultiple_2k (f x) k"] z
          by(auto)
        have 2:"power_2 k * epsilon2 * i = epsilon2 * \<Delta>"
          using delta by(simp)
        show ?thesis
          using 1 2 by presburger
      qed
      finally show ?thesis by simp
    qed
    then show ?thesis
      by auto
  qed
  finally have 2:"spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i x epsilon1 epsilon2 k)) z =
  (exp (epsilon1 /(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>z - power_2 k * real_of_int (findNearstMultiple_2k (f x) k)\<bar> / (epsilon2 * \<Delta>))) /
  (exp (epsilon1 /(epsilon2 * i)) + 1)"
    by simp
  show ?thesis
    using 1 2 by simp
qed
    

lemma spmf_discrete_laplace_mechanism_Z2k_out_Z2k:
  assumes scale:"1\<le>epsilon1" and "1\<le>epsilon2"
and seinsitivity:"1\<le>i"
and z:"z\<notin>{d. \<exists>n::int. d = power_2 k * n}"
shows "spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z = 0"
  sorry

lemma pure_dp_discrete_laplace_mechanism_Z2k:
  fixes f::"'a list \<Rightarrow> double"
and i::nat
and x:: "'a list"
and epsilon1 epsilon2::nat
and k:: int
  assumes sensitivity:"\<bar>findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f y) k\<bar>\<le> i"
and scale1:"1\<le> epsilon1" and scale2:"1\<le> epsilon2"
and i:"1\<le>i" and delta: "\<Delta> = power_2 k * i"
shows "\<And>z. spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"
proof -
  fix z:: real
  show "spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"
  proof(cases "z\<in>{d. \<exists>n::int. d = power_2 k * n}")
    case True
    then show ?thesis
    proof -
      have z:"z = power_2 k * real_of_int (THE n. z=power_2 k * n)"
        using True power_2_gt_zero[of "k"]
        by(auto)
      have 1:"spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
        apply(rewrite spmf_discrete_laplace_mechanism_Z2k_in_Z2k[of"epsilon1" "epsilon2" "i" "\<Delta>" "k" "z" "(THE n. z=power_2 k * n)"])
        using assms z by(simp_all)
      have 2:"spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>) / (epsilon2 * \<Delta>)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
        apply(rewrite spmf_discrete_laplace_mechanism_Z2k_in_Z2k[of"epsilon1" "epsilon2" "i" "\<Delta>" "k" "z" "(THE n. z=power_2 k * n)"])
        using assms z by(simp_all)
      have 3:"spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z/ spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z 
            = exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)))/exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>) / (epsilon2 * \<Delta>)))"
        apply(rewrite 1)
        apply(rewrite 2)
        apply(auto)
        using assms apply(simp_all)
      proof -
        have "exp (real epsilon1 / (real epsilon2 * real i)) + 1 > 0"
          using exp_gt_zero add_pos_pos zero_less_one
          by blast
        then show "exp (real epsilon1 / (real epsilon2 * real i)) + 1 = 0 \<Longrightarrow> False"
          by simp
      qed
      also have "... =  exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>))- (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>) / (epsilon2 * \<Delta>))))"
        using exp_diff[of"- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>))" "- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>) / (epsilon2 * \<Delta>))"]
        by simp
      also have "... = exp ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>- epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>))"
        using diff_divide_distrib[of "- (epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>)" "-(epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar>)" "(epsilon2*\<Delta>)"]
        by simp
      also have "... = exp(epsilon1 * (\<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar> - \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>)/(epsilon2*\<Delta>))"
        by argo
      also have "... \<le> exp((epsilon1 * \<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar>)/(epsilon2*\<Delta>))"
      proof 
        have "\<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar> - \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar> \<le> \<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar>"
          by simp
        then have 1:"epsilon1 * (\<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar> - \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) \<le> epsilon1 * \<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar>"
          using scale1 by simp
        have 2:"0\<le> epsilon2 * \<Delta>"
          using scale2 delta sensitivity power_2_gt_zero[of"k"] by simp
        show "real epsilon1 * (\<bar>z - power_2 k * real_of_int (findNearstMultiple_2k (f y) k)\<bar> - \<bar>z - power_2 k * real_of_int (findNearstMultiple_2k (f x) k)\<bar>) / (real epsilon2 * \<Delta>)
    \<le> real epsilon1 * \<bar>power_2 k * real_of_int (findNearstMultiple_2k (f x) k) - power_2 k * real_of_int (findNearstMultiple_2k (f y) k)\<bar> / (real epsilon2 * \<Delta>)"
          using 1 2 divide_right_mono[of "epsilon1 * (\<bar>z - power_2 k * findNearstMultiple_2k (f y) k\<bar> - \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>)" "epsilon1 * \<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar>" "(epsilon2*\<Delta>)"]
          by linarith
      qed
      also have "... \<le> exp((epsilon1*\<Delta>)/(epsilon2*\<Delta>))"
      proof 
        have 1:"epsilon1 * \<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar> \<le> epsilon1*\<Delta>"
        proof -
          have "\<bar>power_2 k * findNearstMultiple_2k (f x) k - power_2 k * findNearstMultiple_2k (f y) k\<bar> = \<bar>power_2 k * (findNearstMultiple_2k (f x) k- findNearstMultiple_2k (f y) k)\<bar>"
            using right_diff_distrib[of "power_2 k" "(findNearstMultiple_2k (f x) k)" "(findNearstMultiple_2k (f y) k)"]
            by simp
          also have "... = power_2 k * \<bar>findNearstMultiple_2k (f x) k- findNearstMultiple_2k (f y) k\<bar>"
            using abs_mult_pos'[of "power_2 k" "findNearstMultiple_2k (f x) k- findNearstMultiple_2k (f y) k"] power_2_gt_zero[of "k"]
            by simp
          also have "... \<le> \<Delta>"
            using sensitivity delta power_2_gt_zero[of"k"]
            by(simp)
          finally have "\<bar>power_2 k * real_of_int (findNearstMultiple_2k (f x) k) - power_2 k * real_of_int (findNearstMultiple_2k (f y) k)\<bar> \<le> \<Delta> " by simp
          then show ?thesis 
            using scale1 by simp
        qed
        have 2:"0 \<le> epsilon2*\<Delta>"
          using assms power_2_gt_zero[of"k"] by simp     
        show "real epsilon1 * \<bar>power_2 k * real_of_int (findNearstMultiple_2k (f x) k) - power_2 k * real_of_int (findNearstMultiple_2k (f y) k)\<bar> / (real epsilon2 * \<Delta>)
    \<le> real epsilon1 * \<Delta> / (real epsilon2 * \<Delta>)"
          using 1 2 divide_right_mono by blast
      qed
      also have "... = exp(epsilon1/epsilon2)"
        using assms power_2_gt_zero[of"k"] by simp 
      finally have p:"spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z/ spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z \<le> exp (epsilon1/epsilon2)"
        by simp
      show ?thesis
      proof -
        have "spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z = spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z * spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z/ spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"
        proof -
          have "spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z/spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z = 1"
            using divide_self[of"spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"]
            apply(simp)
            using 3 by auto
          then show ?thesis by auto
        qed
        also have "... = spmf (discrete_laplace_mechanism_Z2k f i x epsilon1 epsilon2 k) z/spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z * spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"
          by simp
        also have "... \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k f i y epsilon1 epsilon2 k) z"
          apply(rewrite mult_right_mono)
          using p by (simp_all)
        finally show ?thesis by simp
      qed
    qed
  next
    case False
    then show ?thesis 
    apply(rewrite spmf_discrete_laplace_mechanism_Z2k_out_Z2k)
      using assms False by(simp_all)
  qed
qed


end