section \<open>Discrete Laplace Mechanism\<close>

theory Discrete_laplace_mechanism_Z2k
  imports "sampler/Discrete_laplace_rat"
          Differential_Privacy
          IEEE_Floating_Point.Double
begin 

subsection \<open>granularity:multiples of 2^k\<close>
(*work in progress*)
(*
  Reference:
  https://github.com/opendp/opendp/blob/main/rust/src/measurements/laplace/float/mod.rs
*)

(*
  query returns floating-point value (that is rounded to the nearst multiples of 2^k)
  noise from discrete laplace on (2^k * \<int>)
  f: query 
  i: 2^k*i is sensitivity of f 
  x: dataset
  epsilon = epsilon1/epsilon2 (1\<le>epsilon1,epsilon2)
  k: noise granularity in terms of 2^k
*)

subsubsection \<open>definition\<close>

text \<open>Converts a double-precision floating-point number to a real number\<close>
lift_definition valof :: "double \<Rightarrow> real" is IEEE.valof.

text \<open>Calculate x/2^k\<close>
definition x_div_2k :: "real \<Rightarrow> int \<Rightarrow> real" where
"x_div_2k x k = (if 0\<le>k then x/(2^(nat k)) else x * 2^(nat (-k)))"

text \<open>Calculate the min of {z |d\<le>z * 2^k}\<close>
definition findUpperBoundMultiple_2k :: "double \<Rightarrow> int \<Rightarrow> int" where
"findUpperBoundMultiple_2k d k = (if 0\<le>k then ceiling (x_div_2k (valof d) k)
                                  else ceiling (x_div_2k (valof d) k))"

text \<open>Calculate the argmin_z|d - z^*2k|\<close>
definition findNearstMultiple_2k :: "double \<Rightarrow> int \<Rightarrow> int" where
"findNearstMultiple_2k d k = (let x = findUpperBoundMultiple_2k d k in 
                             (if ((x - (x_div_2k (valof d) k)) \<le> (x_div_2k (valof d) k)- (x-1)) then x else x-1)
)"


definition discrete_laplace_mechanism_Z2k_unit :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> int spmf" where
"discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x = do {
  noise::int \<leftarrow> discrete_laplace_rat (epsilon2 * i) epsilon1;
  return_spmf (noise  + (findNearstMultiple_2k (f x) k))
}
"

text\<open>Calculate 2^k\<close>
definition power_2 :: "int \<Rightarrow> real" where
"power_2 k = (if 0\<le>k then 2^(nat k) else 1/(2^(nat (-k))))"

definition discrete_laplace_mechanism_Z2k :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> real spmf" where
"discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x = do {
  postprocess (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k) (\<lambda>ans. ans * power_2 k) x
}
"

definition discrete_laplace_mechanism_Z2k' :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> real spmf" where
"discrete_laplace_mechanism_Z2k' f i epsilon1 epsilon2 k x = do {
  ans::int \<leftarrow> discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x;
  return_spmf (ans * power_2 k)
}
"

lift_definition double_of_real::"real \<Rightarrow> double" is "\<lambda>x. round RNE x" .

definition round_to_double :: "real \<Rightarrow> double" where
"round_to_double x = double_of_real x"

definition discrete_laplace_mechanism_Z2k_to_double :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> double spmf" where
"discrete_laplace_mechanism_Z2k_to_double f i epsilon1 epsilon2 k x = do {
  postprocess (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k) round_to_double x
}
"

definition mul_2k_to_double :: "int \<Rightarrow> int \<Rightarrow> double" where
"mul_2k_to_double man expo = 
  (let d = double_of_man_exp (integer_of_int man) (integer_of_int expo)
   in (if d=None then 0 else the d))"

definition discrete_laplace_mechanism_Z2k_to_double2 :: "('a list \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> double spmf" where
"discrete_laplace_mechanism_Z2k_to_double2 f i epsilon1 epsilon2 k x = do {
  ans::int \<leftarrow> discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x;
  return_spmf (mul_2k_to_double ans k)
}
"

subsubsection \<open>sensitivity for Z2k\<close>

definition is_sensitivity_Z2k :: "('a, double) query \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
"is_sensitivity_Z2k q i k 
= (\<forall>(l1, l2)\<in>adj. \<bar>findNearstMultiple_2k (q l1) k - findNearstMultiple_2k (q l2) k\<bar> \<le> i)"

lemma sensitivity_Z2k:
  assumes "is_sensitivity_Z2k q i k"
and "(l1, l2)\<in>adj"
shows "\<bar>findNearstMultiple_2k (q l1) k - findNearstMultiple_2k (q l2) k\<bar> \<le> i"
  using assms
  unfolding is_sensitivity_Z2k_def
  by auto

subsubsection \<open>Properties of Component Functions\<close>

text \<open>power_2\<close>

lemma power_2_pos:
  assumes "0\<le>k"
  shows "power_2 k = 2^(nat k)"
  unfolding power_2_def by(rule if_P,simp add: assms)

lemma power_2_neg:
  assumes "k<0"
  shows "power_2 k = 1/2^(nat (-k))"
  unfolding power_2_def 
  apply(rule if_not_P)
  using assms by(simp)

lemma power_2_gt_zero:
"0<power_2 k"
  unfolding power_2_def
  by simp

text \<open>findUpperBoundMultipl2_2k\<close>

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

text \<open>x_div_2k\<close>

lemma div_2k_power_2k:
  shows "x_div_2k (valof x) k * power_2 k = valof x"
  unfolding x_div_2k_def power_2_def
  by simp

text \<open>findNearstMultiple_2k\<close>

lemma findNearstMultiple_2k:
  fixes z::int
  shows "\<bar>valof x - power_2 k * findNearstMultiple_2k x k\<bar> \<le> \<bar>valof x - power_2 k * z\<bar>"
  unfolding findNearstMultiple_2k_def Let_def
proof(auto)
  assume H:"2 * real_of_int (findUpperBoundMultiple_2k x k) \<le> 2 * x_div_2k (valof x) k + 1"
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
      proof -
        have p:"power_2 k * findUpperBoundMultiple_2k x k \<le> power_2 k * z"
          using True power_2_gt_zero[of k] by simp
        have p1:"2 * x_div_2k (valof x) k < 2 * (findUpperBoundMultiple_2k x k) - 1"
          using H by simp
        have "2 * valof x < (2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k"
        proof -
          have 1:"2 * x_div_2k (valof x) k * power_2 k = 2 * valof x"
            using div_2k_power_2k[of "x" "k"] by simp
          have 2:"2 * x_div_2k (valof x) k * power_2 k < (2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k"
            using p1 power_2_gt_zero[of k] mult_right_mono[of "2 * x_div_2k (valof x) k " "2 * (findUpperBoundMultiple_2k x k) - 1" "power_2 k"]
            by simp
          show ?thesis
            using 1 2 by simp
        qed
        then have "0 < (2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k - 2* valof x"
          by(simp)
        also have "... \<le> power_2 k * z + power_2 k * ((findUpperBoundMultiple_2k x k) - 1) - 2* valof x "
        proof -
          have "2 * (findUpperBoundMultiple_2k x k) - 1 = findUpperBoundMultiple_2k x k + (findUpperBoundMultiple_2k x k - 1)"
            by simp
          then have "(2 * (findUpperBoundMultiple_2k x k) - 1) * power_2 k = power_2 k * (findUpperBoundMultiple_2k x k) + power_2 k * ((findUpperBoundMultiple_2k x k) - 1)"
            apply(rewrite mult.commute)
            using distrib_left[of "power_2 k" "findUpperBoundMultiple_2k x k" "findUpperBoundMultiple_2k x k-1"]
            by simp
          then show ?thesis
            using p by simp
        qed
        finally show ?thesis by simp
      qed
      then show ?thesis using 3 by auto
    qed
  next
    case False
    then show ?thesis
    proof -
      have 1:"\<bar>valof x - power_2 k * (findUpperBoundMultiple_2k x k - 1)\<bar> = valof x - power_2 k * (findUpperBoundMultiple_2k x k - 1)"
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
      have 2:"\<bar>valof x - power_2 k * z\<bar> = valof x - power_2 k * z"
        using False findUpperBoundMultiple_2k_ub2
        by force
      have 3:"\<bar>valof x - power_2 k * z\<bar> - \<bar>valof x - power_2 k * (findUpperBoundMultiple_2k x k - 1)\<bar>
             = power_2 k * (findUpperBoundMultiple_2k x k - 1) - power_2 k * z"
        using 1 2 by simp
      have "0 \<le> power_2 k * (findUpperBoundMultiple_2k x k - 1) - power_2 k * z"
        using False power_2_gt_zero[of k] by simp
      then show ?thesis
        using 3 by simp
    qed
  qed
qed




subsubsection \<open>pure-dp of discrete_laplace_mechanism_Z2k\<close>

lemma lossless_discrete_laplace_mechanism_Z2k_unit:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
shows "lossless_spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x)"
  unfolding discrete_laplace_mechanism_Z2k_unit_def
  using lossless_discrete_laplace_rat assms
  by simp

lemma lossless_discrete_laplace_mechanism_Z2k:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
shows "lossless_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x)"
  unfolding discrete_laplace_mechanism_Z2k_def postprocess_def
  using lossless_discrete_laplace_mechanism_Z2k_unit assms
  by fastforce

lemma spmf_discrete_laplace_mechanism_Z2k_unit:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
  shows "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z 
       = (exp(epsilon1/(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
proof - 
  have "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z  
      = spmf (discrete_laplace_rat (epsilon2 * i) epsilon1 \<bind> (\<lambda>noise. return_spmf (noise + findNearstMultiple_2k (f x) k))) z "
    unfolding discrete_laplace_mechanism_Z2k_unit_def by simp
  also have "... = spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z 
                = spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z"
    by simp
  have "(\<lambda>noise. noise + findNearstMultiple_2k (f x) k) -` {z} = {z - findNearstMultiple_2k (f x) k}"
    by auto
  then have 2:"spmf (map_spmf (\<lambda>noise. noise + findNearstMultiple_2k (f x) k) (discrete_laplace_rat (epsilon2 * i) epsilon1)) z 
             = spmf (discrete_laplace_rat (epsilon2 * i) epsilon1) (z-findNearstMultiple_2k (f x) k)" 
    apply(simp add: spmf_map)
    by(simp add: spmf_conv_measure_spmf)    
  have 3:"... = (exp (epsilon1 /(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-findNearstMultiple_2k (f x) k\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
    using assms spmf_discrete_laplace_rat    
    by simp
  show ?thesis
    using 1 2 3 by simp
qed

lemma pointwise_pure_dp_inequality_discrete_laplace_mechanism_Z2k_unit:
  assumes "is_sensitivity_Z2k f i k"
and "(x, y)\<in>adj"
and "1\<le>epsilon1"
and "1\<le>epsilon2"
and "1\<le>i"
shows "\<And>z. spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z \<le> exp(epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z "
proof -
  fix z::int
  have 1:"spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z = (exp(epsilon1/(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
    using spmf_discrete_laplace_mechanism_Z2k_unit[of "epsilon1" "epsilon2" "i" "f" "k" "x"] assms
    by simp
  have 2:"spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z = (exp(epsilon1/(epsilon2*i))-1) * exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>/(epsilon2*i)))/(exp (epsilon1/(epsilon2*i))+1)"
    using spmf_discrete_laplace_mechanism_Z2k_unit[of "epsilon1" "epsilon2" "i" "f" "k" "y"] assms
    by simp
  have 3:"spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z/spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z
        = exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i)))/exp (-(epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>/(epsilon2*i)))"
    using assms
  proof(rewrite 1, rewrite 2,auto)
    have "exp (real epsilon1 / (real epsilon2 * real i)) + 1 > 1"
      using exp_gt_zero[of "epsilon1/(epsilon2 * i)"]
      by simp
    then show "exp (real epsilon1 / (real epsilon2 * real i)) + 1 = 0 \<Longrightarrow> False"
      by simp
  qed
  also have "... = exp(-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i))-(-(epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>/(epsilon2*i))))"
    using exp_diff[of"-(epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>/(epsilon2*i))" "-(epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>/(epsilon2*i))"]
    by argo
  also have "... = exp ((epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>-epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>)/(epsilon2*i))"
    using diff_divide_distrib[of "-epsilon1*\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>" "-epsilon1*\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>" "(epsilon2*i)"]
    by simp
  also have "... = exp ((epsilon1*(\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>-\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>))/(epsilon2*i))"
    using int_distrib(4) by presburger
  also have "... \<le> exp((epsilon1*\<bar>(findNearstMultiple_2k (f x) k) - (findNearstMultiple_2k (f y) k)\<bar>)/(epsilon2*i))"
  proof 
    have "\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>-\<bar>z-(findNearstMultiple_2k (f x) k)\<bar> \<le> \<bar>(findNearstMultiple_2k (f x) k) - (findNearstMultiple_2k (f y) k)\<bar>"
      by simp
    then have 1:"epsilon1 * (\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>-\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>) \<le> epsilon1 * \<bar>(findNearstMultiple_2k (f x) k) - (findNearstMultiple_2k (f y) k)\<bar>"
      using assms by simp
    have 2:"0\<le> epsilon2 * i"
      using assms by simp
    show "(epsilon1 * (\<bar>z - findNearstMultiple_2k (f y) k\<bar> - \<bar>z - findNearstMultiple_2k (f x) k\<bar>))/(epsilon2 * i)
       \<le> (epsilon1 * \<bar>findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f y) k\<bar>)/(epsilon2 * i)"
      using 1 2 divide_right_mono[of "epsilon1*(\<bar>z-(findNearstMultiple_2k (f y) k)\<bar>-\<bar>z-(findNearstMultiple_2k (f x) k)\<bar>)" "epsilon1*\<bar>(findNearstMultiple_2k (f x) k) - (findNearstMultiple_2k (f y) k)\<bar>" "(epsilon2*i)"]
      by linarith
  qed
  also have "... \<le> exp((epsilon1*i)/(epsilon2*i))"
  proof
    have 1:"epsilon1 * \<bar>findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f y) k\<bar> \<le> epsilon1 * i"
      using assms sensitivity_Z2k[of "f" "i" "k" "x" "y"] by simp
    have 2:"0 \<le> epsilon2 * i"
      using assms by simp
    show "epsilon1 * \<bar>findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f y) k\<bar>/(epsilon2 * i) \<le> (epsilon1 * i)/(epsilon2 * i)"
      using 1 2 divide_right_mono[of "epsilon1 * \<bar>findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f y) k\<bar>" "epsilon1 * i" "epsilon2*i"]
      by linarith
  qed
  also have "... = exp(epsilon1/epsilon2)"
    using assms by simp
  finally have p:"spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z / spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z \<le> exp (epsilon1/epsilon2)"
    by simp
  show "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z"
  proof -
    have "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z  = spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z * spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z/spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z"
    proof -
      have "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z/spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z = 1"
        using divide_self[of "spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z "] 3
        by(auto)
      then show ?thesis by auto
    qed
    also have "... = spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) z/spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z * spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z"
      by simp
    also have "... \<le> exp (epsilon1/epsilon2) * spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k y) z "
      apply(rewrite mult_right_mono)
      using p by simp_all
    finally show ?thesis by simp
  qed
qed

lemma pure_dp_discrete_laplace_mechanism_Z2k_unit:
  assumes "is_sensitivity_Z2k f i k"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
shows "pure_dp (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k) (epsilon1/epsilon2)"
  using pointwise_spmf_bound_imp_pure_dp 
        pointwise_pure_dp_inequality_discrete_laplace_mechanism_Z2k_unit assms
  by blast

lemma pure_dp_discrete_laplace_mechanism_Z2k:
  assumes "is_sensitivity_Z2k f i k"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
shows "pure_dp (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k) (epsilon1/epsilon2)"
  unfolding discrete_laplace_mechanism_Z2k_def 
  using pure_dp_discrete_laplace_mechanism_Z2k_unit dp_postprocess_theorem assms
  by blast

lemma pure_dp_discrete_laplace_mechanism_Z2k_to_double:
  assumes "is_sensitivity_Z2k f i k"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "1\<le>i"
shows "pure_dp (discrete_laplace_mechanism_Z2k_to_double f i epsilon1 epsilon2 k) (epsilon1/epsilon2)"
  unfolding discrete_laplace_mechanism_Z2k_to_double_def 
  using pure_dp_discrete_laplace_mechanism_Z2k dp_postprocess_theorem assms
  by blast

lemma spmf_discrete_laplace_mechanism_Z2k_in_Z2k:
  fixes z::real and n::int
  assumes scale1:"1\<le>epsilon1" and scale2:"1\<le>epsilon2"
and seinsitivity:"1\<le>i" and delta:"\<Delta> = power_2 k * i"
and z:"z = power_2 k * n"
shows "spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z 
      = (exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * \<Delta>)))/(exp (epsilon1 / (epsilon2 * i)) + 1)"
proof -
  have "spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z = spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x \<bind> (\<lambda>x. return_spmf (real_of_int x * power_2 k))) z"
    unfolding discrete_laplace_mechanism_Z2k_def postprocess_def by simp
  also have "... = spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x)) z"
    by(simp add: map_spmf_conv_bind_spmf)
  finally have 1:"spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z = spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x)) z"
    by simp
  term "(\<lambda>x. real_of_int x * power_2 k) -` {z}"
  have "(\<lambda>x. real_of_int x * power_2 k) -` {z} = {n}"
    unfolding vimage_def
    apply(rewrite z)
    unfolding power_2_def 
    by simp
  then have "spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x)) z = spmf (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x) n"
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
  finally have 2:"spmf (map_spmf (\<lambda>x. real_of_int x * power_2 k) (discrete_laplace_mechanism_Z2k_unit f i epsilon1 epsilon2 k x)) z =
  (exp (epsilon1 /(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>z - power_2 k * real_of_int (findNearstMultiple_2k (f x) k)\<bar> / (epsilon2 * \<Delta>))) /
  (exp (epsilon1 /(epsilon2 * i)) + 1)"
    by simp
  show ?thesis
    using 1 2 by simp
qed

lemma plus_measure_spmf:
  assumes "A \<union> B = C" and "A \<inter> B = empty"
shows "(Sigma_Algebra.measure (measure_spmf p) C) = (Sigma_Algebra.measure (measure_spmf p) A) + (Sigma_Algebra.measure (measure_spmf p) B)"
  unfolding measure_def 
proof -
  have A:"A \<in> sets (measure_spmf p)"
    by simp
  have B:"B \<in> sets (measure_spmf p)"
    by simp
  have p1:"emeasure (measure_spmf p) A + emeasure (measure_spmf p) B = emeasure (measure_spmf p) C"
    using A B assms plus_emeasure by blast
  have p2:"emeasure (measure_spmf p) A  < \<top>"
    by (simp add: ennreal_less_top_iff)
  have p3:"emeasure (measure_spmf p) B  < \<top>"
    by (simp add: ennreal_less_top_iff)
  show "enn2real (emeasure (measure_spmf p) C) = enn2real (emeasure (measure_spmf p) A) + enn2real (emeasure (measure_spmf p) B)"
    using p1 p2 p3 enn2real_plus by metis
qed

lemma summable_exp_minu_rat:
  fixes t:: "real"
  assumes "0<t"
  shows "summable (\<lambda>x. exp (- (real x /t)))"
proof -
  have 1:"(\<lambda>x::nat. exp (- (real x / t))) = (\<lambda>x::nat. (exp (- (1/ t))) ^ x)"
  proof 
    fix x ::nat
    have "exp (-real x/t) = exp (x * (-1/t))"
      by simp
    also have "... = exp(-1/t)^x"
      by (rule exp_of_nat_mult)
    finally show "exp (- (real x / t)) = exp (- (1 /  t)) ^ x" 
      by simp
  qed
  have "summable (\<lambda>x::nat. (exp (- (1/ t))) ^ x)"
    apply(rewrite summable_geometric)
    using assms by(simp_all)
  then show "summable (\<lambda>x. exp (- (real x / t)))"
    using assms 1 by simp
qed

lemma exp_sum2:
  fixes n::nat and t::real
  assumes "0<t"
  shows "(\<Sum>x = 0..<n. exp (- x/t)) = (1-exp(-n/t))/(1-exp(-1/t))"
proof -
  have "(\<Sum>x = 0..<n. exp (- x/t)) * exp(-1/t) = (\<Sum>x = 1..<n+1. exp (- x/t))"
  proof(rewrite sum_distrib_right, simp add:Fract_of_int_quotient of_rat_divide)
    have "\<And>n::nat. exp (- (real n / t)) * exp (- (1 / t)) = exp(-((n+1)/t))"
      apply(simp add: mult_exp_exp)
      by argo
    then have "(\<Sum>n = 0..<n. exp (- (real n / t)) * exp (- (1 / t))) = (\<Sum>n = 0..<n. exp (- ((n+1)/t)))"
      by simp
    also have "... = (\<Sum>n = 1..<Suc n. exp (- (n/t)))"
    proof -
      have "((\<lambda>n::nat. exp (- (n / t)) ) \<circ> Suc) = (\<lambda>n::nat. exp (- (real(n + 1) / t)))"
        by(simp add: o_def)
      then have "(\<Sum>n = 0..<n. exp (- (real (n + 1) / t)))  = sum ((\<lambda>n. exp (- (real n / t)))  \<circ> Suc) {0..<n}"
        by simp
      also have "... = (\<Sum>n = Suc 0..<Suc n. exp (- (n/t)))"
        using sum.atLeast_Suc_lessThan_Suc_shift[of "(\<lambda>n. exp(-n/t))" "0" "n"]
        by auto
      also have "... = (\<Sum>n = 1..<Suc n. exp (- (n/t)))" 
        by auto
      finally show ?thesis
        by simp
    qed
    finally have "(\<Sum>n = 0..<n. exp (- (real n /t)) * exp (- (1 /t))) = (\<Sum>x = Suc 0..<Suc n. exp (- (real x /t)))"
      by simp
    then show " 0 < n \<longrightarrow>(\<Sum>n = 0..<n. exp (- (real n / t)) * exp (- (1 / t))) = (\<Sum>x = Suc 0..<n. exp (- (real x / t))) + exp (- (real n / t))"
      by simp
  qed
  then have "(\<Sum>x = 0..<n. exp (- x/t)) * (1 -exp(-1/t)) = (\<Sum>x = 0..<n. exp (- x/t)) - (\<Sum>x = 1..<n+1. exp (- x/t))"
    by(rewrite right_diff_distrib, simp)    
  also have "... = 1 - exp(-n/t)"
  proof -
    have 1:"(\<Sum>x = 0..<n. exp (- x/t))  = (\<Sum>x = 0..<n+1. exp (- x/t)) - exp(-n/t)"
    proof -
      have "{0..<n+1} = {0..<n} \<union> {n}"
        by auto
      then have p:"(\<Sum>x = 0..<n+1. exp (- x/t)) = (\<Sum>x = 0..<n. exp (- x/t)) + (\<Sum>x \<in>{n}. exp (- x/t))"
        by simp
      show ?thesis
      proof -
        have "(\<Sum>x \<in>{n}. exp (- x/t)) = exp(-n/t)"
          by simp
        then show ?thesis
          using p by simp
      qed
    qed
    have 2:"(\<Sum>x = 1..<n+1. exp (- x/t)) = (\<Sum>x = 0..<n+1. exp (- x/t)) - 1"
    proof -
      have "(\<Sum>x = 0..<n+1. exp (- x/t)) - 1 = (\<Sum>x = 1..<n+1. exp (- x/t)) + (\<Sum>x = 0..0. exp (- x/t))  - 1"
      proof-
        have "{0..<n+1} = {0} \<union> {1..<n+1}" by auto
        then show ?thesis by simp
      qed
      also have "... = (\<Sum>x = 1..<n+1. exp (- x/t))"
        by simp
      finally show ?thesis
        by simp
    qed 
    show ?thesis
      using 1 2 by simp
  qed
  finally have 1:"(\<Sum>x = 0..<n. exp ((-x)/t)) * (1 - exp (- 1/t)) = 1 - exp ((- n)/t)"
    by simp
  have 2:"0<1-exp(-1/t)"
    using assms by simp
  then show ?thesis
    using 1 2
    by (simp add: nonzero_eq_divide_eq)
qed

lemma exp_suminf:
  fixes t::real
  assumes "0<t"
  shows "(\<Sum>x. exp (- x/t))  = 1/(1-exp(-1/t))"
proof -
  thm sums_def
  have "(\<lambda>x. exp (- real x / t)) sums  (1/(1-exp(-1/t)))"
    unfolding sums_def
  proof -
    have "(\<lambda>n. \<Sum>x<n. exp (- real x / t)) = (\<lambda>n. (1-exp(-n/t))/(1-exp(-1/t)))"
    proof 
      fix n::nat
      show "(\<Sum>x<n. exp (- real x / t)) = (1 - exp (- real n / t)) / (1 - exp (- 1 / t))"
        using exp_sum2[of "t" "n"] assms
        by (simp add: lessThan_atLeast0 sum_negf)
    qed
    also have "... \<longlonglongrightarrow> 1 / (1 - exp (- 1 / t))"
    proof -
      have 1:"(\<lambda>n. - exp(-n/t)/(1-exp(-1/t))) \<longlonglongrightarrow> 0"
      proof-
        have 1:"1 / (1 - exp (- 1 / t)) \<noteq> 0"
        proof-
          have "0<1 - exp (- 1 / t)"
            using assms by simp
          then show ?thesis
            by simp
        qed
        have 2:"(\<lambda>x. (exp (- real x / t)))\<longlonglongrightarrow> 0"
          using assms summable_exp_minu_rat[of "t"] 
                summable_LIMSEQ_zero[of "\<lambda>x. (exp (- real x / t))"]
          by simp
        show ?thesis
        using tendsto_divide[of "\<lambda>n. - exp(-n/t)" "0" "sequentially" "\<lambda>n. 1/(1-exp(-1/t))" "1/(1-exp(-1/t))"]
              1 2 tendsto_minus_cancel_left 
        by force
      qed
      have 2:"(\<lambda>n. 1/(1-exp(-1/t))) \<longlonglongrightarrow> 1/(1-exp(-1/t)) "
        by simp
      have 3:"(\<lambda>x. (1 - exp (- real x / t)) / (1 - exp (- 1 / t)))  = (\<lambda>n. 1/(1-exp(-1/t)) - exp(-n/t)/(1-exp(-1/t)))" 
        apply(rule)
        by argo
      also have "...  \<longlonglongrightarrow> 1 / (1 - exp (- 1 / t))"
        using 1 2  
          tendsto_add[of "\<lambda>n. 1/(1-exp(-1/t))" "1/(1-exp(-1/t))" "sequentially" "\<lambda>n. - exp(-n/t)/(1-exp(-1/t))" "0"]
        by simp
      finally show ?thesis
        by simp
    qed
    finally show "(\<lambda>n. \<Sum>x<n. exp (- real x / t)) \<longlonglongrightarrow> 1 / (1 - exp (- 1 / t))"
      by simp
  qed
  then show ?thesis 
    using sums_unique[of "\<lambda>x. exp (- x/t)" "(1/(1-exp(-1/t)))"] 
    by simp
qed
 

lemma spmf_discrete_laplace_mechanism_Z2k_out_Z2k:
  assumes scale:"1\<le>epsilon1" and "1\<le>epsilon2" 
and seinsitivity:"1\<le>i"
and z:"z\<notin>{d. \<exists>n::int. d = power_2 k * n}"
shows "spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z = 0"
proof -
  have lossless:"weight_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) = 1"
    using lossless_discrete_laplace_mechanism_Z2k assms lossless_spmf_def
    by blast
  have 1:"weight_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) 
    = Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) UNIV"
    using weight_spmf_def by blast
  have set1:"{d. \<exists>n::int. d = power_2 k * n} \<union> {d.\<forall> n::int. d \<noteq> power_2 k * n} = UNIV"
    by auto
  have set2:"{d. \<exists>n::int. d = power_2 k * n} \<inter> {d.\<forall> n::int. d \<noteq> power_2 k * n} = {}"
    by auto
  have 2:"Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) UNIV 
      = Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {d. \<exists>n::int. d = power_2 k * n}
       + Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {d.\<forall> n::int. d \<noteq> power_2 k * n}"
    using set1 set2 plus_measure_spmf by blast
  have 3:"Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {d. \<exists>n::int. d = power_2 k * n} = 1"
  proof -
    have set1:"{power_2 k * n | n::int. True} = {power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n}  \<union> {power_2 k * n | n::int. findNearstMultiple_2k (f x) k>n} "
      by fastforce
    have set2:"{power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n} \<inter> {power_2 k * n | n::int. findNearstMultiple_2k (f x) k>n}= {}"
      apply(rule)
      using power_2_gt_zero[of k]
      by(auto)
    have "measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {d. \<exists>n::int. d = power_2 k * n} 
        = measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n} 
        + measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {power_2 k * n | n::int. findNearstMultiple_2k (f x) k>n}"
      using set1 set2 plus_measure_spmf by fastforce
    have "ennreal (Sigma_Algebra.measure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n})
        = emeasure (measure_spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) ) {power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n}"
      by (simp add: measure_spmf.emeasure_eq_measure)
    also have "... = (\<Sum>\<^sup>+ z\<in>{power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n}. ennreal (spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z))"
      using nn_integral_spmf by metis
    also have "... = (\<Sum>\<^sup>+ z\<in>{power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n}. 
                      ennreal ((exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * (power_2 k * i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
    proof -
      have "\<And>z. z\<in>{d. \<exists>n::int. d = power_2 k * n \<and> findNearstMultiple_2k (f x) k\<le>n} \<Longrightarrow> ennreal (spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z)
                                                     = ennreal ((exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * (power_2 k * i))))/(exp (epsilon1 / (epsilon2 * i)) + 1))"
        sorry
      then show ?thesis
        using nn_integral_cong[of _ "\<lambda>z. ennreal (spmf (discrete_laplace_mechanism_Z2k f i epsilon1 epsilon2 k x) z)" "\<lambda>z. ennreal ((exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * (power_2 k * i))))/(exp (epsilon1 / (epsilon2 * i)) + 1))"]
        by fastforce
    qed
    also have "... =  (\<Sum>\<^sup>+ n\<in>{n. findNearstMultiple_2k (f x) k \<le> n}.
   ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * n - power_2 k * (findNearstMultiple_2k (f x) k)\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
    proof -
      have "bij_betw (\<lambda>x. power_2 k * real_of_int x) {n. findNearstMultiple_2k (f x) k \<le> n} {power_2 k * real_of_int n |n. findNearstMultiple_2k (f x) k \<le> n}"
        sorry
      then show ?thesis
        using nn_integral_bij_count_space[of "\<lambda>n. power_2 k * n" "{n::int. findNearstMultiple_2k (f x) k\<le>n}" "{power_2 k * n | n::int. findNearstMultiple_2k (f x) k\<le>n}"
                                      "\<lambda>z. ennreal ((exp (epsilon1 / (epsilon2 * i)) - 1) * exp (- ((epsilon1 * \<bar>z - power_2 k * findNearstMultiple_2k (f x) k\<bar>) / (epsilon2 * (power_2 k * i))))/(exp (epsilon1 / (epsilon2 * i)) + 1))"]
        by simp
    qed
    also have "... =  (\<Sum>\<^sup>+ n\<in>{n. findNearstMultiple_2k (f x) k \<le> n}.
   ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * (n - (findNearstMultiple_2k (f x) k))\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
    proof -
      have "\<And>n. power_2 k * n - power_2 k * (findNearstMultiple_2k (f x) k) = power_2 k * (n - (findNearstMultiple_2k (f x) k))"
        by argo
      then show ?thesis
        by auto
    qed
    also have "... =  (\<Sum>\<^sup>+ m\<in>{m::int. 0 \<le> m}.
   ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * m\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
    proof -
      have 1:"bij_betw (\<lambda>m. m + (findNearstMultiple_2k (f x) k)) {m. 0\<le>m} {n. findNearstMultiple_2k (f x) k \<le> n}"
        sorry
      then have "(\<Sum>\<^sup>+ n\<in>{n. findNearstMultiple_2k (f x) k \<le> n}.
       ennreal ((exp (real epsilon1 / real (epsilon2 * i)) - 1) * exp (- (real epsilon1 * \<bar>power_2 k * real_of_int (n - findNearstMultiple_2k (f x) k)\<bar> / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / real (epsilon2 * i)) + 1)))
               = (\<Sum>\<^sup>+ m\<in>{m::int. 0 \<le> m}.
       ennreal ((exp (real epsilon1 / real (epsilon2 * i)) - 1) * exp (- (real epsilon1 * \<bar>power_2 k * (m + findNearstMultiple_2k (f x) k - findNearstMultiple_2k (f x) k)\<bar> / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / real (epsilon2 * i)) + 1)))"
        using nn_integral_bij_count_space [of "(\<lambda>m. m + (findNearstMultiple_2k (f x) k))" "{m. 0\<le>m}" "{n. findNearstMultiple_2k (f x) k \<le> n}" 
                                              "\<lambda>n. ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * (n - (findNearstMultiple_2k (f x) k))\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1))"]
        by argo
      also have "... =  (\<Sum>\<^sup>+ m\<in>{m::int. 0 \<le> m}.
   ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * m\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
        by simp
      finally show ?thesis
        by simp
    qed
    also have "... = (\<Sum>\<^sup>+ m\<in>{m::nat. True}.
   ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * m\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1)))"
    proof -
      have 1:"bij_betw (\<lambda>m. int m) {m::nat. True} {m::int. 0\<le>m}"
        sorry
      then show ?thesis
        using nn_integral_bij_count_space[of "\<lambda>m. m" "{m::nat. True}" "{m::int. 0\<le>m}" 
                                             "\<lambda>m. ennreal ((exp (epsilon1/(epsilon2 * i)) - 1) * exp (- (epsilon1 * \<bar>power_2 k * m\<bar> / (epsilon2 * (power_2 k * real i))))/(exp (epsilon1 / (epsilon2 * i)) + 1))"]
        by simp
    qed
    also have "... = (\<Sum>m. ennreal((exp (real epsilon1 / (real epsilon2 * real i)) - 1) * exp (- (real epsilon1 * \<bar>power_2 k * real m\<bar> / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1)))"
      by(simp add: nn_integral_count_space_nat)
    also have "... = (\<Sum>m. ennreal((exp (real epsilon1 / (real epsilon2 * real i)) - 1) * exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1)))"
    proof -
      have "\<And>m::nat. ennreal((exp (real epsilon1 / (real epsilon2 * real i)) - 1) * exp (- (real epsilon1 * \<bar>power_2 k * real m\<bar> / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1))
                    = ennreal((exp (real epsilon1 / (real epsilon2 * real i)) - 1) * exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1))"
        using power_2_gt_zero[of"k"] by simp
      then show ?thesis by metis
    qed
    also have "... = ennreal ((\<Sum>m. (exp (real epsilon1 / (real epsilon2 * real i)) - 1) * exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1)))"
    proof(rewrite suminf_ennreal2,simp_all)
      have 1:"\<And>x::nat. exp (- (real x / (real epsilon2 * real i / real epsilon1))) =  exp (- (real epsilon1 * real x / (real epsilon2 * real i)))"
        using assms by simp
      have 2:"summable (\<lambda>m. exp (- (real m / (real epsilon2 * real i / real epsilon1))))"
        using summable_exp_minu_rat[of "(real epsilon2 * i)/epsilon1"] assms
        by auto
      have "summable (\<lambda>m. exp (- (if power_2 k = 0 then 0 else real epsilon1 * real m / (real epsilon2 * real i))))"
        using power_2_gt_zero[of"k"] 
        apply(auto)
        using 1 2
        by presburger
      then show "exp (real epsilon1 / (real epsilon2 * real i)) + 1 = 0 \<or>
    epsilon1 = 0 \<or> epsilon2 = 0 \<or> i = 0 \<or> summable (\<lambda>m. exp (- (if power_2 k = 0 then 0 else real epsilon1 * real m / (real epsilon2 * real i))))"
        by blast
    qed
    also have "... = ennreal((exp (real epsilon1 / (real epsilon2 * real i)) - 1)/ (exp (real epsilon1 / (real epsilon2 * real i)) + 1)
                     * (\<Sum>m.  exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i))))))"
    proof -
      have "(\<Sum>m. (exp (real epsilon1 / (real epsilon2 * real i)) - 1) * (exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i))))/(exp (real epsilon1 / (real epsilon2 * real i)) + 1))) 
          = (exp (real epsilon1 / (real epsilon2 * real i)) - 1)/ (exp (real epsilon1 / (real epsilon2 * real i)) + 1)
                     * (\<Sum>m.  exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))))"
      proof(rewrite suminf_mult)
        have 1:"summable (\<lambda>m. exp (- (if power_2 k = 0 then 0 else real epsilon1 * real m / (real epsilon2 * real i))))"
          sorry
        then show "summable (\<lambda>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1))"
          by simp
        have 2:" (\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1)) 
             = 1/ (exp (real epsilon1 / (real epsilon2 * real i)) + 1) *
               (\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))))"
        proof-
          have "(\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1)) 
              = (\<Sum>m. (1/ (exp (real epsilon1 / (real epsilon2 * real i)) + 1)) * exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))))"
            by auto
          also have "... = 1/ (exp (real epsilon1 / (real epsilon2 * real i)) + 1) *
               (\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))))"
            apply(rewrite suminf_mult)
            using 1 by auto
          finally show ?thesis by simp
        qed
        then show "(exp (real epsilon1 / (real epsilon2 * real i)) - 1) *
    (\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1)) =
    (exp (real epsilon1 / (real epsilon2 * real i)) - 1) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1) *
    (\<Sum>m. exp (- (real epsilon1 * power_2 k * real m / (real epsilon2 * (power_2 k * real i)))))"
          by simp
      qed
      also have "... = (exp (real epsilon1 / (real epsilon2 * real i)) - 1) / (exp (real epsilon1 / (real epsilon2 * real i)) + 1) *
    (\<Sum>m. exp (- (real epsilon1 *  real m / (real epsilon2 *  real i))))"
        using power_2_gt_zero[of "k"] by auto
      then show ?thesis sorry
    qed
    show ?thesis
      sorry
  qed
  show ?thesis
    sorry
qed







end
