theory Discrete_Laplace_rat
  imports "Bernoulli_exp_minus_rat"
          "Probabilistic_While.Fast_Dice_Roll"
          "Bernoulli_rat"
          "Probabilistic_While.While_SPMF"
begin


lemma map_spmf_bind_spmf_lambda:
"map_spmf f \<circ> (\<lambda>y. bind_spmf (p y) (g y) ) = (\<lambda>y. (p y) \<bind> map_spmf f \<circ> (g y))"
  by (simp add: comp_def map_spmf_bind_spmf)

lemma if_else_return_bind_spmf_2:
"(if b1 then return_spmf x
  else if b2 then return_spmf y 
       else return_spmf z)
  \<bind>  f
= (if b1 then f x
  else if b2 then f y 
       else f z)"
  by simp

lemma ord_spmf_if:
  assumes "ord_spmf (=) p1 q1" and "ord_spmf (=) p2 q2"
  shows "ord_spmf (=) (if b then p1 else p2) (if b then q1 else q2)"
  by (simp add: assms(1) assms(2))

term bind_spmf

lemma ord_spmf_bind:
  assumes "ord_spmf (=) f1 f2" and "\<forall>x. ord_spmf (=) (g1 x) (g2 x)"
  shows "ord_spmf (=) (bind_spmf f1 (\<lambda>x. g1 x)) (bind_spmf f2 (\<lambda>x. g2 x))"
  by (simp add: assms(1) assms(2) bind_spmf_mono')

lemma map_spmf_lambda:
"map_spmf f \<circ> (\<lambda>d. g d) = (\<lambda>d. map_spmf f (g d))"
by auto

lemma map_spmf_if:
"map_spmf f (if b then p1 else p2) = (if b then map_spmf f p1 else map_spmf f p2)"
  by auto

lemma map_spmf_lambda_if:
"map_spmf f \<circ> (\<lambda>d. if b d then spmf_1 else spmf2) = (\<lambda>d. if b d then map_spmf f spmf_1 else map_spmf f spmf2)"
  by auto

lemma map_spmf_return_spmf:
"map_spmf f (return_spmf p) = return_spmf (f p)"
  by simp

lemma set_spmf_if:"set_spmf (if b then f  else g) = (if b then set_spmf(f) else set_spmf(g))"
  by fastforce

lemma set_spmf_bind_set: 
  assumes "\<And>x. A x \<subseteq> B "
  shows "Set.bind (set_spmf p) (\<lambda>x. A x) \<subseteq> B "
  unfolding Set.bind_def using assms by auto

lemma exp_sum:
  fixes t n::nat
  assumes "1\<le>t"
  shows "(\<Sum>x = 0..n. exp (- x/t)) = (1-exp(-(n+1)/t))/(1-exp(-1/t))"
proof -
  have "(\<Sum>x = 0..n. exp (- x/t)) * exp(-1/t) = (\<Sum>x = 1..n+1. exp (- x/t))"
  proof(rewrite sum_distrib_right, simp add:Fract_of_int_quotient of_rat_divide)
    have "\<And>n::nat. exp (-n/t) * exp(-1/t) = exp(-(n+1)/t)"
      apply(simp add: mult_exp_exp)
      by argo
    then have "(\<Sum>n = 0..n. exp (- (n/t)) * exp (- (1/t))) = (\<Sum>n = 0..n. exp (- (n+1)/t))"
      by simp
    also have "... = (\<Sum>n = 1..Suc n. exp (- n/t))"
    proof -
      have "((\<lambda>n::nat. exp (-n/t)) \<circ> Suc) = (\<lambda>n::nat. exp (-(n+1)/real t))"
        apply(simp add: o_def)
        by (simp add: minus_diff_commute minus_divide_left)
      then have "(\<Sum>n = 0..n. exp (real_of_int (- int (n + 1)) / real t)) = sum ((\<lambda>n. exp (real_of_int (- int n) / real t)) \<circ> Suc) {0..n}"
        by simp
      also have "... = (\<Sum>n = Suc 0..Suc n. exp (real_of_int (- int n) / real t))"
        using sum.atLeast_Suc_atMost_Suc_shift[of "(\<lambda>n. exp(-n/t))" "0" "n"]
        by auto
      also have "... = (\<Sum>n = 1..Suc n. exp (- n/t))" 
        using assms(1) by auto
      finally show ?thesis by simp
    qed
    finally have "(\<Sum>n = 0..n. exp (- (real n / real t)) * exp (- (1 / real t))) = (\<Sum>x = Suc 0..Suc n. exp (- (real x / real t)))"
      by simp
    then show "(\<Sum>n = 0..n. exp (- (real n / real t)) * exp (- (1 / real t))) = (\<Sum>x = Suc 0..n. exp (- (real x / real t))) + exp (- ((1 + real n) / real t))"
      by simp
  qed
  then have "(\<Sum>x = 0..n. exp (- x/t)) * (1 -exp(-1/t)) = (\<Sum>x = 0..n. exp (- x/t)) - (\<Sum>x = 1..n+1. exp (- x/t))"
    by(rewrite right_diff_distrib, simp)    
  also have "... = 1 - exp(-(n+1)/t)"
  proof -
    have 1:"(\<Sum>x = 0..n. exp (- x/t))  = (\<Sum>x = 0..n+1. exp (- x/t)) - exp(-(n+1)/t)"
    proof -
      have "(\<Sum>x = 0..n. exp (- x/t)) = (\<Sum>x<n+1. exp (real_of_int (- int x) / real t))"
      proof - 
        have "{0..n} = {0..<n+1}" 
          by auto
        then show ?thesis 
          using lessThan_atLeast0 by presburger
      qed
      also have "... =  (\<Sum>x = 0..n+1. exp (- x/t)) - exp(-(n+1)/t)"
        apply(rewrite sum_lessThan_conv_atMost_nat[of "\<lambda>x. exp(-x/t)" "n+1"],simp)
        by (simp add: atMost_atLeast0)
      finally show ?thesis 
        by simp
    qed
    have 2:"(\<Sum>x = 1..n+1. exp (- x/t)) = (\<Sum>x = 0..n+1. exp (- x/t)) - 1"
    proof -
      have "(\<Sum>x = 0..n+1. exp (- x/t)) - 1 = (\<Sum>x = 1..n+1. exp (- x/t)) + (\<Sum>x = 0..0. exp (- x/t))  - 1"
      proof-
        have "{0..n+1} = {0} \<union> {1..n+1}" by auto
        then show ?thesis by simp
      qed
      also have "... = (\<Sum>x = 1..n+1. exp (- x/t))"
        by simp
      finally show ?thesis
        by simp
    qed 
    show ?thesis
      using 1 2 by simp
  qed
  finally have 1:"(\<Sum>x = 0..n. exp ((-x)/t)) * (1 - exp (- 1/t)) = 1 - exp ((- (n + 1))/t)"
    by simp
  have 2:"0<1-exp(-1/t)"
    using assms by simp
  then show ?thesis
    using 1 2
    by (simp add: nonzero_eq_divide_eq)
qed

lemma exp_sum_general:
  fixes t m n::nat 
  assumes "1\<le>t" and "n \<le> m"
  shows "(\<Sum>x = n..m. exp (- x/t)) = (exp(-n/t)-exp(-(m+1)/t))/(1-exp(-1/t))"
proof- 
  have 1:"(\<Sum>x = n..m. exp (- x/t)) = exp (-n/t) * (\<Sum>x = 0..m-n. exp (- x/t))"
    apply(rewrite sum.atLeastAtMost_shift_0)
    using assms apply(simp)
  proof(simp)
    have "(\<Sum>x = 0..m - n. exp (- ((real n + real x) / real t))) = (\<Sum>x = 0..m - n. exp(-(n/t)) *exp (-(x/t)))"
    proof -
      have "\<And>x::nat. exp (- ((real n + real x) / real t)) = exp(-(n/t)) *exp (-(x/t))"
      proof -
        fix x
        have "- ((n+ real x)/t) = (-(n/t)) + (-(x/t))"
          by (simp add: add_divide_distrib)
        then have "exp (- ((real n + real x) / real t)) =  exp((-(n/t)) + (-(x/t)))"
          by simp
        also have "... = exp(-(n/t)) *exp (-(x/t))"
          by(rule exp_add)
        finally show "exp (- ((real n + real x) / real t)) = exp (- (real n / real t)) * exp (- (real x / real t))"
          by simp
      qed
      then show ?thesis 
        by simp
    qed
    also have "... = exp (-n/t) * (\<Sum>x = 0..m-n. exp (- x/t))"
      by(rewrite sum_distrib_left, simp)
    finally show "(\<Sum>x = 0..m - n. exp (- ((real n + real x) / real t))) = exp (- (real n / real t)) * (\<Sum>x = 0..m - n. exp (- (real x / real t)))"
      by simp
  qed
  have 2:"(\<Sum>x = 0..m-n. exp (- x/t)) = (1-exp(-(m-n+1)/t))/(1-exp(-1/t))"
    apply(rewrite exp_sum[of "t" "m-n"])
    using assms by(simp_all)
  have "exp (-n/t) * (\<Sum>x = 0..m-n. exp (- x/t)) = exp (-n/t) * (1-exp(-(m-n+1)/t))/(1-exp(-1/t))"
    using 2 by simp
  also have "... = (exp(-n/t)-exp(-(m+1)/t))/(1-exp(-1/t))"
  proof -
    have "(-n) + (-(m-n+1)) = - (m+1)"
      by (simp add: assms(2) of_nat_diff)
    then have "-n/t + - (m - n + 1)/t = -(m+1)/t"
      by (metis add_divide_distrib of_int_add)     
    then have "exp(-n/t) * exp(-(m-n+1)/t) = exp(-(m+1)/t)"
      using exp_add[of"-n/t" "-(m-n+1)/t"]
      by auto
    then show ?thesis
      by (simp add: vector_space_over_itself.scale_right_diff_distrib)
  qed
  finally have "exp ((-n)/t) * (\<Sum>x = 0..m - n. exp ((-x)/t)) 
             = (exp ((-n)/t) - exp ((- (m + 1))/t)) / (1 - exp (- 1/t))"
    by simp
  then show ?thesis
    using 1 by auto
qed
  
lemma summable_exp_rat:
  fixes t::nat
  assumes "1\<le>t"
  shows "summable (\<lambda>x. exp (- (real x / real t)))"
proof -
  have 1:"(\<lambda>x::nat. exp (- (real x / real t))) = (\<lambda>x::nat. (exp (- (1/ real t))) ^ x)"
  proof 
    fix x ::nat
    have "exp (-real x/t) = exp (x * (-1/t))"
      by simp
    also have "... = exp(-1/t)^x"
      by (rule exp_of_nat_mult)
    finally show "exp (- (real x / real t)) = exp (- (1 / real t)) ^ x" 
      by simp
  qed
  have "summable (\<lambda>x::nat. (exp (- (1/ real t))) ^ x)"
    apply(rewrite summable_geometric)
    using assms by(simp_all)
  then show "summable (\<lambda>x. exp (- (real x / real t)))"
    using assms 1 by simp
qed

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat_unit_loop1 :: "nat \<Rightarrow> nat spmf" where 
"discrete_laplace_rat_unit_loop1 t = do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract u t);
  if d then return_spmf u else discrete_laplace_rat_unit_loop1 t 
}"

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat_unit_loop2 :: "nat \<Rightarrow> nat spmf" where
"discrete_laplace_rat_unit_loop2 v = do {
              a \<leftarrow> bernoulli_exp_minus_rat 1;
              if a = False then return_spmf v
              else  discrete_laplace_rat_unit_loop2 (v+1)
}"
end


definition discrete_laplace_rat_unit :: "nat \<Rightarrow> nat spmf" where
"discrete_laplace_rat_unit t = do {
  u::nat \<leftarrow> discrete_laplace_rat_unit_loop1 t;
  v::nat \<leftarrow> discrete_laplace_rat_unit_loop2 0;
  return_spmf ((u::nat)+t * v)
}"

definition calculate_y :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"calculate_y x s= nat(floor(x/s))"


context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat :: "nat \<Rightarrow> nat \<Rightarrow> int spmf" where
"discrete_laplace_rat t s = do {
    x::nat \<leftarrow> discrete_laplace_rat_unit t;
    b::bool \<leftarrow> bernoulli_rat 1 2;
    let y = calculate_y x s in
    if (\<not>b \<and> (y=0)) then discrete_laplace_rat t s
    else if b then return_spmf (-y)
         else return_spmf y
}
"
end

thm discrete_laplace_rat_unit_loop1.fixp_induct

lemma discrete_laplace_rat_unit_loop1_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P" 
and "P (\<lambda>discrete_laplace_rat_unit_loop1. return_pmf None)"
and "(\<And>t. P t \<Longrightarrow> P (\<lambda>ta. fast_uniform ta \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int ta)) \<bind> (\<lambda>d. if d then return_spmf u else t ta))))"
shows "P discrete_laplace_rat_unit_loop1"
  using assms by (rule discrete_laplace_rat_unit_loop1.fixp_induct)

lemma discrete_laplace_rat_unit_loop2_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>discrete_laplace_rat_unit_loop2. return_pmf None)"
and "(\<And>discrete_laplace_rat_unit_loop2'. P discrete_laplace_rat_unit_loop2' \<Longrightarrow> P (\<lambda>va. bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf va else discrete_laplace_rat_unit_loop2' (va + 1))))"
shows "P discrete_laplace_rat_unit_loop2"
  using assms by (rule discrete_laplace_rat_unit_loop2.fixp_induct)

thm discrete_laplace_rat.fixp_induct

lemma discrete_laplace_rat_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>discrete_laplace_rat. P (curry discrete_laplace_rat))"
and "P (\<lambda>discrete_laplace_rat t. return_pmf None)"
and "(\<And>s. P s \<Longrightarrow>
      P (\<lambda>a b. discrete_laplace_rat_unit a \<bind>
                 (\<lambda>x. bernoulli_rat 1 2 \<bind> (\<lambda>ba. let x = calculate_y x b in if \<not> ba \<and> int x = 0 then s a b else if ba then return_spmf (- int x) else return_spmf (int x)))))  "
shows "P discrete_laplace_rat"
  using assms by (rule discrete_laplace_rat.fixp_induct)

context 
  fixes body ::"bool \<times> nat \<times> nat \<Rightarrow> (bool \<times> nat \<times> nat) spmf"
  defines [simp]:"body \<equiv> (\<lambda>(b,t::nat,u1::nat). do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract (int u) t);
  if d then return_spmf (False, t,u) else return_spmf (True, t,0) 
})"
begin
interpretation loop_spmf fst body
  rewrites "body \<equiv> (\<lambda>(b::bool,t::nat,u1). do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract (int u) t);
  if d then return_spmf (False, t, u) else return_spmf (True, t,0) 
})"
  by(fact body_def)

lemma discrete_laplace_rat_unit_loop1_conv_while:
  assumes "1\<le>t"
  shows "discrete_laplace_rat_unit_loop1 t = map_spmf (\<lambda>triple. snd(snd(triple))) (while (True, t, 0))" (is "?lhs = ?rhs")
proof (rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof (induction rule: discrete_laplace_rat_unit_loop1_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step t)
    then show ?case
      apply(rewrite while.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      apply(rewrite while.simps)
      apply(clarsimp)
      done
  qed
next
  have "ord_spmf (=) ?rhs ?lhs"
and "\<And>u. ord_spmf (=) (map_spmf (\<lambda>triple. snd(snd(triple))) (while (False, t, u))) (return_spmf u)"
  proof (induction rule:while_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case by simp
  next
    case (step while')
    case 1 show ?case using step
      by(rewrite discrete_laplace_rat_unit_loop1.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
    case 2 show ?case by simp
  qed
  then show "ord_spmf (=) ?rhs ?lhs" by simp
qed

lemma lossless_discrete_laplace_rat_unit_loop1[simp]:
  assumes "1\<le>t"
  shows "lossless_spmf (discrete_laplace_rat_unit_loop1 t)"
proof -
  have "lossless_spmf (while (True, t, 0))"
  proof (rule termination_0_1_immediate_invar,clarify)
    show " 0 < (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t))))" 
    proof -
      have "0 < 1/t * exp (- real_of_rat (Fract (int 0) (int t)))" 
        using assms by simp
      also have "... = (\<Sum>x = 0..0. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
        by simp
      also have "... \<le> (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
      proof - 
        have 1:"{0} \<subseteq> {0..t-1}" by simp
        have 2:"\<And>x. x\<in>{0..t-1} \<Longrightarrow> 0\<le> 1/t * exp (- real_of_rat (Fract (int x) (int t)))"
          by simp
        show ?thesis  
          using 1 2 by(rewrite sum_mono2,simp_all)
      qed
      finally show ?thesis by simp
    qed
  next
    fix b::bool and t1 u::nat
    assume I:"(\<lambda>(b,t1,u).t1 = t) (b,t1,u)"
    show "(\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t)))) \<le> spmf (map_spmf fst
                    (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind> (\<lambda>d. if d then return_spmf (False, t1, u) else return_spmf (True, t1, 0)))))
              False"
    proof -
      have 1:"spmf (map_spmf fst
                    (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind> (\<lambda>d. if d then return_spmf (False, t1, u) else return_spmf (True, t1, 0))))) False
          = spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False"
        by (simp add: map_spmf_bind_spmf map_spmf_bind_spmf_lambda map_spmf_if o_def, rewrite map_spmf_return_spmf, rewrite map_spmf_return_spmf, rewrite fst_conv, rewrite fst_conv, simp)
      have "ennreal (spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False)
          = (\<Sum>x. ennreal (spmf (fast_uniform t1) x) * ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) True))"
        by(simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_nat nn_integral_count_space_finite UNIV_bool)
      also have "... = (\<Sum>x=0..t1-1. ennreal (1/t1) * ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) True))"
      proof (rewrite suminf_finite[of "{0..t1-1}"],simp_all add: spmf_fast_uniform)
        have "\<And>n. n\<in>{0..t1-1} \<Longrightarrow> (if n < t1 then 1 / real t1 else 0) = 1/t1"
          by auto
        then show "(\<Sum>n = 0..t1 - Suc 0. ennreal (if n < t1 then 1 / real t1 else 0) * ennreal (spmf (bernoulli_exp_minus_rat (Fract (int n) (int t1))) True))
                = (\<Sum>x = 0..t1 - Suc 0. ennreal (1 / real t1) * ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) True))"
          by(simp)
      qed
      also have "... = (\<Sum>x = 0..t1 - Suc 0. ennreal (1/t1) * ennreal (exp(-(of_rat (Fract x t1)))))"
      proof(rewrite spmf_bernoulli_exp_minus_rat_True,simp_all)
        show "\<And>x::nat. 0 \<le> Fract (int x) (int t1)" 
          using I assms by (simp add: zero_le_Fract_iff)
      qed
      also have "... = (\<Sum>x = 0..t1 - Suc 0. ennreal ((1/t1) * exp(-(of_rat (Fract x t1)))))"
      proof -
        have "\<And>x. ennreal (1 / real t1) * ennreal (exp (- real_of_rat (Fract (int x) (int t1)))) = ennreal ((1/t1) * exp(-(of_rat (Fract x t1))))"
          by(rewrite ennreal_mult', simp_all)
        then show ?thesis by simp
      qed
      also have "... = (\<Sum>x = 0..t - Suc 0. (1/t) * exp(-(of_rat (Fract x t))))"
        using I by simp
      finally have nn:"ennreal (spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False)
                  = ennreal (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t)))) "
        by simp
      then have "spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False
                = (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
      proof -
        have 1:"0\<le>spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False"
          by simp
        have 2:"0 < (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
        proof -
          have "0 < 1/t * exp (- real_of_rat (Fract (int 0) (int t)))" 
            using assms by simp
          also have "... = (\<Sum>x = 0..0. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
            by simp
          also have "... \<le> (\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t))))"
          proof - 
            have 1:"{0} \<subseteq> {0..t-1}" by simp
            have 2:"\<And>x. x\<in>{0..t-1} \<Longrightarrow> 0\<le> 1/t * exp (- real_of_rat (Fract (int x) (int t)))"
              by simp
            show ?thesis  
              using 1 2 by(rewrite sum_mono2,simp_all)
          qed
          finally show ?thesis by simp
        qed
        show ?thesis using 1 2 nn by simp
      qed
      then have 2:"(\<Sum>x = 0..t - 1. 1/t * exp (- real_of_rat (Fract (int x) (int t)))) \<le> spmf (fast_uniform t1 \<bind> (\<lambda>x. bernoulli_exp_minus_rat (Fract (int x) (int t1)) \<bind> (\<lambda>x. if x then return_spmf False else return_spmf True))) False"
        by simp
      show ?thesis using 1 2 by simp
    qed
  next
    fix s:: "bool\<times>nat\<times>nat" 
    show " (case s of (b, t1, u) \<Rightarrow> t1 = t) \<Longrightarrow>
         lossless_spmf
          (case s of
           (b, t, u1) \<Rightarrow> fast_uniform t \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind> (\<lambda>d. if d then return_spmf (False, t, u) else return_spmf (True, t, 0))))"
    proof (clarify,auto)
      show "0 < t" using assms by simp
      show "\<And>xa::nat. xa \<in> set_spmf (fast_uniform t) \<Longrightarrow> lossless_spmf (bernoulli_exp_minus_rat (Fract (int xa) (int t))) "
      proof(rewrite lossless_bernoulli_exp_minus_rat,simp_all)
        show "\<And>x::nat. 0 \<le> Fract (int x) (int t) "
          using assms by (simp add:zero_le_Fract_iff)
      qed
    qed
  next
    show "\<And>s s'.
       s' \<in> set_spmf
              (case s of
               (b, t, u1) \<Rightarrow>
                 fast_uniform t \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind> (\<lambda>d. if d then return_spmf (False, t, u) else return_spmf (True, t, 0)))) \<Longrightarrow>
       (case s of (b, t1, u) \<Rightarrow> t1 = t) \<Longrightarrow> fst s \<Longrightarrow> case s' of (b, t1, u) \<Rightarrow> t1 = t"
    proof (clarify)
      fix b1 t1 u1 b2 t2 u2
      assume H:"(b2, t2, u2)
       \<in> set_spmf (fast_uniform t \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind> (\<lambda>d. if d then return_spmf (False, t, u) else return_spmf (True, t, 0))))"
      show "t2 = t"
      proof -
        have "set_spmf (fast_uniform t \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind> (\<lambda>d. if d then return_spmf (False, t, u) else return_spmf (True, t, 0))))
            \<subseteq> {(True,t,0)}\<union>{(b,t3,u). b=False\<and>t3=t }"
          by(simp add: set_bind_spmf o_def,rewrite set_spmf_if,rewrite set_return_spmf, rewrite set_return_spmf,simp add:set_spmf_bind_set)
        then have "(b2, t2, u2)\<in> {(True,t,0)}\<union>{(b,t3,u). b=False\<and>t3=t }" 
          using H by auto
        then show "t2 =t"
          by auto
      qed
    qed
  next
    show "case (True, t, 0) of (b, t1, u) \<Rightarrow> t1 = t"
      by simp
  qed
  then show ?thesis 
    using discrete_laplace_rat_unit_loop1_conv_while assms by auto
qed

end

lemma spmf_discrete_laplace_rat_unit_loop1[simp]:
  fixes u::nat
  assumes "1\<le>t" and "u<t"
  shows "spmf (discrete_laplace_rat_unit_loop1 t) u = exp (-u/t)* (1 - exp (- 1/t))/ (1 - exp (- 1))"
proof -
  have "ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) 
      = ennreal (spmf (fast_uniform t \<bind> (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind> (\<lambda>d. if d then return_spmf u else discrete_laplace_rat_unit_loop1 t))) u)"
    by(simp add:discrete_laplace_rat_unit_loop1.simps)
  also have "... = (\<Sum>x. ennreal (spmf (fast_uniform t) x) *
          (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) False) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
           ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) True) * ennreal (indicat_real {Some u} (Some x))))"
    by(simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_nat UNIV_bool nn_integral_count_space_finite)
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal (1/t) *
          (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) False) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
           ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) True) * ennreal (indicat_real {Some u} (Some x))))"
  proof (rewrite spmf_fast_uniform,rewrite suminf_finite[of"{0..t-1}"],simp_all)
    have "\<And>x. x\<in>{0..t-1} \<Longrightarrow> (if x < t then 1 / real t else 0) = 1/t" 
      using assms by simp
    then show "(\<Sum>n = 0..t - Suc 0.
        ennreal (if n < t then 1 / real t else 0) *
        (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int n) (int t))) False) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
         ennreal (spmf (bernoulli_exp_minus_rat (Fract (int n) (int t))) True) * ennreal (indicat_real {Some u} (Some n)))) =
    (\<Sum>x = 0..t - Suc 0.
        ennreal (1 / real t) *
        (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) False) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
         ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) True) * ennreal (indicat_real {Some u} (Some x))))"
      by simp
  qed
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal (1/t) *
          (ennreal (1-exp(-(of_rat (Fract x t)))) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
           ennreal (exp(-(of_rat (Fract x t)))) * ennreal (indicat_real {Some u} (Some x))))"
  proof(rewrite spmf_bernoulli_exp_minus_rat_True)
    show 1:"\<And>x::nat. 0 \<le> Fract (int x) (int t)" 
      using assms by (simp add: zero_le_Fract_iff)
    show "(\<Sum>x = 0..t - 1. ennreal (1 / real t) *
        (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t))) False) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
         ennreal (exp (- real_of_rat (Fract (int x) (int t)))) * ennreal (indicat_real {Some u} (Some x)))) =
    (\<Sum>x = 0..t - 1. ennreal (1 / real t) *
        (ennreal (1 - exp (- real_of_rat (Fract (int x) (int t)))) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) +
         ennreal (exp (- real_of_rat (Fract (int x) (int t)))) * ennreal (indicat_real {Some u} (Some x))))"
      by(rewrite spmf_bernoulli_exp_minus_rat_False, simp_all add:1)
  qed
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal (1/t) * (ennreal (1-exp(-(of_rat (Fract x t)))) * ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u))
                                 + ennreal (1/t) * (ennreal (exp(-(of_rat (Fract x t)))) * ennreal (indicat_real {Some u} (Some x))))"
    by(simp add: ring_distribs(1))
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal ((1/t) * (1-exp(-(of_rat (Fract x t)))) * (spmf (discrete_laplace_rat_unit_loop1 t) u))
                                 + ennreal ((1/t) * (exp(-(of_rat (Fract x t)))) * (indicat_real {Some u} (Some x))))"
    apply(rewrite ennreal_mult'', simp, rewrite ennreal_mult', simp, rewrite ennreal_mult'', simp, rewrite ennreal_mult', simp)
    by (simp add: mult.commute mult.left_commute)
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal ((1/t) * (1-exp(-(of_rat (Fract x t)))) * (spmf (discrete_laplace_rat_unit_loop1 t) u)))
                 + (\<Sum>x\<in>{0..t-1}. ennreal ((1/t) * (exp(-(of_rat (Fract x t)))) * (indicat_real {Some u} (Some x))))"
    by(simp add: sum.distrib)
  also have "... = (\<Sum>x\<in>{0..t-1}. ennreal ((1/t) * (1-exp(-(of_rat (Fract x t)))) * (spmf (discrete_laplace_rat_unit_loop1 t) u)))
                 + (ennreal ((1/t) * (exp(-(of_rat (Fract u t))))))"
  proof(simp)
    have "(\<Sum>x = 0..t - Suc 0. exp (- real_of_rat (Fract (int x) (int t))) * indicat_real {Some u} (Some x)/t) =
          (\<Sum>x \<in> {u}. exp (- real_of_rat (Fract (int x) (int t))) * indicat_real {Some u} (Some x)/t)
        + (\<Sum>x \<in> {0..t-1} - {u}. exp (- real_of_rat (Fract (int x) (int t))) * indicat_real {Some u} (Some x)/t) "
    proof(rewrite sum.subset_diff[of"{u}"],simp_all)  
      show "u \<le> t - Suc 0"
        using assms by simp
    qed
    also have "... = exp (- real_of_rat (Fract (int u) (int t)))/t"
      by simp
    finally have " (\<Sum>x = 0..t - Suc 0. exp (- real_of_rat (Fract (int x) (int t))) * indicat_real {Some u} (Some x)/t)
                  = exp (- real_of_rat (Fract (int u) (int t)))/t"
      by simp
    then show "ennreal (\<Sum>x = 0..t - Suc 0. exp (- real_of_rat (Fract (int x) (int t))) * indicat_real {Some u} (Some x)/t) 
             = ennreal (exp (- real_of_rat (Fract (int u) (int t)))/t)"
      by simp
  qed
  also have "... = ennreal (\<Sum>x = 0..t - 1. (1/t * (1 - exp (- real_of_rat (Fract (int x) (int t)))) * spmf (discrete_laplace_rat_unit_loop1 t) u)) 
                 + ennreal (1/t * exp (- real_of_rat (Fract (int u) (int t))))"
  proof -
    have "(\<Sum>x = 0..t - 1. ennreal (1/t * (1 - exp (- real_of_rat (Fract (int x) (int t)))) * spmf (discrete_laplace_rat_unit_loop1 t) u)) 
        = ennreal (\<Sum>x = 0..t - 1. (1/t * (1 - exp (- real_of_rat (Fract (int x) (int t)))) * spmf (discrete_laplace_rat_unit_loop1 t) u))"
    proof (rule sum_ennreal)
      fix x::nat
      assume x:"x \<in> {0..t - 1}"
      have 1:"0 \<le> 1/t" 
        using assms by simp
      have " exp (- real_of_rat (Fract (int x) (int t)))\<le> 1 "
      proof(rewrite exp_le_one_iff,simp)
        show "0 \<le> Fract (int x) (int t)"
          using x assms by (simp add: zero_le_Fract_iff)
      qed
      then have 2:"0 \<le> (1 - exp (- real_of_rat (Fract (int x) (int t))))"
        by simp
      have 3:"0 \<le> spmf (discrete_laplace_rat_unit_loop1 t) u"
        by simp
      show "0 \<le> 1/t * (1 - exp (- real_of_rat (Fract (int x) (int t)))) * spmf (discrete_laplace_rat_unit_loop1 t) u"
        using 1 2 3 by simp
    qed
    then show ?thesis by simp
  qed
  also have "... = ennreal (1/t * (\<Sum>x = 0..t - 1. (1 - exp (- real_of_rat (Fract (int x) (int t))))) * spmf (discrete_laplace_rat_unit_loop1 t) u)
                 + ennreal (1/t * exp (- real_of_rat (Fract (int u) (int t))))"
  proof -
    have "(\<Sum>x = 0..t - 1. 1 / real t * (1 - exp (- real_of_rat (Fract (int x) (int t)))) * spmf (discrete_laplace_rat_unit_loop1 t) u) 
        = 1/t * (\<Sum>x = 0..t - 1. 1 - exp (- real_of_rat (Fract (int x) (int t)))) *  spmf (discrete_laplace_rat_unit_loop1 t) u"
      by(rewrite sum_distrib_left,rewrite sum_distrib_right, simp)
    then show ?thesis 
      by simp
  qed
  also have "... = ennreal (1/t * (\<Sum>x = 0..t - 1. 1 - exp (- x/t)) * spmf (discrete_laplace_rat_unit_loop1 t) u) 
                 + ennreal (1/t * exp (-u/t))"
    by(simp add:Fract_of_int_quotient of_rat_divide)
  also have "... = ennreal (1/t * (t-(1-exp(-1))/(1-exp(-1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u)
                 + ennreal (1/t * exp (-u/t))"
  proof -
    have " (\<Sum>x = 0..t - 1. 1 - exp (- x/t)) = t -  (\<Sum>x = 0..t - 1. exp (- x/t))"
      apply(rewrite sum_subtractf,simp)
      using assms(1) by force
    also have "... = t - (1-exp(-1))/(1-exp(-1/t))"
      using exp_sum[of"t" "t-1"] assms by simp
    finally have "(\<Sum>x = 0..t - 1. 1 - exp (- x/t)) =  t - (1-exp(-1))/(1-exp(-1/t))"
      by simp
    then show ?thesis 
      by simp
  qed
  finally have 1:"ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) 
              = ennreal (1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u) + ennreal (1/t * exp (-u/t))"
    by simp
  have "spmf (discrete_laplace_rat_unit_loop1 t) u
           = 1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u + 1/t * exp (-u/t)"
  proof -
    have "0 \<le> (\<Sum>x = 0..t - 1. 1 - exp (- x/t))"
    proof -
      have "\<And>x::nat. x\<in>{0..t-1} \<Longrightarrow> 0\<le>1-exp(-x/t)"
        by simp
      then show ?thesis
        by (simp add:sum_nonneg)
    qed
    also have "... = t - (\<Sum>x = 0..t - 1. exp (- x/t))"
      apply(rewrite sum_subtractf,simp)
      using assms(1) by force
    also have "... = t - (1 - exp (- 1)) / (1 - exp (- 1/t))"
      using assms exp_sum[of "t" "t-1"] by simp
    finally have "0\<le>  t - (1 - exp (- 1)) / (1 - exp (- 1/t))"
      by simp
    then have p1:"0\<le> 1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u"
      using assms by simp
    have p2:"0\<le>1/t * exp (-u/t)"
      by simp
    have p3:"0 \<le> 1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u + 1/t * exp (-u/t)"
      using p1 p2 by simp
    have p4:"0\<le>spmf (discrete_laplace_rat_unit_loop1 t) u"
      by simp
    have "ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) 
        = ennreal (1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))) * spmf (discrete_laplace_rat_unit_loop1 t) u + 1/t * exp (-u/t))"
      apply(rewrite ennreal_plus)
      using p1 p2 1 by(simp_all)
    then show ?thesis
      using p3 p4 by(simp)
  qed
  then have 2:"spmf (discrete_laplace_rat_unit_loop1 t) u * (1- 1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t))))
           = 1/t * exp (-u/t) "
    by argo
  show "spmf (discrete_laplace_rat_unit_loop1 t) u = exp (-u/t)* (1 - exp (- 1/t))/ (1 - exp (- 1))"
  proof -
    have "(1- 1/t * (t - (1 - exp (- 1)) / (1 - exp (- 1/t)))) = 1/t * (1 - exp (- 1)) / (1 - exp (- 1/t))"
      apply(rewrite right_diff_distrib)
      using assms by simp
    then have "1/t * spmf (discrete_laplace_rat_unit_loop1 t) u * (1 - exp (- 1)) / (1 - exp (- 1/t))
             = 1/t * exp (-u/t) "
      using 2 by simp
    then have p1:"spmf (discrete_laplace_rat_unit_loop1 t) u * (1 - exp (- 1)) / (1 - exp (- 1/t))
             = exp (-u/t) "
      apply(rewrite scale_left_imp_eq[of "1/t"],simp_all)
      using assms by simp
    show ?thesis
    proof -
      have "spmf (discrete_laplace_rat_unit_loop1 t) u * (1 - exp (- 1)) / (1 - exp (- 1/t)) * (1 - exp (- 1/t))/ (1 - exp (- 1))
          = spmf (discrete_laplace_rat_unit_loop1 t) u"
        using assms by(simp)
      then show ?thesis
        using p1 by metis
    qed
  qed
qed

lemma spmf_spmf_discrete_laplace_rat_unit_loop1_zero[simp]:
  fixes u::nat
  assumes "1\<le>t" and "t\<le>u"
  shows "spmf (discrete_laplace_rat_unit_loop1 t) u = 0"
  sorry
    

context
  fixes body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"
  by(fact body_def)

lemma discrete_laplace_rat_unit_loop2_conv_while:
  "discrete_laplace_rat_unit_loop2 1 = map_spmf snd (while (True,1))"
proof -
  have "discrete_laplace_rat_unit_loop2 x = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule: discrete_laplace_rat_unit_loop2_fixp_induct)
      case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next
      case (step loop')
      then show ?case using step.IH[of "Suc x"]
        apply(rewrite while.simps)
        apply(clarsimp)
        apply(clarsimp simp add: map_spmf_bind_spmf)
        apply(clarsimp simp add:bind_map_spmf)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        apply(rewrite while.simps)
        apply(clarsimp)
        done
    qed
    have "ord_spmf (=) ?rhs ?lhs"
    and "ord_spmf (=) (map_spmf snd (while (False,x))) (return_spmf x)"
    proof(induction arbitrary: x and x rule: while_fixp_induct)
      case adm show ?case by simp
      case bottom case 1 show ?case by simp
      case bottom case 2 show ?case by simp
    next
      case (step while')
      case 1 show ?case using step.IH(1)[of "Suc x"] step.IH(2)[of x]
        by(rewrite discrete_laplace_rat_unit_loop2.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

lemma lossless_discrete_laplace_rat_unit_loop2 [simp]: "lossless_spmf (discrete_laplace_rat_unit_loop2 1)"
proof - 
  have "lossless_spmf (while (True,1))"
  proof (rule termination_0_1_immediate,clarify)
    fix a::bool and  b::nat
    show "1-exp(-1) \<le> spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli_exp_minus_rat 1))) False"
    proof -
      have "ennreal (1-exp (-1)) = spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli_exp_minus_rat 1))) False"
        apply(simp add: ennreal_spmf_map_conv_nn_integral)
        apply(simp add: nn_integral_measure_spmf)
        apply(simp add: UNIV_bool)               
        apply(simp add: nn_integral_count_space_finite)
      proof-
        have "Collect Not = {False}" by blast
        then show "card (Collect Not) = Suc 0" by simp
      qed
      then show ?thesis by simp
    qed
    show "0 < 1 - exp (- 1::real)" by simp
    show "\<And>s. fst s \<Longrightarrow> lossless_spmf (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli_exp_minus_rat 1))"
      using lossless_bernoulli_exp_minus_rat by auto
  qed
  then show ?thesis using discrete_laplace_rat_unit_loop2_conv_while by simp
qed

lemma lossless_discrete_laplace_rat_unit_loop2_zero[simp]:
"lossless_spmf (discrete_laplace_rat_unit_loop2 0)"
  apply(rewrite discrete_laplace_rat_unit_loop2.simps)
proof(simp, auto, simp add:lossless_bernoulli_exp_minus_rat)
  show "lossless_spmf (discrete_laplace_rat_unit_loop2 (Suc 0)) " using lossless_discrete_laplace_rat_unit_loop2 by simp
qed

end

lemma spmf_discrete_laplace_rat_unit_loop2_zero_fixp_induct_case_adm:
  shows "spmf.admissible (\<lambda>loop. \<forall>l>m. spmf (loop l) m = 0)"
proof(simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf, clarify)
  fix A l
  assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
  H: "\<forall>x\<in>A.\<forall>l>m. spmf (x l) m = 0" and
  L: "l>m" 
  have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f l}) m =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f l}. spmf p m)"
  proof(rule spmf_lub_spmf)
    show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f l}" 
      by (simp add: CA chain_fun)
  next 
    show "{y. \<exists>f\<in>A. y = f l} \<noteq> {}" using A by blast
  qed
  have "... =  \<Squnion>{0}"
  proof (rule cong[where f=Sup and g=Sup],simp)
    show " (\<lambda>p. spmf p m) ` {y. \<exists>f\<in>A. y = f l} = {0}"
      using A H L by (auto simp add: image_def)
  qed
  also have "... = 0"
    by simp
  finally show  "spmf (lub_spmf {y. \<exists>f\<in>A. y = f l}) m = 0"
    using P by presburger
qed

lemma spmf_discrete_laplace_rat_unit_loop2_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (discrete_laplace_rat_unit_loop2  l) m = 0"
proof (induction rule: discrete_laplace_rat_unit_loop2_fixp_induct)
  case adm
  then show ?case 
    using spmf_discrete_laplace_rat_unit_loop2_zero_fixp_induct_case_adm by blast
next
  case bottom
  then show ?case by simp
next
  case (step loop')
  then show ?case 
  proof (clarify)
    fix l
    assume Step:"\<forall>l>m. spmf (loop' l) m = 0" and L:"m<l"
    have "ennreal (spmf (bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf l else loop' (l + 1))) m) = 0"
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
      using L Step not_less_eq option.inject order_less_imp_not_less singletonD
      by auto
    then show "spmf (bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf l else loop' (l + 1))) m = 0"
      by simp
  qed
qed

lemma spmf_discrete_laplace_rat_unit_loop2 [simp]: 
  shows "spmf (discrete_laplace_rat_unit_loop2 0) m = (exp(-1))^(m) * (1-exp(-1))"
proof -
  have P:"\<forall>k l::nat .  ennreal (spmf (discrete_laplace_rat_unit_loop2 k) (k+l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
  proof rule+
    fix l
    show "\<And>k.
           ennreal (spmf (discrete_laplace_rat_unit_loop2 k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have 1:"ennreal (spmf (discrete_laplace_rat_unit_loop2 k) (k + 0)) = ennreal (1 - (exp (- 1)))"
          apply(rewrite discrete_laplace_rat_unit_loop2.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          apply(simp add: spmf_discrete_laplace_rat_unit_loop2_zero)
          done
        have 2:"ennreal (exp (- 1) ^ 0 * (1 - exp (- 1))) = ennreal (1 - (exp (- 1)))"
          by simp
        show ?thesis using 1 2 by simp
      qed
    next
      case (Suc l)
      then show ?case
      proof -
        assume step:"\<And>k. 
                    ennreal (spmf (discrete_laplace_rat_unit_loop2 k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
           
        have "ennreal (spmf (discrete_laplace_rat_unit_loop2 k) (k + Suc l)) = exp (- 1) * ennreal (spmf (discrete_laplace_rat_unit_loop2 (Suc k)) (Suc (k + l)))"
          apply(rewrite discrete_laplace_rat_unit_loop2.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal ((exp (- 1)) ^ Suc l * (1- (exp (- 1))))"
          using step[of"Suc k"] apply(simp add: ennreal_mult)
          by (rule semiring_normalization_rules(18))
        finally show ?thesis by simp
      qed
    qed
  qed
  have "ennreal (spmf (discrete_laplace_rat_unit_loop2 0) m) = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
  proof -
    have "ennreal (spmf (discrete_laplace_rat_unit_loop2 0) m) = ennreal (spmf (discrete_laplace_rat_unit_loop2 0) (0+m))"
      by auto
    also have "... = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
      using P by blast
    finally show ?thesis by simp
  qed
  then show ?thesis by simp
qed

lemma lossless_discrete_laplace_rat_unit:
  assumes "1\<le>t"
  shows "lossless_spmf (discrete_laplace_rat_unit t)"
  using assms
  apply(rewrite discrete_laplace_rat_unit_def)
  by(simp)

thm discrete_laplace_rat.simps
(*declare [[show_types]]*)
lemma spmf_discrete_laplace_rat_unit[simp]:
  assumes "1\<le>t"
  shows "spmf (discrete_laplace_rat_unit t) x = (1-exp(-1/t)) * exp(-x/t)"
proof -
  have "ennreal (spmf (discrete_laplace_rat_unit t) x)
      = (\<Sum>u. ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) *
           (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (u + t * v)))))"
    apply(rewrite discrete_laplace_rat_unit_def)
    by(simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_nat)
  also have "(\<Sum>u. ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u) *
           (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (u + t * v)))))
          = (\<Sum>u\<in>{0..t-1}. ennreal (exp (-u/t)* (1 - exp (- 1/t))/ (1 - exp (- 1))) *
           (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (u + t * v)))))"
  proof (rewrite suminf_finite[of"{0..t-1}"],simp_all)
    have 1:"\<And>u. u\<in>{0..t-1} \<Longrightarrow>  spmf (discrete_laplace_rat_unit_loop1 t) u = exp (-u/t)* (1 - exp (- 1/t))/ (1 - exp (- 1)) "
      using assms by simp
    have 2:"\<And>u::nat. u\<notin>{0..t-1} \<Longrightarrow>  spmf (discrete_laplace_rat_unit_loop1 t) u = 0"
      using assms by simp
    show "\<And>n. \<not> n \<le> t - Suc 0 \<Longrightarrow>
         spmf (discrete_laplace_rat_unit_loop1 t) n = 0 \<or> (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (n + t * v)))) = 0"
      using 2 by simp
    show "(\<Sum>n = 0..t - Suc 0.
        ennreal (spmf (discrete_laplace_rat_unit_loop1 t) n) * (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (n + t * v))))) =
    (\<Sum>u = 0..t - Suc 0.
        ennreal (exp (- (real u / real t)) * (1 - exp (- (1 / real t))) / (1 - exp (- 1))) *
        (\<Sum>v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (indicat_real {Some x} (Some (u + t * v)))))"
      using 1 by simp
  qed
  also have "... = (\<Sum>u = 0..t - 1. ennreal (exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1))) *
       (\<Sum>v. ennreal ((exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))))"
    by(simp add: ennreal_mult)
  also have "... = (\<Sum>u = 0..t - 1. ennreal (exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1))) *
       ennreal (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))))"
  proof -
    
    have 1:"\<And>u::nat. (\<Sum>v. ennreal ((exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))) 
        = ennreal (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))"
    proof -
      fix u 
      show "(\<Sum>v. ennreal ((exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))) 
        = ennreal (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))"
      proof(rewrite suminf_ennreal,simp_all,rewrite ennreal_suminf_neq_top,simp_all)
        have 1:"\<And>v. (\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v)))v
                   \<le> (\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1)))v "
          by simp
        have 2:"summable (\<lambda>v::nat. exp (- 1::real) ^ v * (1 - exp (- 1))) "
        proof -
          have "norm (exp(-1::real)) < 1"
            by simp
          then show ?thesis
            by (simp add: summable_mult2)
        qed
        show "summable (\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v)))"
          apply(rewrite summable_comparison_test [of"\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v))" "\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1))"],simp_all)
          using 2 by simp
      qed
    qed
    show ?thesis 
      using 1 by(simp)
  qed
  also have "... = (\<Sum>u = 0..t - 1. ennreal ((exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1))) *
        (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v))))))"
    by(rewrite ennreal_mult',simp_all)
  also have "... = (\<Sum>u = 0..t - 1. (exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1))) *
        (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))))"
  proof(rule sum_ennreal,simp_all)
    fix u ::nat
    assume "u\<le> t-Suc 0"
    show "0 \<le> exp (- (real u / real t)) * (1 - exp (- (1 / real t))) * (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v))) / (1 - exp (- 1))"
    proof -
      have 1:"0 \<le> exp (- (u/t)) * (1 - exp (- (1/t)))" 
        by simp
      have 2:"0\<le>  (\<Sum>v. (\<lambda>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v)))v)"
      proof (rewrite suminf_nonneg,simp_all)
        have 1:"\<And>v. exp (- 1) ^ v * (1 - exp (- 1)) * indicat_real {Some x} (Some (u + t * v)) \<le> exp (- 1) ^ v * (1 - exp (- 1))"
          by simp
        have "summable  (\<lambda>v. exp (- 1::real) ^ v * (1 - exp (- 1)))"
          by(rewrite summable_mult2,simp_all)
        then show "summable (\<lambda>v::nat. exp (- (1::real)) ^ v * ((1::real) - exp (- (1::real))) * indicat_real {Some x} (Some (u + t * v)))"
          by(rewrite summable_comparison_test[of "(\<lambda>v::nat. exp (- (1::real)) ^ v * ((1::real) - exp (- (1::real))) * indicat_real {Some x} (Some (u + t * v)))"
                                          "(\<lambda>v::nat. exp (- (1::real)) ^ v * ((1::real) - exp (- (1::real))))"],simp_all)
      qed
      have 3:"0< (1 - exp (- 1::real))"
        by simp
      show ?thesis using 1 2 3 by simp
    qed
  qed
  also have "... =  (\<Sum>u = 0..t - 1. (exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1))) *
        (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (if (u+t * v = x) then 1 else 0)))" 
  proof -
    fix v::nat
    have "\<And>u. indicat_real {Some x} (Some (u + t * v)) = (if (u+t * v = x) then 1 else 0)"
      by simp
    then have "\<And>u. (exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))
             = (exp (- 1) ^ v * (1 - exp (- 1))) * (if (u+t * v = x) then 1 else 0)"
      by simp
    then have 1:"\<And>u. (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))) 
             = (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (if (u+t * v = x) then 1 else 0))"
    proof -
      fix u
      show "(\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))) 
             = (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (if (u+t * v = x) then 1 else 0))"
        by(rewrite suminf_cong,simp_all)
    qed
    then have "\<And>u. (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (indicat_real {Some x} (Some (u + t * v)))) 
             = (\<Sum>v.(exp (- 1) ^ v * (1 - exp (- 1))) * (if (u+t * v = x) then 1 else 0))"
      by simp
    then show ?thesis
      by simp
  qed
  also have "... = exp(- real_of_nat(x mod t)/t) * (1-exp (- (1::real)/t)) / (1 - exp (- 1)) * exp(-(1::real))^((x-x mod t) div t) * (1 - exp (- 1))"
  proof -
    have 1:"\<And>u v::nat. u\<in>{0..t-1} \<Longrightarrow> u + t * v = x \<Longrightarrow> u = x mod t"
      using assms less_imp_diff_less by auto
    have 2:"(\<Sum>u = 0..t - 1. exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))
        = (\<Sum>u \<in> {0..t - 1}-{x mod t}. exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))
         + (\<Sum>u \<in> {x mod t}. exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))"
    proof(rewrite sum.Int_Diff[of"{0..t-1}" "_" "{x mod t}"],simp)
      have "{0..t - 1} \<inter> {x mod t} = {x mod t}"
      proof -
        have 1:"0 \<le> x mod  t" by simp
        have 2:"x mod t \<le> t-1" 
        proof -
          have "(t-1) + 1 = t" 
            using assms by(rule le_add_diff_inverse2)
          then show ?thesis 
            using mod_Suc_le_divisor[of "x" "t-1"] by simp
        qed
        show ?thesis using 1 2 by auto
      qed
      then show "(\<Sum>u\<in>{0..t - 1} \<inter> {x mod t}.
       exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
       (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0))) +
    (\<Sum>u\<in>{0..t - 1} - {x mod t}.
       exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
       (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0))) =
    (\<Sum>u\<in>{0..t - 1} - {x mod t}.
       exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) *
       (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0))) +
    (\<Sum>u\<in>{x mod t}.
       exp (real_of_int (- int u) / real t) * (1 - exp (- 1 / real t)) / (1 - exp (- 1)) * (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))"
        by simp
    qed
    have 3:"(\<Sum>u \<in> {0..t - 1}-{x mod t}. exp (-u/t) * (1 - exp (- 1/t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0))) = 0"
    proof -
      have "\<And>u. u \<in> {0..t - 1}-{x mod t} \<Longrightarrow>  exp (-u/t) * (1 - exp (- 1/t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)) = 0"
      proof (simp)
        fix u::nat
        assume u:"u \<le> t - Suc 0 \<and> u \<noteq> x mod t " 
        show "t = 0 \<or> (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)) = 0"
          using assms
        proof(simp)
          show "(\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)) = 0"
          proof -
            have "\<And>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0) = 0"
            proof - 
              have "\<And>v::nat. u + t * v \<noteq> x "
                using u assms by force
              then show "\<And>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0) = 0"
                by simp
            qed
            then have "(\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)) = (\<Sum>v. 0)"
              by meson
            also have "... = 0"
              by simp
            finally show ?thesis by simp
          qed
        qed
      qed
      then have "(\<Sum>u \<in> {0..t - 1}-{x mod t}. exp (-u/t) * (1 - exp (- 1/t)) / (1 - exp (- 1)) *
         (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0))) = (\<Sum>u \<in> {0..t - 1}-{x mod t}. 0)"
        by (rewrite Finite_Cartesian_Product.sum_cong_aux[of "{0..t-1}-{x mod t}" "_" "\<lambda>v. 0"],simp_all)
      also have "... = 0"
        by simp
      finally show ?thesis by simp
    qed
    have 4:"(\<Sum>u::nat\<in>{x mod t}. exp (real_of_int (- int u) / real t) * (1-exp (-(1::real)/t)) / (1 - exp (- 1)) * (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))
           = exp(- real_of_nat(x mod t)/t) * (1-exp (- (1::real)/t)) / (1 - exp (- 1)) * exp(-(1::real))^((x-x mod t) div t) * (1 - exp (- 1)) "
    proof -
      have p1:"(\<Sum>u::nat\<in>{x mod t}. exp (real_of_int (- int u) / real t) * (1-exp (-(1::real)/t)) / (1 - exp (- 1)) * (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if u + t * v = x then 1 else 0)))
          = exp (-real_of_nat (x mod t)/t) * (1-exp (-(1::real)/t)) / (1 - exp (- 1)) * (\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if x mod t + t * v = x then 1 else 0))"
        by simp
      have p2:"(\<Sum>v. exp (- 1) ^ v * (1 - exp (- 1)) * (if x mod t + t * v = x then 1 else 0)) = exp(-(1::real))^((x-x mod t) div t) * (1 - exp (- 1))"
      proof - 
        have "(\<Sum>v. exp (- 1::real) ^ v * (1 - exp (- 1)) * (if x mod t + t * v = x then 1 else 0)) = (\<Sum>v\<in>{(x-x mod t) div t}. exp (- 1) ^ v * (1 - exp (- 1)) * (if x mod t + t * v = x then 1 else 0))"
        proof (rule suminf_finite,simp_all)
        fix v
        show"v \<noteq> (x-x mod t) div t \<Longrightarrow> x mod t + t * v \<noteq> x"
          by (metis add.commute add_diff_cancel_right' assms le_antisym less_eq_nat.simps(1) nonzero_mult_div_cancel_left zero_neq_one)
        qed
        also have "... = exp (- 1) ^ ((x-x mod t) div t) * (1 - exp (- 1)) * (if x mod t + t * ((x-x mod t) div t) = x then 1 else 0)"
          by simp
        also have "... = exp (- 1) ^ ((x-x mod t) div t) * (1 - exp (- 1))"
          by simp
        finally show ?thesis by simp
      qed
      show ?thesis using p1 p2 by simp
    qed
    show ?thesis
      using 2 3 4 
      by simp
  qed
  also have "... = (1-exp(-1/t)) * exp(-x/t)"
  proof - 
    have "exp (- (x mod t)/t) * (1 - exp (- 1/t)) / (1 - exp (- 1)) * exp (- 1) ^ ((x - x mod t) div t) * (1 - exp (- 1))
        = exp (- (x mod t)/t) * (1 - exp (- 1/t)) * exp (- 1) ^ ((x - x mod t) div t)"
      by simp
    also have "... = exp (- (x mod t)/t) * (1 - exp (- 1/t)) * exp (-((x - x mod t) div t))"
      using assms apply(simp)
      by (metis exp_of_nat_mult mult_minus1_right)
    also have "... =  (1 - exp (- 1/t)) * exp(-x/t)"
      using assms 
    proof(simp)
      show "exp (- ((x mod t)/t)) * exp (- real ((x - x mod t) div t)) = exp (- (x/t)) "
      proof-
        have "exp (- ((x mod t)/t)) * exp (- real ((x - x mod t) div t))  = exp (- ((x mod t)/t + (x - x mod t) div t)) "
          by (simp add: mult_exp_exp)
        also have "... =  exp (-(x/t))"
        proof -
          have p1:"(x mod t)+ (x - x mod t) = x"
            by simp
          then have p2:"(x mod t)/t + (x - x mod t)/t = x/t"
            by (metis add_divide_distrib of_nat_add)
          then have "(x mod t)/t + (x - x mod t) div t = x/t"
          proof -
            have "(x - x mod t)/t = (x - x mod t) div t"
              by (simp add: real_of_nat_div_aux)
            then show ?thesis 
              using p2 by simp
          qed
          then show ?thesis 
            by simp
        qed
        finally show ?thesis
          by simp
      qed
    qed
    finally have "exp (- (x mod t)/t) * (1 - exp (- 1/t)) / (1 - exp (- 1)) * exp (- 1) ^ ((x - x mod t) div t) * (1 - exp (- 1))
                = (1 - exp (- 1/t)) * exp(-x/t)"
      by simp
    then show ?thesis
      by simp
  qed
  finally have "ennreal (spmf (discrete_laplace_rat_unit t) x) = ennreal ((1 - exp (- 1 / real t))*exp(-x/t))"
    by simp
  then show ?thesis by simp
qed

lemma spmf_y_discrete_laplace_rat:
  assumes "1\<le>t" and "1\<le>s"
  shows "spmf (map_spmf (\<lambda>x. calculate_y x s) (discrete_laplace_rat_unit t)) y = (1-exp(-1/t)^s) * exp(-1/t) ^ (s*y)" 
proof -
  have "ennreal (spmf (map_spmf (\<lambda>x. calculate_y x s) (discrete_laplace_rat_unit t)) y) =(1-exp(-1/t)^s) * exp(-1/t) ^ (s*y)"
    apply(rewrite ennreal_spmf_map_conv_nn_integral, rewrite nn_integral_measure_spmf)
    apply(simp add: nn_integral_count_space_nat)
    using assms apply(simp add:calculate_y_def)
  proof -
    show "(\<Sum>x. ennreal ((1 - exp (-(1/t))) * exp (- (x/t))) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x)
        = ennreal ((1 - exp (- (1 / real t)) ^ s) * exp (- (1 / real t)) ^ (s * y))"
    proof -
      have 1:"{x. nat \<lfloor>real x/s\<rfloor> \<in> {y}} = {x. nat \<lfloor>real x /s\<rfloor> = y}"
        by simp
      then have 2:"\<And>x. indicator {x. nat \<lfloor>real x / real s\<rfloor> \<in> {y}} x =  indicator {x. nat \<lfloor>real x/s\<rfloor> =y} x"
        by simp
      have 3:"\<And>x. (s * y \<le> x \<and> x< s * (y+1)) = (nat\<lfloor>real x/s\<rfloor> =y)"
      proof 
        fix x::nat
        assume H:"s * y \<le> x \<and> x< s * (y+1)"
        show "nat \<lfloor>real x/s\<rfloor> =y"
          apply(rewrite floor_eq2[of "y"])
          apply(simp_all)
        proof -
          have "(s * y)/ s\<le> x/s"
            apply(rewrite divide_right_mono,simp_all)
            using H of_nat_mono by fastforce
          then show "y \<le> x/s"
            using assms by simp
          show "real x / real s < real y + 1 "
          proof-
            have "real x < s * (real y + 1)"
            proof-
              have "real y + 1 = y + 1"
                by simp
              then have "s * (real y + 1) = s * (y+1)"
                using of_nat_mult by metis
              then show ?thesis
                using H 
                by linarith
            qed
            then have "x/s < (s * (real y + 1))/s"
              apply(rewrite divide_strict_right_mono,simp_all)
              using assms by simp
            then show ?thesis 
              using assms by simp
          qed
        qed
      next
        fix x::nat
        assume H:"nat \<lfloor>real x / real s\<rfloor> = y"
        show "s * y \<le> x \<and> x < s * (y + 1)"
        proof
          have 1:"nat \<lfloor>real x / real s\<rfloor>  = x div s"
            using floor_divide_of_nat_eq 
            by (metis nat_int)
          show "s*y\<le>x"
            using 1 H assms 
            by simp
          show "x < s * (y + 1)"
            using 1 H assms 
            by (simp add: dividend_less_times_div)
        qed
      qed
      have 4:"\<And>x. (x\<in>{s*y..<s*(y+1)}) = (indicator {x. nat \<lfloor>real x / real s\<rfloor> \<in> {y}} x = 1)"
        using 2 3 by force
      have 5:"\<And>x. (x\<notin>{s*y..<s*(y+1)}) = (indicator {x. nat \<lfloor>real x / real s\<rfloor> \<in> {y}} x = 0)"
        using 2 3 by force
      have 6:"\<And>x. x\<in>{s*y..<s*(y+1)} \<Longrightarrow> (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * indicator {x. nat \<lfloor>real x / real s\<rfloor> \<in> {y}} x = (1 - exp (-(1/t))) * exp (- (x/t))"
        using 4 by auto
      have 7:"\<And>x. x\<notin>{s*y..<s*(y+1)} \<Longrightarrow> (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * indicator {x. nat \<lfloor>real x / real s\<rfloor> \<in> {y}} x = 0"
        using 5 by auto
      have "(\<Sum>x. ennreal ((1 - exp (-(1/t))) * exp (- (x/t))) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x)
          = (\<Sum>x. ennreal ((1 - exp (-(1/t))) * exp (- (x/t))) * ennreal (indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x))"
        by(simp add: ennreal_indicator)
      also have "... = (\<Sum>x. ennreal ((1 - exp (-(1/t))) * exp (- (x/t)) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x))"
        by(simp add: ennreal_mult')
      also have "... = ennreal (\<Sum>x. (1 - exp (-(1/t))) * exp (- (x/t)) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x)"
      proof(rewrite suminf_ennreal,simp_all,rewrite ennreal_suminf_neq_top,simp_all)
        have 1:"\<And>x. (\<lambda>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) x)x
                   \<le> (\<lambda>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t))) x"
          using assms by simp
        have 2:"summable (\<lambda>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t))) "
          apply(rewrite summable_mult, simp_all)
          using assms summable_exp_rat by simp
        show "summable (\<lambda>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) x)"
        proof(rewrite summable_comparison_test[of "_" "(\<lambda>x. exp (- (real x / real t)))"],simp_all)
          show "summable (\<lambda>x. exp (- (real x / real t)))"
            using assms summable_exp_rat by simp
          show "\<exists>N. \<forall>n\<ge>N. (1 - exp (- (1 / real t))) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) n \<le> 1 "
          proof -
            have "\<And>n::nat. (1 - exp (- (1 / real t))) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) n \<le> 1 "
            proof -
              fix n
              have 1:"(1 - exp (- (1 / real t))) \<le> 1"
                by simp
              have 2:"indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) n \<le> 1"
                by simp
              show "(1 - exp (- (1 / real t))) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) n \<le> 1"
                using 1 2
                ereal_mult_mono[of "1" "indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) n" "(1 - exp (- (1 / real t)))" "1"]
                by simp
            qed
            then show ?thesis by simp
          qed
        qed
      qed
      also have "... = ennreal (\<Sum>x\<in>{s*y..<s*(y+1)} . (1 - exp (-(1/t))) * exp (- (x/t)))"
      proof -
        have "(\<Sum>x. (1 - exp (-(1/t))) * exp (- (x/t)) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x) 
            = (\<Sum>x\<in>{s*y..<s*(y+1)}. (1 - exp (-(1/t))) * exp (- (x/t)) * indicator ((\<lambda>x. nat \<lfloor>x/s\<rfloor>) -` {y}) x)"
        proof(rule suminf_finite,simp_all)
          fix x::nat
          assume H:"s * y \<le> x \<longrightarrow> \<not> x < s + s * y"
          show "t = 0 \<or> indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) x = 0"
            using assms
          proof (simp)
            show "indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) x = 0"
              unfolding vimage_def using H 5 by auto
          qed
        qed
        also have "... = (\<Sum>x = s * y..<s * (y + 1). (1 - exp (- (1 / real t))) * exp (- (real x / real t)))"
          unfolding vimage_def using 6
          by(rule Finite_Cartesian_Product.sum_cong_aux,auto)
        finally have "(\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * indicat_real ((\<lambda>x. nat \<lfloor>real x / real s\<rfloor>) -` {y}) x)
                    = (\<Sum>x = s * y..<s * (y + 1). (1 - exp (- (1 / real t))) * exp (- (real x / real t))) "
          by simp
        then show ?thesis by simp
      qed
      also have "... = (1-exp(-1/t)^s) * exp(-1/t) ^ (s*y)"
      proof -
        have "(\<Sum>x = s * y..<s * (y + 1). (1 - exp (- (1 / real t))) * exp (- (real x / real t)))
            = (1-exp(-1/t)^s) * exp(-1/t) ^ (s*y) "
        proof -
          have "(\<Sum>x = s * y..<s * (y + 1). (1 - exp (- (1 / real t))) * exp (- (real x / real t)))
              = (1 - exp (- (1 / real t))) * (\<Sum>x = s * y..<s * (y + 1).  exp (- (real x / real t)))"
            by(rewrite sum_distrib_left, simp)
          also have "... = (1 - exp (- (1 / real t))) * (exp(-(s*y)/t)-exp(-(s*(y+1))/t))/(1-exp(-1/t))"
          proof -
            have " (\<Sum>x = s * y..<s * (y + 1).  exp (- (x/t))) = (\<Sum>x = s * y..s * (y + 1)-1.  exp (- (x/t)))"
            proof -
              have "{s*y..<s* (y+1)} = {s*y..s*(y+1)-1}"
                using assms by auto
              then show ?thesis 
                by auto
            qed
            also have "... = (\<Sum>x = s * y..s * (y + 1) - 1. exp (- x/t))"
              by simp
            also have "... = (exp(-(s*y)/t)-exp(-(s*(y+1))/t))/(1-exp(-1/t))"
              apply(rewrite exp_sum_general[of "t" "s*y" "s*(y+1)-1"])
              using assms by(simp_all)
            finally have "(\<Sum>x = s * y..<s * (y + 1). exp (- (real x / real t)))
                        = (exp(-(s*y)/t)-exp(-(s*(y+1))/t))/(1-exp(-1/t))"
              by simp
            then show ?thesis by simp
          qed
          also have "... = (exp(-(s*y)/t)-exp(-(s*(y+1))/t))" 
            by simp
          also have "... = (1 - exp(-s/t)) *  exp(-(s*y)/t)"
          proof -
            have "exp(-(s*y)/t)-exp(-(s*(y+1))/t) = 1*exp(-(s*y)/t) - exp(-s/t)*exp(-(s*y)/t)"
              apply(simp)
              using exp_add[of "- (real s*y/t)" "-(s/t)"]
              by argo
            also have "... = exp(-(s*y)/t) * (1- exp(-s/t))"
              by argo
            finally show "exp(-(s*y)/t)-exp(-(s*(y+1))/t) = (1 - exp(-s/t)) *  exp(-(s*y)/t)"
              by simp
          qed
          also have "... = (1-exp(-1/t)^s) * exp(-1/t) ^ (s*y)"
          proof -
            have "exp(-(s*y)/t) = exp ((s*y)*(-1/t))"
              by simp
            also have "... = exp(-1/t) ^ (s*y)"
              using exp_of_nat_mult[of "s*y" "-1/t"]
              by simp
            finally have 1:"exp(-(s*y)/t) = exp(-1/t) ^ (s*y)"
              by simp
            have "1 - exp(-s/t) = 1-exp(s*(-1/t))"
              by simp
            also have "... =(1-exp(-1/t)^s)"
              using exp_of_nat_mult[of "s" "-1/t"]
              by simp
            finally have 2:"1 - exp(-s/t) = (1-exp(-1/t)^s)"
              by simp
            show ?thesis 
              using 1 2 by simp
          qed
          finally show ?thesis by simp
        qed
        then show ?thesis by simp
      qed
      finally show ?thesis by simp
    qed
  qed
  then show ?thesis 
    by (simp add: power_le_one)
qed


context
  fixes body :: "bool \<times> nat \<times> nat \<times> int \<Rightarrow> (bool \<times> nat \<times> nat \<times> int) spmf"
  defines [simp]: "body \<equiv> (\<lambda>(b, t, s, z). 
                            fast_uniform (t::nat) \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t))  \<bind>
                            (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                                 else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s,- y) else return_spmf (False, t, s,y))))))"

begin
interpretation loop_spmf "fst" body 
  rewrites  "body \<equiv> (\<lambda>(b, t, s, z). 
                            fast_uniform (t::nat) \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t))  \<bind>
                            (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                                 else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s,- y) else return_spmf (False, t, s,y))))))"
  by(fact body_def)


lemma discrete_laplace_rat_cov_while:
"discrete_laplace_rat t s = map_spmf (\<lambda>a. snd (snd (snd a))) (while (True, t, s, 0))" (is "?lhs = ?rhs")
proof (rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof (induction rule: discrete_laplace_rat_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step discrete_laplace_rat)
    show ?case 
      apply(rewrite while.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step apply(simp)
    proof (clarify)
      fix x::nat 
      have " (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while)) 
            = (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))) "
        by metis
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                                                   else if b then return_spmf (False, t, s, - y) 
                                                   else return_spmf (False, t, s, y))
                                              \<bind>  (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))))) "
        by simp
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (True, t, s, 0)
                                                   else if b then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, - y) 
                                                   else (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, y))
                                              )))) "
        by(rewrite if_else_return_bind_spmf_2, simp)
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              )))) "
      proof -
        have 1:"\<forall>y. (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, y) = return_spmf y"
          by(rewrite o_apply, simp add:while.simps)
        have 2:"(map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (True, t, s, 0) = map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))"
          by simp
        show ?thesis 
          using 1 2 by presburger
      qed
      finally have 1:"(loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while)) 
                  = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              )))) "
        by simp
      have 2:"ord_spmf (=)
                    (loop 0 \<bind>
                      (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
                       in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))
                    (loop 0 \<bind>
                      (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
                       in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              ))))"
      proof (rule ord_spmf_bind, simp, clarify)
        fix v
        show " ord_spmf (=)
          (let y = \<lfloor>(real x + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))
          (let y = \<lfloor>(real x + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a)))(local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))"
        proof -
          have "\<forall>y. ord_spmf (=)
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a)))(local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))"
          proof (clarify, rule ord_spmf_bind,simp,clarify)
            fix y b
            show "ord_spmf (=) (if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)
                               (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y)"
              using step by simp
          qed
          then show ?thesis by meson
        qed
      qed
      show " ord_spmf (=)
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>ba. if \<not> ba \<and> y = 0 then discrete_laplace_rat t s else if ba then return_spmf (- y) else return_spmf y)))
        (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(real x + real t * real y) / real s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))"
        using 1 2 by simp
    qed
  qed
next  
  have "ord_spmf (=) ?rhs ?lhs"
  and "\<And>x. ord_spmf (=) (map_spmf (\<lambda>a. snd (snd (snd a))) (while (False, t,s, x))) (return_spmf x)"
  proof (induction rule: while_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case by simp
  next
    case (step while')
    case 1 show ?case 
      apply(rewrite discrete_laplace_rat.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step apply(simp)
    proof 
      fix u  
      show "ord_spmf (=)
        (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(u+t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while'))
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(u+t*real v)/s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))"
      proof (rule ord_spmf_bind, simp, clarify)
        fix v
      have "\<forall>y. ord_spmf (=)
        (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
         map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
        (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
      proof 
        fix y
        have 1:"ord_spmf (=)
              (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
              (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) 
                                            else if b then return_spmf (- y) else return_spmf y))"
        proof -
          have "bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
                map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while' 
              = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (True, t, s, 0)
                                                   else if b then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (False, t, s, - y) 
                                                   else (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (False, t, s, y)))"
            by(simp add: if_else_return_bind_spmf_2)
          also have "... 
               = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                   else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                   else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y))))"
            by(rewrite o_apply, rewrite o_apply,rewrite o_apply,simp)
          finally have 1:"bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
                map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while' 
                      = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                          else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                          else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y))))"
            by simp
          have 2:"ord_spmf (=) (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                                else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                                else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y)))))
                             (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) 
                                                           else if b then return_spmf (- y) else return_spmf y))"
          proof (rule ord_spmf_bind, simp ,clarify)
            fix b
            show "ord_spmf (=)
          (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
           else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, - y)) else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y)))
          (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y)"
              using step.IH(2)[of"y"] step.IH(2)[of"-y"] by simp
          qed
          show ?thesis 
            using 1 2 by simp
        qed
        have 2:"ord_spmf (=) (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))
                             (bernoulli_rat (Suc 0) 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
          by(rule ord_spmf_bind,simp,simp add:step.IH(1))
        show "ord_spmf (=)
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
          using 1 2 spmf.leq_trans by blast
      qed
      then show "ord_spmf (=)
          ((let y = \<lfloor>(u + real t * real v) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
          (let y = \<lfloor>(u + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
        by meson
      qed
    qed
    case 2 show ?case by simp
  qed
  then show "ord_spmf (=) ?rhs ?lhs" by simp
qed

lemma map_spmf_lambda_if:
"map_spmf f \<circ> (\<lambda>d. if b then spmf_1 else spmf2) = (\<lambda>d. if b then map_spmf f spmf_1 else map_spmf f spmf2)"
  by auto

lemma map_spmf_return_spmf:
"map_spmf f (return_spmf p) = return_spmf (f p)"
  by simp

lemma map_spmf_let:
"map_spmf f \<circ> (\<lambda>v. let x = t;y= g x in h x) = (\<lambda>v. let x = t;y= g x in map_spmf f (h x)) "
  by simp

lemma discrete_laplace_rat_body_map_spmf_fst:
"map_spmf fst
                    (fast_uniform t \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) 
                  = fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))"
proof -
  have "map_spmf fst
                    (fast_uniform t \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) 
          = 
     fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Rat.Fract (int u) (int t)) \<bind>
          map_spmf fst \<circ>  (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                else loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))"   
        by (simp add: map_spmf_bind_spmf map_spmf_bind_spmf_lambda)
      also have "... = 
      fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))"  
      proof (rule bind_spmf_cong,simp,rule bind_spmf_cong,simp_all,clarify)
        fix x xa
        show "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))) =
       loop 0 \<bind> (\<lambda>v. bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> \<lfloor>(real x + real t * real v) / real s\<rfloor> = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
        proof -
          have "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))) =
        (loop 0 \<bind>
          map_spmf fst \<circ>  (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
            by (simp add: map_spmf_bind_spmf)
          also have "...
                   = (loop 0 \<bind>
           (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))"
          proof (rule bind_spmf_cong,simp_all)
            fix xa
            show "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
          bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> \<lfloor>(real x + real t * real xa) / real s\<rfloor> = 0 then return_spmf True else if b then return_spmf False else return_spmf False)"
            proof - 
              have "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in map_spmf fst (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
                by metis
              also have "... = (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
              proof -
                have 1:"\<And>y. map_spmf fst (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))
                         =  bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)"
                  by(simp add:map_spmf_bind_spmf, rule bind_spmf_cong, simp_all)
                show ?thesis by(simp add:1)
              qed
              finally have "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
                by simp
              then show ?thesis by simp
            qed
          qed
          finally have "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))
      = (loop 0 \<bind>
           (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))"
            by simp 
          then show ?thesis by simp
        qed
      qed
      ...      finally show ?thesis
        by simp
    qed 



(*declare[[show_types,show_sorts]]*)
lemma lossless_discrete_laplace_rat:
  assumes "1\<le>s" and "1\<le>t"
  shows "lossless_spmf (discrete_laplace_rat t s)"
proof- 
  have "lossless_spmf (while (True,t,s,0))"
  proof (rule termination_0_1_immediate_invar,clarify)
    fix b::bool and t1 s1::nat and z::int
    assume "fst (b,t1,s1,z)"
    and I:"(\<lambda>(b,t1,s1,z). t1=t \<and> s1=s) (b,t1,s1,z)"
    show "1/t * (1 - exp (- 1)) *  (inverse (2::nat)) \<le> spmf (map_spmf fst
                    (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y)))))))
              False"
    proof -
      have "ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False) =
            ennreal (spmf (fast_uniform t1 \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))) False)"
        by(simp add: discrete_laplace_rat_body_map_spmf_fst)
      also have "... = (\<Sum>u::nat. ennreal (spmf (fast_uniform t1) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t1)) True) *
        (\<Sum>\<^sup>+ v. ennreal (exp (-1)^v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
        apply(simp add:ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_finite UNIV_bool)
        using nn_integral_count_space_nat by blast
      also have "... = (\<Sum>u\<in>{0::nat..t1-1}. ennreal (spmf (fast_uniform t1) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t1)) True) *
        (\<Sum>\<^sup>+ v. ennreal (exp (-1)^v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
      proof (rule suminf_finite)
        show "finite {0::nat..t1-1}" by simp
        fix u 
        assume u:"u \<notin> {0..t1 - 1}"
        show "ennreal (spmf (fast_uniform t1) u) *
         (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int u) (int t1))) True) *
          (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2)))=0"
        proof -
          have "spmf (fast_uniform t1) u = 0"
            using u spmf_fast_uniform by simp 
          then show ?thesis by simp
        qed
      qed
      also have "... \<ge> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
      proof -
        have 1:"\<forall>u\<in>{0::nat..t1-1}. 0 \<le> (Fract u t1)" using I assms
          by (simp add: zero_le_Fract_iff)
        have 2:"\<forall>u\<in>{0::nat..t1-1}. u < t1" 
          using I assms by auto
        show ?thesis using 1 2 spmf_fast_uniform  
          by(simp)
      qed
      finally have 1:"
        ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)
  \<ge> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
        by simp
      have 2:"(\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))))
      \<le>  (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse (2::nat) * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse (2::nat)))))"
      proof (rule ordered_comm_monoid_add_class.sum_mono)
        fix u
        have 1:"(\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (inverse (real 2))) \<le> 
               (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
               (ennreal (inverse (real 2)) * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + ennreal (inverse (real 2))))"
        proof (rewrite nn_integral_mono,simp_all,clarify)
          fix x
          show "ennreal (exp (- 1) ^ x * (1 - exp (- 1))) * (inverse 2::ennreal) \<le> ennreal (exp (- 1) ^ x * (1 - exp (- 1))) * ((inverse 2 + inverse 2)::ennreal)"
          proof -
            have "(inverse 2::ennreal) \<le> (inverse 2 + inverse 2)"
              by simp
            then show ?thesis 
              by (simp add: distrib_left)
          qed
        qed
        have 2:"ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1))))) \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))))"
          by simp
        then show "ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (inverse (real 2))))
         \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) *
             (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
                (ennreal (inverse (real 2)) * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + ennreal (inverse (real 2)))))"
          using 1 2 
          by (metis (no_types, lifting) ennreal_eq_0_iff ennreal_mult_cancel_left ennreal_mult_le_mult_iff not_exp_le_zero top_neq_ennreal)
      qed
      have 3:"(\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat))))) \<le> 
         ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)"
        using 1 2 by simp
      have 4:" (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (ennreal (1 - exp (- 1)) *  (inverse (2::nat))))) \<le>
      (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat))))) "
      proof -
        have "ennreal (1 - exp (- 1)) *  (inverse (2::nat)) = (\<Sum> v\<in>{0::nat}. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by simp
        also have "...\<le> (\<Sum> v::nat. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by(rule sum_le_suminf,simp_all)
        also have "... = (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))" 
          using nn_integral_count_space_nat by simp
        finally have 1:"ennreal (1 - exp (- 1)) *  (inverse (2::nat)) \<le> (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by simp
        show ?thesis 
        proof (rewrite sum_mono,simp_all)
          fix u 
          show "ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (ennreal (1 - exp (- 1)) * inverse 2))
         \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * inverse 2))"
          proof(rule mult_mono,simp_all,rule mult_mono,simp_all)
            show "ennreal (1 - exp (- 1)) * inverse 2 \<le> (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * inverse 2)"
            proof -
              have "ennreal (1 - exp (- 1)) *  (inverse 2) = (\<Sum> v\<in>{0::nat}. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
                by simp
              also have "...\<le> (\<Sum> v::nat. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
                by(rule sum_le_suminf,simp_all)
              also have "... = (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse 2))" 
                using nn_integral_count_space_nat by simp
              finally show ?thesis by simp
            qed
          qed
        qed
      qed
      have 5:"ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat))) \<le>
       (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (ennreal (1 - exp (- 1)) *  (inverse (2::nat)))))"
      proof -
        have "(ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat)))) = (ennreal (1/t1 * (1 - exp (- 1)) *  (inverse (2::nat))))"
          using I by simp
        also have "... = (ennreal (1/t1) * (ennreal 1 * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
        proof(rewrite ennreal_mult,simp_all)
          have " ennreal ((1 - exp (- 1)) / real t1) * inverse 2 =  ennreal (1/ t1) * ennreal (1 - exp (- 1)) * inverse 2"
            by(simp add: divide_inverse ennreal_mult' mult.commute)
          also have "... = (ennreal (1/t1) * (ennreal 1 * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
            by (simp add: mult.assoc)
          finally show "ennreal ((1 - exp (- 1)) / real t1) * inverse 2 = ennreal (1 / real t1) * (ennreal (1 - exp (- 1)) * inverse 2)"
            by simp
        qed
        also have "... = (ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract 0 t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2)))) "
        proof- 
          have "Fract 0 t1 = 0" by(rule rat_number_collapse)
          then show ?thesis by simp
        qed
        also have "... \<le> 
              (\<Sum>u\<in>{0::nat}. ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract u t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
          by simp
        also have "... \<le> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract u t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
          by(rule sum_mono2, simp_all)
        finally show ?thesis by simp
      qed
      have "ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat)))\<le>
             ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)"
        using 3 4 5 by order
      then show ?thesis by simp
    qed
  next
    show "0< 1/t * (1 - exp (- 1)) *  (inverse (2::nat))"
    proof -
      have 1:"0 < 1/t" using assms by auto
      have "exp(-1::real)< 1" 
        by(rewrite exp_less_one_iff,simp)
      then have 2:"0 < 1-exp(-1::real)" by simp
      have 3:"0<inverse (2::nat)" by simp
      show ?thesis using 1 2 3 by auto
    qed
  next
    show "case (True, t, s, 0) of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s" by simp
  next
    show "\<And>sa. fst sa \<Longrightarrow>
          (case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow>
          lossless_spmf
           (case sa of
            (b, t, s, z) \<Rightarrow>
              fast_uniform t \<bind>
              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                   (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                        else loop 0 \<bind>
                             (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                  in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
    proof(clarify,auto)
      show "0<t" using assms by simp
    next
      fix x::nat
      assume A1:"x \<in> set_spmf (fast_uniform t)"
      show "lossless_spmf (bernoulli_exp_minus_rat (Fract (int x) (int t)))"
      proof-
        have "0\<le> Fract (int x) (int t)"
          using assms(2) zero_le_Fract_iff by auto 
        then show ?thesis by(rule lossless_bernoulli_exp_minus_rat)
      qed
    next
      fix a x xa xb
      show "lossless_spmf
        (let y = \<lfloor>(x + real t * xb) / real s\<rfloor>
         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
      proof -
        have 1:"\<And>y. lossless_spmf (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
          by simp
        show ?thesis 
          by (metis (no_types) "1")
      qed
    qed
  next
    show "\<And>sa s'.
       s' \<in> set_spmf
              (case sa of
               (b, t, s, z) \<Rightarrow>
                 fast_uniform t \<bind>
                 (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                      (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                           else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                     in bernoulli_rat 1 2 \<bind>
                                        (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) \<Longrightarrow>
       (case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow> fst sa \<Longrightarrow> (case s' of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s)"
    proof (clarify)
      fix b1 t1 s1 z1 b2 t2 s2 z2
      assume H:"(b2,t2,s2,z2)\<in> set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
      then show "t2 = t \<and> s2 = s"
      proof -
        have "set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))
            = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (set_spmf \<circ> (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          by (simp add: set_bind_spmf o_def)
        also have "... = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          by(rewrite set_spmf_if,simp)
        also have "... = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (set_spmf \<circ> (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          using set_bind_spmf 
          by metis
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))))"
        proof -
          have "\<And>u. set_spmf \<circ> (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))
                  =  (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
            by (metis set_spmf_if)
          then show ?thesis by auto
        qed
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  set_spmf \<circ> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
        proof - 
          have "\<And>u. (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))
                  =  (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind> set_spmf \<circ> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
            by (meson set_bind_spmf)
          then show ?thesis by auto
        qed
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then set_spmf (return_spmf (True, t, s, 0)) else set_spmf (if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))))"
          by(rewrite set_spmf_if,simp)
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then set_spmf (return_spmf (True, t, s, 0)) else if b then set_spmf(return_spmf (False, t, s, - y)) else set_spmf (return_spmf (False, t, s, y)))))))"
          by(rewrite if_distrib,simp)
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then {(True, t, s, 0)}
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})))))"
          by(rewrite set_return_spmf, rewrite set_return_spmf, rewrite set_return_spmf, rewrite set_return_spmf, simp)
        also have "... \<subseteq> {(True,t,s,0)} \<union> {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"  
        proof (rewrite set_spmf_bind_set,simp_all)
          fix u
          show "set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
         (\<lambda>d. if \<not> d then {(True, t, s, 0)}
              else set_spmf (loop 0) \<bind>
                   (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                        in set_spmf (bernoulli_rat 1 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"
          proof (rewrite set_spmf_bind_set,simp_all,rule)
            fix d
            show "set_spmf (loop 0) \<bind>
         (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
              in set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)}))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
            proof(rewrite set_spmf_bind_set,simp_all)
              fix v::nat 
              have 1:"\<And>y::int. set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"
                unfolding Ints_def
                by(rewrite set_spmf_bind_set,auto)
              show "(let y = \<lfloor>(real u + real t * real v) / real s\<rfloor> in set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)}))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
                using 1 by meson
            qed
          qed
        qed
        finally have "set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))
            \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
          by simp
        then show ?thesis using H by auto
      qed
    qed
  qed
  then show ?thesis by (simp add:discrete_laplace_rat_cov_while)
qed
               
end





lemma spmf_discrete_laplace_rat[simp]:
  assumes "1\<le>s" and "1\<le>t"
  shows "spmf (discrete_laplace_rat t s) z = (exp(t/s)-1)/(exp(t/s)+1) * exp (- abs z * t/s)"
proof (rule spmf_ub_tight)
  fix x
  show "spmf (discrete_laplace_rat t s) x \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
  proof (induction rule: discrete_laplace_rat_fixp_induct)
    case adm
    then show ?case 
    proof (simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf,clarify)
      fix A
      assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
        H: "\<forall>xa\<in>A. spmf (xa (t, s)) x \<le> (exp (t/s)-1) * exp (- (\<bar>real_of_int x\<bar> * t/s)) / (exp (t/s)+1)"
      have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f (t, s)}) x =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f (t, s)}. spmf p x)"
      proof (rule spmf_lub_spmf)
        show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f (t, s)}" 
          by (simp add: CA chain_fun)
      next
        show "{y. \<exists>f\<in>A. y = f (t, s)} \<noteq> {}" using A by blast
      qed
      also have "... \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
      proof (rule conditionally_complete_lattice_class.cSUP_least)
        show "{y. \<exists>f\<in>A. y = f (t, s)} \<noteq> {}" using A by auto 
        fix p
        assume "p\<in> {y. \<exists>f\<in>A. y = f (t, s)} "
        then show "spmf p x \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
          using H by auto
      qed
      finally show "spmf (lub_spmf {y. \<exists>f\<in>A. y = f (t, s)}) x \<le> (exp (t/s)-1) * exp (- (\<bar>real_of_int x\<bar>*t/s))/(exp (t/s)+1)"
        by simp
    qed         
  next
    case bottom
    then show ?case by simp
  next
    case (step discrete_laplace_rat)
    then show ?case
    proof -
      have "ennreal (spmf
     (fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                else loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>ba. if \<not> ba \<and> y = 0 then discrete_laplace_rat t s else if ba then return_spmf (- y) else return_spmf y)))))
      x)
    \<le> (exp (t/s)-1)/(exp (t/s)+1)*exp (- \<bar>real_of_int x\<bar> * t/s)"
      proof -
        have "ennreal (spmf (fast_uniform t \<bind>
                        (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                         (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                              else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                 in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))z) =
                  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
                          (\<Sum>\<^sup>+ d. ennreal (spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) d) *
                                  ennreal (spmf (if \<not> d then discrete_laplace_rat t s
                                                 else loop 0 \<bind>
                                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor> in
                                                     bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                else if b then return_spmf (- y) else return_spmf y)))z)))"
          by (simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        also have "... =  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
          by(simp add: nn_integral_count_space_finite UNIV_bool)
        also have "... = (\<Sum> u::nat. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
          using nn_integral_count_space_nat by blast
        also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
        proof (rule suminf_finite)
          show "finite {0::nat..t-1}" by simp
          show "\<And>u. u \<notin>  {0::nat..t-1} \<Longrightarrow> ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z))= 0"
          proof -
            fix u::nat
            assume u:"u \<notin> {0..t - 1}"
            then show "ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z))= 0"
            proof -
            have "spmf (fast_uniform t) u = 0"
              using u spmf_fast_uniform by simp 
            then show ?thesis by simp
          qed
        qed
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )" 
      proof -
        have 1:"\<forall>u\<in>{0::nat..t-1}. 0 \<le> (Fract u t)" using assms 
          by (simp add: zero_le_Fract_iff)
        have 2:"\<forall>u\<in>{0::nat..t-1}. u < t" 
          using assms(2) by auto
        show ?thesis using 1 2 spmf_fast_uniform by simp
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *
                                                       ennreal (spmf (let y = \<lfloor>(u+t*real v)/s\<rfloor> in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                            else if b then return_spmf (- y) 
                                                                                                                                 else return_spmf y))
              z))))" 
        by (simp add: ennreal_spmf_bind nn_integral_measure_spmf)
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                                       ennreal (spmf (bernoulli_rat 1 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                  else if b then return_spmf (- y) 
                                                                                                       else return_spmf y))z)))
      ))"
        by metis
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) * (let y = \<lfloor>(u+t*real v)/s\<rfloor> in 
                                             (inverse 2 * ennreal (spmf ((\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                          else if b then return_spmf (- y) 
                                                                                                               else return_spmf y) False) z) 
                                               +
                                              inverse 2 * ennreal (spmf ((\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                          else if b then return_spmf (- y) 
                                                                                                                  else return_spmf y) True) z)
                                             ))
     )))"
        by(simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_finite UNIV_bool) 
      also have  "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (inverse 2 * ennreal (spmf (if y = 0 then discrete_laplace_rat t s 
                                                                              else return_spmf y) z) 
                                               +
                                              inverse 2 * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
        by presburger
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal (spmf (if y = 0 then discrete_laplace_rat t s 
                                                                              else return_spmf y) z) 
                                               +
                                              1/(2::nat) * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
        using inverse_eq_divide[of "2"] by simp
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal ((if y = 0 then spmf (discrete_laplace_rat t s) z
                                                                     else spmf (return_spmf y) z)) 
                                               +
                                              1/(2::nat) * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
      proof-
        have "\<forall>y x. (spmf (if y = 0 then discrete_laplace_rat t s else return_spmf y) x) 
                   =(if y = 0 then spmf (discrete_laplace_rat t s) x else spmf (return_spmf y) x)"
          using if_distrib by simp
        then show ?thesis by simp
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal ((if y = 0 then spmf (discrete_laplace_rat t s) z
                                                                     else if y = z then 1 else 0)) 
                                               +
                                              1/(2::nat) * ennreal ( (if (- y)=z then 1 else 0))
                                             )))))"
      proof -
        have 1:"\<forall> x y. spmf (return_spmf y) x = (if y=x then 1 else 0)" by simp
        have 2:"\<forall> x y. spmf (return_spmf (uminus y)) x = (if (uminus y)=x then 1 else 0)" by simp
        show ?thesis by(rewrite 1,rewrite 2,simp) 
      qed
      finally have "ennreal (spmf (fast_uniform t \<bind>
                        (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                         (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                              else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                 in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))z) =
                   (\<Sum>u = 0..t - 1. ennreal (1/t)*
                   (ennreal (1 - exp (- real_of_rat (Fract u t))) * ennreal (spmf (discrete_laplace_rat t s) z) +
                    ennreal (exp (- real_of_rat (Fract u t))) *
                            (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
                                   (let y = \<lfloor>(u+t*real v)/s\<rfloor>
                                    in ennreal (1 / real 2) * ennreal (if y = 0 then spmf (discrete_laplace_rat t s) z else if y = z then 1 else 0) 
                                     + ennreal (1 / real 2) * ennreal (if - y = z then 1 else 0)))))"
        by simp

(*
      then show ?thesis by simp
    qed
  qed
  show "(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = ennreal (weight_spmf (discrete_laplace_rat t s))"
  proof - 
    have 1:"ennreal (weight_spmf (discrete_laplace_rat t s)) = 1"
      using lossless_discrete_laplace_rat lossless_spmf_def by auto
    have 2:"(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = 1" 
*)

end