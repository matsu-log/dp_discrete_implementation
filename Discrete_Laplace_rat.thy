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

lemma spmf_abs_summable:
"Infinite_Set_Sum.abs_summable_on (spmf p) A"
  apply(rule abs_summable_on_subset[OF _ subset_UNIV])
  apply(auto simp: abs_summable_on_def integrable_iff_bounded nn_integral_spmf)
  using measure_spmf.emeasure_finite ennreal_less_top_iff by auto

lemma summable_spmf:
  shows "summable (spmf p)"
proof -
  have "Infinite_Set_Sum.abs_summable_on (spmf p) UNIV"
    using spmf_abs_summable by auto
  then have 1:"summable (\<lambda>n. norm (spmf p n))"
    using abs_summable_on_nat_iff'[of"spmf p"] by simp
  have 2:"\<And>n. norm (spmf p n) = spmf p n"
  proof -
    fix n
    have "0\<le> spmf p n" 
      by simp
    then show "norm (spmf p n) = spmf p n"
      by simp
  qed
  show ?thesis using 1 2 by simp
qed

lemma finite_support_implies_zero:
  fixes f::"nat \<Rightarrow> real"
  assumes eq:"suminf f = sum f {0..n}"
and summable_f:"summable f"
and f:"\<And>x. 0\<le> f x"
shows "\<And>x. x\<notin>{0..n} \<Longrightarrow> f x = 0"
proof -
  fix x::nat
  assume x:"x\<notin>{0..n}"
  have 1:"sum f {0..<x+1} = sum f {0..n} + sum f {n+1..<x+1}"
  proof(rewrite sum.subset_diff[of "{0..n}" "{0..<x+1}"])
    show "{0..n} \<subseteq> {0..<x + 1}"
      using x by auto
    show "finite {0..<x+1}" by simp
    show "sum f ({0..<x + 1} - {0..n}) + sum f {0..n} = sum f {0..n} + sum f {n + 1..<x + 1} "
    proof -
      have "{0..<x + 1} - {0..n} = {n + 1..<x + 1}"
        using x by auto
      then show ?thesis by simp
    qed
  qed
  have 2:"sum f {0..<x+1} = sum f {0..n}"
  proof -
    have 1:"sum f {0..n} \<le> sum f {0..<x+1} "
      apply(rewrite sum_mono2)
      using f x by(simp_all,auto)
    have 2:"sum f {0..<x+1} \<le> sum f {0..n}"       
    proof(rewrite incseq_le[of "(\<lambda>n. sum f {0..<n})" "sum f {0..n}" "x+1"],simp_all)
      show "incseq (\<lambda>n. sum f {0..<n})"
      proof
        fix x y::nat
        assume xy:"x\<le>y"
        show "sum f {0..<x} \<le> sum f {0..<y}"
          apply(rewrite sum_mono2,simp_all)
          using xy f by(simp_all)
      qed
      show "(\<lambda>n. sum f {0..<n}) \<longlonglongrightarrow> sum f {0..n}"
      proof -      
        have 1:"(THE s. (\<lambda>n. sum f {..<n}) \<longlonglongrightarrow> s) = sum f {0..n}"
          using eq unfolding suminf_def sums_def by simp
        have "convergent (\<lambda>n. sum f {..<n})"
          using summable_f by (simp add: summable_iff_convergent)
        then have 2:"\<exists>L. (\<lambda>n. sum f {..<n}) \<longlonglongrightarrow> L"
          using convergentD
          by simp
        have "(\<lambda>n. sum f {..<n}) \<longlonglongrightarrow> sum f {0..n}"
          using 1 2 LIMSEQ_unique theI'
          by metis
      then show ?thesis
        by (simp add: lessThan_atLeast0)
    qed
  qed
    show ?thesis using 1 2 by simp
  qed
  have 3:"sum f {n+1..<x+1} = 0"
    using 1 2 by simp
  have "\<And>i. i\<in>{n+1..<x+1} \<Longrightarrow> f i = 0"
  proof -
    fix i
    assume i:"i\<in>{n+1..<x+1}"
    show "f i = 0"
      apply(rewrite sum_nonneg_0[of "{n+1..<x+1}" "f" "i"])
      using f i 3 by(simp_all)
  qed
  then show "f x =0"
    apply(rule)
    using x by(simp_all)
qed

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat_unit_loop1 :: "nat \<Rightarrow> nat spmf" where 
"discrete_laplace_rat_unit_loop1 t = do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract u t);
  if d then return_spmf u else discrete_laplace_rat_unit_loop1 t 
}"
end
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

lemma spmf_discrete_laplace_rat_unit_loop1_zero[simp]:
  fixes u::nat
  assumes "1\<le>t" and "t\<le>u"
  shows "spmf (discrete_laplace_rat_unit_loop1 t) u = 0"
proof -
  have "ennreal (\<Sum>u. spmf (discrete_laplace_rat_unit_loop1 t) u) = weight_spmf (discrete_laplace_rat_unit_loop1 t)"
    apply(rewrite weight_spmf_eq_nn_integral_spmf)
    apply(simp add: nn_integral_count_space_nat)
    apply(rewrite suminf_ennreal)
      apply(simp_all)
  proof - 
    show "(\<Sum>x. ennreal (spmf (discrete_laplace_rat_unit_loop1 t) x)) \<noteq> \<top>"
    proof-
      have "(\<Sum>u. ennreal (spmf (discrete_laplace_rat_unit_loop1 t) u)) = (\<Sum>\<^sup>+ x. ennreal (spmf (discrete_laplace_rat_unit_loop1 t) x))"
        by(simp add: nn_integral_count_space_nat)
      also have "... \<noteq> \<top>"
        by(simp add:nn_integral_spmf_neq_top)
      finally show ?thesis
        by simp
    qed
  qed
  also have "... = 1"
  proof -
    have "weight_spmf (discrete_laplace_rat_unit_loop1 t) = 1"
      using lossless_discrete_laplace_rat_unit_loop1 assms
      by (simp add: lossless_spmf_def)
    then show ?thesis by simp
  qed
  finally have "ennreal (\<Sum>u. spmf (discrete_laplace_rat_unit_loop1 t) u) = 1"
    by simp
  then have 1:"(\<Sum>u. spmf (discrete_laplace_rat_unit_loop1 t) u) = 1"
    by simp
  have 2:"(\<Sum>u\<in>{0..t-1}. spmf (discrete_laplace_rat_unit_loop1 t) u) = 1"
  proof -
    have "(\<Sum>u\<in>{0..t-1}. spmf (discrete_laplace_rat_unit_loop1 t) u) 
         =(\<Sum>u = 0..t-1. exp (- (u/t))*(1-exp(-(1/t)))/(1-exp(-1)))"
      using assms by(simp)
    also have "... = (\<Sum>u = 0..t-1. exp (- (u/t))) * (1-exp(-(1/t)))/(1-exp(-1))"
      using sum_distrib_right[of _ "{0..t-1}" "(1 - exp (- (1 / real t))) / (1 - exp (- 1))"]
      by simp
    also have "... = (1-exp(-1))/(1-exp(-1/t))* (1-exp(-(1/t)))/(1-exp(-1))"
      using exp_sum[of"t" "t-1"] assms
      by simp
    also have "... = 1"
      using assms(1) by auto
    finally show ?thesis by simp
  qed
  have p1:"(\<Sum>u. spmf (discrete_laplace_rat_unit_loop1 t) u) = (\<Sum>u\<in>{0..t-1}. spmf (discrete_laplace_rat_unit_loop1 t) u)"
    using 1 2 by simp
  have p2:"summable (spmf (discrete_laplace_rat_unit_loop1 t))"
    using summable_spmf by simp
  have p3:"\<And>u. 0\<le> spmf (discrete_laplace_rat_unit_loop1 t) u"
    by simp
  have "\<And>u. u\<notin>{0..t-1} \<Longrightarrow> spmf (discrete_laplace_rat_unit_loop1 t) u = 0"
    using p1 p2 p3 finite_support_implies_zero
    by blast
  then show ?thesis
    using assms by simp
qed




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

lemma lossless_discrete_laplace_rat_unit[simp]:
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
                            do {
    x::nat \<leftarrow> discrete_laplace_rat_unit t;
    b::bool \<leftarrow> bernoulli_rat 1 2;
    let y = calculate_y x s in
    if (\<not>b \<and> (y=0)) then return_spmf (True, t, s, 0)
    else if b then return_spmf (False, t, s, -y)
         else return_spmf (False, t, s, y)
})"

begin
interpretation loop_spmf "fst" body 
  rewrites  "body \<equiv> (\<lambda>(b, t, s, z). 
                            do {
    x::nat \<leftarrow> discrete_laplace_rat_unit t;
    b::bool \<leftarrow> bernoulli_rat 1 2;
    let y = calculate_y x s in
    if (\<not>b \<and> (y=0)) then return_spmf (True, t, s, 0)
    else if b then return_spmf (False, t, s, -y)
         else return_spmf (False, t, s, y)
})"
  by(fact body_def)


lemma discrete_laplace_rat_cov_while:
"discrete_laplace_rat t s = map_spmf (\<lambda>a. snd (snd (snd a))) (while (True, t, s, 0))" (is "?lhs = ?rhs")
proof (rule spmf.leq_antisym)
  have "ord_spmf (=) ?lhs ?rhs"
    and "\<And>x. ord_spmf (=) (return_spmf x) (map_spmf (\<lambda>a. snd (snd (snd a))) (while (False, t,s, x)))"
  proof (induction rule: discrete_laplace_rat_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case 
      using fst_conv map_spmf_return_spmf snd_conv snd_def spmf.leq_refl while_simps(2) by auto
  next
    case (step discrete_laplace_rat)
    case 1 show ?case using step.IH
      apply(rewrite while.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_lambda)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_lambda map_spmf_bind_spmf)
      apply(clarsimp simp add: Let_def)
      by(clarsimp intro!: ord_spmf_bind_reflI)
    case 2 show ?case using step.IH(2) by simp
  qed
  then show "ord_spmf (=) ?lhs ?rhs" by -
next  
  have "ord_spmf (=) ?rhs ?lhs"
  and "\<And>x. ord_spmf (=) (map_spmf (\<lambda>a. snd (snd (snd a))) (while (False, t,s, x))) (return_spmf x)"
  proof (induction rule: while_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case by simp
  next
    case (step while')
    case 1 show ?case using step.IH 
      apply(rewrite discrete_laplace_rat.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp simp add: Let_def)
      by(clarsimp intro!: ord_spmf_bind_reflI)
    case 2 show ?case by simp
  qed
  then show "ord_spmf (=) ?rhs ?lhs" by -
qed

lemma lossless_discrete_laplace_rat[simp]:
  assumes "1\<le>t" and "1\<le>s"
  shows "lossless_spmf (discrete_laplace_rat t s)"
proof -
  have "lossless_spmf (while (True, t,s, 0))"
  proof (rule termination_0_1_immediate_invar,clarify)
    fix b::bool and  t1 s1::nat and  z::int
    assume cond:"fst (b,t1,s1,z)"
        and I:"(\<lambda>(b,t1,s1,z). t1=t\<and>s1=s)(b,t1,s1,z)"
    show "(\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2)) \<le> spmf (map_spmf fst
                    (discrete_laplace_rat_unit t1 \<bind>
                     (\<lambda>x. bernoulli_rat 1 2 \<bind>
                          (\<lambda>b. let y = calculate_y x s1
                               in if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0)
                                  else if b then return_spmf (False, t1, s1, - int y) else return_spmf (False, t1, s1, int y))))) False"
    proof -
      have "spmf (map_spmf fst
                    (discrete_laplace_rat_unit t1 \<bind>
                     (\<lambda>x. bernoulli_rat 1 2 \<bind>
                          (\<lambda>b. let y = calculate_y x s1
                               in if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0)
                                  else if b then return_spmf (False, t1, s1, - int y) else return_spmf (False, t1, s1, int y))))) False
          = spmf (map_spmf fst
                    (discrete_laplace_rat_unit t \<bind>
                     (\<lambda>x. bernoulli_rat 1 2 \<bind>
                          (\<lambda>b. let y = calculate_y x s
                               in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                                  else if b then return_spmf (False, t, s, - int y) else return_spmf (False, t, s, int y))))) False"
        using I by auto
      also have "...
          = spmf (discrete_laplace_rat_unit t \<bind>
                  (\<lambda>x. bernoulli_rat (Suc 0) 2 \<bind> 
                    (\<lambda>b. if \<not> b \<and> calculate_y x s = 0 then return_spmf True 
                          else if b then return_spmf False 
                               else return_spmf False))) False"
        apply(simp add: map_spmf_bind_spmf o_def Let_def map_spmf_if)
        apply(rewrite map_spmf_if)
        apply(rewrite map_spmf_return_spmf, rewrite map_spmf_return_spmf, rewrite map_spmf_return_spmf)
        by(rewrite fst_conv, rewrite fst_conv, rewrite fst_conv,simp)
      finally have 1:"spmf (map_spmf fst
                      (discrete_laplace_rat_unit t1 \<bind>
                        (\<lambda>x. bernoulli_rat 1 2 \<bind>
                          (\<lambda>b. let y = calculate_y x s1 in 
                           if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) 
                           else if b then return_spmf (False, t1, s1, - int y) 
                                else return_spmf (False, t1, s1, int y))))) False 
                  = spmf (discrete_laplace_rat_unit t \<bind>
                          (\<lambda>x. bernoulli_rat (Suc 0) 2 \<bind> 
                            (\<lambda>b. if \<not> b \<and> calculate_y x s = 0 then return_spmf True 
                                 else if b then return_spmf False 
                                      else return_spmf False))) False"
        by simp
      have "ennreal (spmf (discrete_laplace_rat_unit t \<bind>
                          (\<lambda>x. bernoulli_rat (Suc 0) 2 \<bind> 
                            (\<lambda>b. if \<not> b \<and> calculate_y x s = 0 then return_spmf True 
                                 else if b then return_spmf False 
                                      else return_spmf False))) False)
          = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
          (1/2 * ennreal (spmf (if calculate_y x s = 0 then return_spmf True else return_spmf False) False) + 1/2))"
        apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
        apply(simp add: nn_integral_count_space_nat)
        using assms apply(simp)
        using divide_ennreal_def by auto
      also have "... \<ge> (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1/2)))"
      proof -
        have "\<And>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1/2))
                \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
             (1 / 2 * ennreal (spmf (if calculate_y x s = 0 then return_spmf True else return_spmf False) False) + 1 / 2)"
        proof -
          fix x::nat
          have "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1/2))
             \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * ennreal (1/2)"
            by(rewrite ennreal_mult''[of"(1/2)"],simp_all)
          also have "... = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * 1/2"
            by (simp add: divide_ennreal_def)
          also have "... \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
               (1 / 2 * ennreal (spmf (if calculate_y x s = 0 then return_spmf True else return_spmf False) False) + 1 / 2)"
          proof (auto simp add: ennreal_mult_le_mult_iff[of "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)))"])
            show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) / 2 \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (1 / 2)"
              by (simp add: ennreal_times_divide)
            show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) / 2 \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (1 / 2 + 1 / 2)"
            proof -
              have "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) / 2 \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (1 / 2)"
                by (simp add: ennreal_times_divide)
              also have "... \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (1 / 2 + 1 / 2)"
              proof-
                have "(1::ennreal)/2 \<le> 1/2 + 1/2"
                  by simp
                then show ?thesis
                  by(rewrite mult_mono,simp_all)
              qed
              finally show ?thesis by simp
            qed
          qed
          finally show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2))
                     \<le> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
                             (1 / 2 * ennreal (spmf (if calculate_y x s = 0 then return_spmf True else return_spmf False) False) + 1 / 2)"
            by simp
        qed
        then show ?thesis 
          by(rewrite suminf_le,simp_all)
      qed
      also have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1/2))) = (\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1/2))"
        apply(rewrite suminf_ennreal2,simp_all)
        using summable_exp_rat assms by simp
      finally have "ennreal (\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2))
                 \<le> ennreal (spmf (discrete_laplace_rat_unit t \<bind>
                                  (\<lambda>x. bernoulli_rat (Suc 0) 2 \<bind> 
                                    (\<lambda>b. if \<not> b \<and> calculate_y x s = 0 then return_spmf True else if b then return_spmf False else return_spmf False))) False)"
        by simp
      then have 2:"(\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2))
                 \<le> spmf (discrete_laplace_rat_unit t \<bind>
                                  (\<lambda>x. bernoulli_rat (Suc 0) 2 \<bind> 
                                    (\<lambda>b. if \<not> b \<and> calculate_y x s = 0 then return_spmf True else if b then return_spmf False else return_spmf False))) False"
        by simp
      show ?thesis using 1 2 by simp
    qed
  next
    show "0 < (\<Sum>x. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2))"
    proof -
      have "\<And>x. 0 < (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2)"
      proof -
        fix x::nat
        have "0 < (1 - exp (- (1 / real t)))" using assms by simp
        then show "0 < (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (1 / 2)"
          by simp
      qed
      then show ?thesis 
        apply(rewrite suminf_pos, simp_all)
        using assms summable_exp_rat by simp
    qed
  next
    fix sa::"bool\<times>nat\<times>nat\<times>int"
    assume H:"case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s "
    show "lossless_spmf
           (case sa of
            (b, t, s, z) \<Rightarrow>
              discrete_laplace_rat_unit t \<bind>
              (\<lambda>x. bernoulli_rat 1 2 \<bind>
                   (\<lambda>b. let y = calculate_y x s
                        in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                           else if b then return_spmf (False, t, s, - int y)
                                else return_spmf (case (False, t, s, y) of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, int y)))))))"
    proof -
      have 1:"(case sa of
            (b, t, s, z) \<Rightarrow>
              discrete_laplace_rat_unit t \<bind>
              (\<lambda>x. bernoulli_rat 1 2 \<bind>
                   (\<lambda>b. let y = calculate_y x s
                        in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                           else if b then return_spmf (False, t, s, - int y)
                                else return_spmf (case (False, t, s, y) of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, int y)))))))
          = discrete_laplace_rat_unit t \<bind>
              (\<lambda>x. bernoulli_rat 1 2 \<bind>
                   (\<lambda>b. let y = calculate_y x s
                        in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                           else if b then return_spmf (False, t, s, - int y)
                                else return_spmf (case (False, t, s, y) of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, int y))))))"
        using H by auto
      have 2:"lossless_spmf (discrete_laplace_rat_unit t \<bind>
              (\<lambda>x. bernoulli_rat 1 2 \<bind>
                   (\<lambda>b. let y = calculate_y x s
                        in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                           else if b then return_spmf (False, t, s, - int y)
                                else return_spmf (case (False, t, s, y) of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, int y)))))))"
      proof(auto)
        show "lossless_spmf (discrete_laplace_rat_unit t)"
          using assms by simp
        fix x::nat and xa::bool
        show "lossless_spmf
        (let y = calculate_y x s
         in if \<not> xa \<and> y = 0 then return_spmf (True, t, s, 0) else if xa then return_spmf (False, t, s, - int y) else return_spmf (False, t, s, int y))"
          by(simp add:Let_def)
      qed
      show ?thesis using 1 2 by simp
    qed
  next
    show "\<And>sa s'.
       s' \<in> set_spmf
              (case sa of
               (b, t, s, z) \<Rightarrow>
                 discrete_laplace_rat_unit t \<bind>
                 (\<lambda>x. bernoulli_rat 1 2 \<bind>
                      (\<lambda>b. let y = calculate_y x s
                           in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                              else if b then return_spmf (False, t, s, - int y)
                                   else return_spmf (case (False, t, s, y) of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, int y))))))) \<Longrightarrow>
       (case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow> fst sa \<Longrightarrow> case s' of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s"
    proof(clarify)
      fix b1 t1 s1 z1 b2 t2 s2 z2
      assume H:"(b2, t2, s2, z2)
       \<in> set_spmf
           (discrete_laplace_rat_unit t \<bind>
            (\<lambda>x. bernoulli_rat 1 2 \<bind>
                 (\<lambda>b. let y = calculate_y x s
                      in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - int y) else return_spmf (False, t, s, int y))))"
      show "t2 = t \<and> s2 = s"
      proof -
        have "set_spmf
           (discrete_laplace_rat_unit t \<bind>
            (\<lambda>x. bernoulli_rat 1 2 \<bind>
                 (\<lambda>b. let y = calculate_y x s
                      in if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - int y) else return_spmf (False, t, s, int y))))
            \<subseteq> {(True,t,s,0)} \<union> {(b3,t3,s3,z3). b3 =False \<and> t3=t \<and> s3=s}"
          by(simp add: set_bind_spmf o_def set_spmf_bind_set Let_def)
        then have "(b2,t2,s2,z2)\<in> {(True,t,s,0)} \<union> {(b3,t3,s3,z3). b3 =False \<and> t3=t \<and> s3=s}"
          using H by auto
        then show ?thesis
          by auto
      qed
    qed
  next
    show "case (True, t, s, 0) of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s"
      by simp
  qed
  then show ?thesis
    using discrete_laplace_rat_cov_while by auto
qed
end

lemma calculate_y_range_x:
  assumes  "1\<le>s"
  shows "(calculate_y x s = z) = (s*z \<le> x \<and> x \<le> s*(z+1)-1)"
proof
  assume H1:"calculate_y x s = z"
  show "s * z \<le> x \<and> x \<le> s * (z + 1) - 1"
  proof
    have "z\<le> x/s"
      using H1 assms unfolding calculate_y_def
      by auto
    then have "s * z \<le> s * (x/s)"
      using assms mult_left_mono of_nat_0_le_iff of_nat_mult 
      by metis
    also have 1:"... = x"
      using assms by auto
    finally show "s*z \<le> x"
      by linarith
    have "x/s < z+1"
      using H1 assms unfolding calculate_y_def
      by linarith
    then have "s * (x/s) < s * (z+1)"
      using assms mult_strict_left_mono gr_implies_not0 nat_neq_iff not_one_le_zero of_nat_0_less_iff of_nat_mult
      by metis
    then have "x < s * (z+1)"
      using 1 by linarith
    then show "x \<le> s*(z+1)-1"
      by simp
  qed
next
  assume H2:"s * z \<le> x \<and> x \<le> s * (z + 1) - 1"
  show "calculate_y x s = z"
  proof -
    have 1:"(s*z)/s\<le> x/s"
      using H2 assms
      by (metis divide_right_mono of_nat_0_le_iff of_nat_mono)
    have 2:"(s*z)/s = z"
      using assms by simp
    have "z\<le> x/s"
      using 1 2 by simp
    then have p1:"z\<le>calculate_y x s"
      unfolding calculate_y_def
      using le_nat_floor
      by simp
    have "x < s * (z+1)"
      using H2 assms
      by auto
    then have "x/s < (s*(z+1))/s"
      using assms divide_strict_right_mono[of "x" "s*(z+1)" "s"]
      by linarith
    also have "... = s/s * (z+1)"
      using assms times_divide_eq_left[of "s" "s" "z+1"]
      by (metis of_nat_mult)
    also have "... = z+1"
      using assms by simp
    finally have "x/s < z+1" by simp
    then have p2:"calculate_y x s < z+1"
      unfolding calculate_y_def
      by linarith
    show ?thesis using p1 p2 by simp
  qed
qed

lemma spmf_discrete_laplace_rat:
  assumes "1\<le>t" and "1\<le>s"
  shows "spmf (discrete_laplace_rat t s) z = (exp(s/t)-1)/(exp(s/t)+1) * exp(- s*\<bar>z\<bar>/t)"
proof -
  have "ennreal (spmf (discrete_laplace_rat t s) z) = (exp(s/t)-1)/(exp(s/t)+1) * exp(- s*\<bar>z\<bar>/t)"
  proof- 
    have "ennreal (spmf (discrete_laplace_rat t s) z) 
         = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
          (inverse 2 * ennreal (spmf (if calculate_y x s = 0 then discrete_laplace_rat t s else return_spmf (int (calculate_y x s))) z) +
           inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
    apply(rewrite discrete_laplace_rat.simps)
    apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
    apply(simp add: nn_integral_count_space_nat Let_def)
    using assms by(rewrite if_False,simp)
    also have "...
        = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
          (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s)z else spmf (return_spmf (int (calculate_y x s))) z) +
           inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
    proof -
      have "\<forall>n. ennreal ((1 - exp (- (1 / real t))) * exp (- (real n / real t))) * (inverse 2 * ennreal (if calculate_y n s = 0 then spmf (discrete_laplace_rat t s) z else spmf (return_spmf (int (calculate_y n s))) z) + inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y n s))))) = ennreal ((1 - exp (- (1 / real t))) * exp (- (real n / real t))) * (inverse 2 * ennreal (spmf (if calculate_y n s = 0 then discrete_laplace_rat t s else return_spmf (int (calculate_y n s))) z) + inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y n s)))))"
        by presburger
      then show ?thesis
        by presburger
    qed
    also have "... = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
          (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s)z else (indicat_real {Some z} (Some (int (calculate_y x s))))) +
           inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
      by (metis pmf_return)
    finally have 1:"ennreal (spmf (discrete_laplace_rat t s) z) =
  (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
      by simp
    show "ennreal (spmf (discrete_laplace_rat t s) z)= (exp(s/t)-1)/(exp(s/t)+1) * exp(- s*\<bar>z\<bar>/t)"
    proof (cases "0=z")
      case True
      then show ?thesis
      proof -
        have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))))) 
        = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) 0 else indicat_real {Some 0} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some 0} (Some (- int (calculate_y x s))))))"
          using True by blast
        also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) 0 else indicat_real {Some 0} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some 0} (Some (- int (calculate_y x s))))))"
          apply (rule suminf_finite,simp_all)
          using assms 
        proof(simp)
          fix x
          assume x:"\<not> x \<le> s - Suc 0 "
          have "s\<le>x" using x by simp
          show "0< calculate_y x s"
            unfolding calculate_y_def using assms x by simp
        qed
        also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if 0 = 0 then spmf (discrete_laplace_rat t s) 0 else indicat_real {Some 0} (Some (0))) +
         inverse 2 * ennreal (indicat_real {Some 0} (Some (0)))))"
        proof -
          have "\<And>x. x\<in>{0..s-1} \<Longrightarrow> calculate_y x s =0"
            using assms calculate_y_range_x by simp
          then show ?thesis by simp
        qed
        also have "(\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if 0 = 0 then spmf (discrete_laplace_rat t s) 0 else indicat_real {Some 0} (Some (0))) +
         inverse 2 * ennreal (indicat_real {Some 0} (Some (0))))) 
                 = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) 0) +
         inverse 2 * ennreal 1))"
          by simp
        also have "(\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) 0) +
         inverse 2 * ennreal 1))= (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2))"
        proof -
          have "inverse 2 * ennreal (spmf (discrete_laplace_rat t s) 0) + inverse 2 * ennreal 1 
              = inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2"
          proof -
            have 1:"inverse 2 * ennreal 1 = ennreal (inverse 2)" by simp
            have "inverse 2 * ennreal (spmf (discrete_laplace_rat t s) 0) = ennreal (inverse 2) * ennreal(spmf (discrete_laplace_rat t s) 0)"
              by simp
            also have 2:"... = ennreal (inverse 2 * (spmf (discrete_laplace_rat t s) 0))" 
              by(rewrite ennreal_mult'',simp_all)
            show ?thesis using 1 2 by simp
          qed
          then show ?thesis by simp
        qed
        also have "... 
                  = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)))"
        proof -
          have "\<And>x.  ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)
              = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2))"
          proof -
            fix x
            show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)
              = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2))"
              by(rewrite ennreal_mult'[of "(1 - exp (- (1 / real t))) * exp (- (real x / real t))"],simp_all)
          qed
          then show ?thesis by simp
        qed
        also have "... = ennreal (\<Sum>x\<in>{0..s-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2))"
          by simp
        also have "... =  (\<Sum>x\<in>{0..s-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t)))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)" 
          by(rewrite sum_distrib_right, simp)
        also have "... = ((1 - exp (- (1 / real t)))* (\<Sum>x\<in>{0..s-1}. exp (- (real x / real t)))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)"
          by(rewrite sum_distrib_left,simp)
        also have "... = ((1 - exp (- (1 / real t)))* (1-exp(-s/t))/(1-exp(-1/t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)"
          using exp_sum[of"t""s-1"] assms
          by simp
        also have "... = (1-exp(-s/t))* (inverse 2 * (spmf (discrete_laplace_rat t s) 0) + inverse 2)"
          by simp
        finally have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))))) 
      = ennreal ((1 - exp (real_of_int (- int s) / real t)) * (inverse 2 * spmf (discrete_laplace_rat t s) 0 + inverse 2))"
          by simp
        then have "ennreal (spmf (discrete_laplace_rat t s) z) = ennreal ((1 - exp (real_of_int (- int s) / real t)) * (inverse 2 * spmf (discrete_laplace_rat t s) 0 + inverse 2))"
          using 1 by simp
        then have "spmf (discrete_laplace_rat t s) 0 = (1 - exp (-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) 0 + inverse 2)"
          using True by simp
        then have "(1 + exp(-s/t)) * (spmf (discrete_laplace_rat t s) 0) = (1 - exp (-s/t))"
          by algebra
        then have "spmf (discrete_laplace_rat t s) 0 =  (1 - exp (-s/t))/ (1 + exp (-s/t))"
          using eq_divide_imp[of "1+exp(-s/t)" "spmf (discrete_laplace_rat t s) 0" "1-exp(-s/t)"]
          by algebra
        also have "... = (exp(s/t) - 1)/ (exp(s/t) + 1)"
        proof -
          have 1:"(1-exp(-s/t)) * exp(s/t) = exp(s/t) -1"
            apply(rewrite left_diff_distrib)
            by (simp add: exp_minus_inverse mult.commute)
          have 2:"(1+exp(-s/t))* exp(s/t) =  exp(s/t) + 1"
            apply(rewrite ring_distribs(2))
            by (simp add: exp_minus_inverse mult.commute)
          have 3:"(1-exp(-s/t))/(1+exp(-s/t)) = ((1-exp(-s/t)) * exp(s/t))/ ((1+exp(-s/t)) * exp(s/t))"
            by simp
          show ?thesis using 1 2 3 by simp
        qed
        finally have "spmf (discrete_laplace_rat t s) 0 = (exp(s/t) - 1)/ (exp(s/t) + 1)"
          by simp
        then show ?thesis
          using True by simp
      qed
    next
      case False
      then show ?thesis 
      proof(cases "0<z")
        case True
        then show ?thesis
        proof -
          assume z:"0<z"
          have z_nat:"nat z = z"
            using z by simp
          have z_nat_plus1: "nat (z+1) = nat z+1"
            using z by simp
          have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))))) 
              = (\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s))))))"
            using z by simp
          also have "... = (\<Sum>x\<in>{0..s-1}\<union>{s*nat(z)..s*nat(z+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s))))))"
            using z assms 
          proof(rewrite suminf_finite[of "{0..s-1}\<union>{s*nat(z)..s*nat(z+1)-1}"],simp_all,auto)
            fix n::nat
            assume H1:"\<not> n \<le> s - Suc 0" and H2:" \<not> s * nat z \<le> n"
            have 1:"calculate_y n s \<noteq> 0"
              using H1 calculate_y_range_x assms by simp
            have 2:"calculate_y n s \<noteq> z"
              using z H2 assms calculate_y_range_x
              using int_eq_iff by blast
            show "calculate_y n s = 0 \<Longrightarrow> spmf (discrete_laplace_rat t s) z = 0"
              using 1 by simp
            show "0 < calculate_y n s \<Longrightarrow> indicat_real {Some z} (Some (int (calculate_y n s))) = 0"
              using 2 by simp
          next
            fix n
            assume H1:"\<not> n \<le> s - Suc 0" and H2:"\<not> n \<le> s * nat (z + 1) - Suc 0 "
            have 1:"calculate_y n s \<noteq> 0"
              using H1 calculate_y_range_x assms by simp
            have "s*nat(z+1)-Suc 0 =s* (nat z+1) -1"
              using z 
              using nat_add_distrib by force
            then have 2:"calculate_y n s \<noteq> z"
              using assms calculate_y_range_x[of"s" "n" "nat z"] z H2
              by simp
            show "calculate_y n s = 0 \<Longrightarrow> spmf (discrete_laplace_rat t s) z = 0"
              using 1 by simp
            show "0 < calculate_y n s \<Longrightarrow> indicat_real {Some z} (Some (int (calculate_y n s))) = 0"
              using 2 by simp
          qed
          also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s))))))
        +(\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s))))))"
            apply(rule sum.union_disjoint)
            using assms z 
            by(simp_all add: nat_le_eq_zle not_less_eq_eq)
          also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z)))
        +(\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal 1))"
          proof -
            have 1:"\<And>x. x\<in>{0..s-1} \<Longrightarrow> calculate_y x s = 0" 
              using assms calculate_y_range_x by simp
            have 2:"\<And>x. x\<in>{s*nat(z)..s*nat(z+1)-1} \<Longrightarrow> calculate_y x s = nat z"
            proof -
              fix x
              assume H:"x\<in>{s*nat(z)..s*nat(z+1)-1}"
              have 1:"s*nat(z+1) -1 = s*(nat z + 1)-1"
                using z 
                by (simp add: nat_add_distrib)
              show "calculate_y x s = nat z"
                using 1 H assms calculate_y_range_x[of "s" "x" "nat z"] z
                by simp
            qed
            show ?thesis using 1 2 z by simp
          qed
          also have "... = ennreal (\<Sum>x\<in>{0..s-1}. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z))
                          +ennreal (\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. (1 - exp (- (1 / real t))) * exp (- (real x / real t)) *(inverse 2))"
          proof -
            have p11:"(inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z)) = ennreal (inverse 2 * spmf (discrete_laplace_rat t s) z)"
                by(rewrite ennreal_mult'', simp_all)
            then have 1:"\<And>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))
                    = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z))"
              by(rewrite p11, rewrite ennreal_mult''[of "(inverse 2 * spmf (discrete_laplace_rat t s) z)"],simp_all)
            have p21:"(inverse 2 * ennreal 1) = ennreal (inverse 2)"
              by simp
            have 2:"\<And>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * ennreal 1)
                    = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t)) *(inverse 2))"
              by(rewrite p21, rewrite ennreal_mult''[of "inverse 2"],simp_all) 
            show ?thesis using 1 2 by simp
          qed
          also have "... = ennreal ((\<Sum>x\<in>{0..s-1}.(1 - exp (- (1/t))) * exp (- (real x / real t))) * (inverse 2 * spmf (discrete_laplace_rat t s) z))
                          +ennreal ((\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. (1 - exp (- (1/t))) * exp (- (real x / real t))) *(inverse 2))"
            apply(rewrite sum_distrib_right)
            apply(rewrite sum_distrib_right)
            by(simp)
          also have "... = ennreal ((1 - exp (- (1/t))) * (\<Sum>x\<in>{0..s-1}. exp(-(x/t))) * (inverse 2 * spmf (discrete_laplace_rat t s) z))
                         + ennreal ((1 - exp (- (1/t))) * (\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. exp (- (x/t))) *(inverse 2))"
            apply(rewrite sum_distrib_left, rewrite sum_distrib_left)
            by (simp)
          also have "... = ennreal ((1 - exp (- (1/t))) * (1-exp(-s/t))/(1-exp(-1/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z))
                         + ennreal ((1 - exp (- (1/t))) * ((exp(-s*z/t)-exp(-s*(z+1)/t))/(1-exp(-1/t))) *(inverse 2))"
          proof - 
            have 1:"(\<Sum>x\<in>{0..s-1}. exp(-(x/t))) = (1-exp(-s/t))/(1-exp(-1/t))"
              using assms exp_sum[of "t" "s-1"] by simp
            have "s * nat z \<le> s * nat (z + 1) - 1"
              using z assms z_nat_plus1 by simp
            then have "(\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. exp (- (x/t))) = (exp ((-(s * nat z))/t) - exp ((-(s * nat(z+1)))/t)) / (1 - exp (-1/t))"
              using exp_sum_general[of"t" "s*nat z" "s* nat(z+1)-1"] assms z 
              by(simp)
            also have "... = (exp(-s*z/t)-exp(-s*(z+1)/t))/(1-exp(-1/t))"
              using z_nat by auto
            finally have 2:"(\<Sum>x\<in>{s*nat(z)..s*nat(z+1)-1}. exp (- (x/t))) = (exp(-s*z/t)-exp(-s*(z+1)/t))/(1-exp(-1/t))"
              by simp
            show ?thesis using 1 2 by auto
          qed
          also have "... = ennreal ((1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z))
                         + ennreal ((exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2))"
            by simp
          also have "... = ennreal ((1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z)
                                    + (exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2))"
            apply(rewrite ennreal_plus,simp_all)
            using assms z 
            by (simp add: divide_right_mono)
          finally have "(\<Sum>x. ennreal ((1-exp (-(1/t))) * exp (- (x/t))) * 
          (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
           inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))))) 
        = ennreal ((1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z) + (exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2))"
            by simp
          then have p1:"ennreal (spmf (discrete_laplace_rat t s) z) = ennreal ((1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z) + (exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2))"
            using 1 by simp
          then have "spmf (discrete_laplace_rat t s) z = (1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z) + (exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2)"
          proof -
            have 1:"0\<le> spmf (discrete_laplace_rat t s) z" by simp
            have 2:"0\<le> (1-exp(-s/t)) * (inverse 2 * spmf (discrete_laplace_rat t s) z) + (exp(-s*z/t)-exp(-s*(z+1)/t)) *(inverse 2)"
            proof -
              have "0\<le>(exp(-s*z/t)-exp(-s*(z+1)/t))"
              proof -
                have "- s*(z+1)/t < -s*z/t"
                  apply(rewrite divide_strict_right_mono)
                  using assms z by(simp_all)
                then show ?thesis by simp
              qed
              then show ?thesis by simp
            qed
            show ?thesis 
              using 1 2 ennreal_inj p1 by blast
          qed
          then have " spmf (discrete_laplace_rat t s) z * (1+exp(-s/t)) = exp(-s*z/t)-exp(-s*(z+1)/t)"
            by algebra
          also have "... = exp(-s*z/t) * (1-exp(-s/t))"
          proof -
            have "exp(-s*(z+1)/t) = exp(-s*z/t)*exp(-s/t)"
            proof -
              have "-s*z/t + (-s/t) = -s*(z+1)/t"
                using add_divide_distrib[of "-s*z" "-s" "t"]
                by (simp add: int_distrib(1) mult_of_nat_commute)
              then show ?thesis
                using mult_exp_exp[of "-s*z/t" "-s/t"]
                by simp
            qed
            then show ?thesis by argo
          qed
          finally have "spmf (discrete_laplace_rat t s) z * (1+exp(-s/t)) = exp(-s*z/t) * (1-exp(-s/t))"
            by simp
          then have "spmf (discrete_laplace_rat t s) z = exp(-s*z/t)* (1-exp(-s/t))/(1+exp(-s/t))"
            using eq_divide_imp[of "1+exp(-s/t)"]
            by fastforce
          also have "... = (1-exp(-s/t))/(1+exp(-s/t)) * exp(-s*z/t)"
            by simp
          also have "... = (exp(s/t)-1)/(exp(s/t)+1) * exp(-s*z/t)"
          proof -
            have "(1-exp(-s/t))/(1+exp(-s/t)) = (exp(s/t)* (1-exp(-s/t)))/(exp(s/t)*(1+exp(-s/t)))"
              by simp
            also have "... = (exp(s/t)-1)/(exp(s/t)+1)"
            proof -
              have 1:"exp(s/t)* (1-exp(-s/t)) = exp(s/t)-1"
                apply(rewrite right_diff_distrib) 
                by(simp add: exp_minus_inverse)
              have 2:"exp(s/t)* (1+exp(-s/t)) = exp(s/t)+1"
                apply(rewrite ring_distribs(1)) 
                by(simp add: exp_minus_inverse)
              show ?thesis using 1 2 by simp
            qed
            finally have "(1-exp(-s/t))/(1+exp(-s/t)) = (exp(s/t)-1)/(exp(s/t)+1)"
              by simp
            then show ?thesis by simp
          qed
          finally have "spmf (discrete_laplace_rat t s) z = (exp(s/t)-1)/(exp(s/t)+1) * exp(-s*z/t)"
            by simp
          then show ?thesis
            using z by simp
        qed
      next
        case False
        show "0 \<noteq> z \<Longrightarrow> \<not> 0 < z \<Longrightarrow> ennreal (spmf (discrete_laplace_rat t s) z) = ennreal ((exp (real s / real t) - 1) / (exp (real s / real t) + 1) * exp (real_of_int (- int s * \<bar>z\<bar>) / real t))"
        proof -
          assume z1:"0 \<noteq> z" and z2:"\<not> 0 < z"
          have z:"z<0" 
            using z1 z2 by simp
          have z_nat:"nat(-z) = -z"
            using z by simp
          have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))
               =(\<Sum>x\<in>{0..s-1}\<union>{s*nat(-z)..s*(nat(-z)+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
            apply(rewrite suminf_finite[of "{0..s-1}\<union>{s*nat(-z)..s*(nat(-z)+1)-1}"])
            using z assms 
          proof(simp_all,auto)
            fix n
            have nat_z:"-z= nat(-z)"
              using z by simp
            assume n1:"\<not> n \<le> s - Suc 0" and n2:"\<not> s * nat (- z) \<le> n"
            have n11:"s\<le> n"
              using n1 by auto
            then have p1:"calculate_y n s \<noteq> 0"
              using assms calculate_y_range_x by simp
            have n21:"n<s*nat(-z)"
              using n2 by simp
            have p2:"calculate_y n s \<noteq> -z"
              using n21 nat_z calculate_y_range_x[of"s" "n" "nat(-z)"] assms by simp
            show "calculate_y n s = 0 \<Longrightarrow> spmf (discrete_laplace_rat t s) z = 0"
              using p1 by simp
            show "indicat_real {Some z} (Some (- int (calculate_y n s))) = 0"
              using p2 by simp
          next
            fix n
            have nat_z:"-z= nat(-z)"
              using z by simp
            assume n1:"\<not> n \<le> s - Suc 0" and n2:"\<not> n \<le> s + s * nat (- z) - Suc 0"
            have n11:"s\<le> n"
              using n1 by auto
            then have p1:"calculate_y n s \<noteq> 0"
              using assms calculate_y_range_x by simp
            have n21:"s*(nat(-z)+1) \<le> n"
              using n2 by simp
            have p2:"calculate_y n s \<noteq> -z"
              using n21 nat_z calculate_y_range_x[of"s" "n" "nat(-z)"] assms by auto
            show "calculate_y n s = 0 \<Longrightarrow> spmf (discrete_laplace_rat t s) z = 0"
              using p1 by simp
            show "indicat_real {Some z} (Some (- int (calculate_y n s))) = 0"
              using p2 by simp
          qed
          also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))
                          +(\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))))"
            apply(rewrite sum.union_disjoint,simp_all)
            using z assms z_nat 
            by (simp add: not_less_eq_eq)
          also have "... = (\<Sum>x\<in>{0..s-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))) 
                         + (\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2 * ennreal 1)"
          proof -
            have 1:"\<And>x. x\<in>{0..s-1} \<Longrightarrow> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))) 
                                    = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))"
            proof -
              fix x 
              assume x:"x\<in>{0..s-1}"
              have p1:"calculate_y x s = 0"
                using x calculate_y_range_x assms by simp
              have p2:"inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s))))
                        =inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z)"
                using p1 by simp
              have p3:"inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))) = 0"
                using p1 z by simp
              then show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))) 
                       = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))"
                using p2 p3 by simp
            qed
            have 2:"\<And>x. x\<in>{s*nat(-z)..s*(nat(-z)+1)-1} \<Longrightarrow> ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))) 
                                    = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2 * ennreal 1"
            proof -
              fix x::nat
              assume x:"x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}"
              have p1:"calculate_y x s = - z"
                using x z_nat assms calculate_y_range_x[of"s" "x" "nat(-z)"] z by simp 
              have p2:"inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) = 0"
                using p1 z by simp
              have p3:"inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))) = inverse 2 * ennreal 1"
                using p1 by simp
              show "ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s))))) 
                  = ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2 * ennreal 1"
                using p2 p3 by simp
            qed
            show ?thesis using 1 2 by simp
          qed
          also have "... = ennreal (\<Sum>x\<in>{0..s-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))
                          +ennreal (\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2)"
          proof -
            have 1:"\<And>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))
                    = ennreal (((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))"
            proof - 
              have p:" (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z)) = ennreal (inverse 2 * (spmf (discrete_laplace_rat t s) z))"
              proof - 
                have p:"inverse 2 = ennreal (inverse 2)"
                  by simp
                show ?thesis
                  by(rewrite p,rewrite ennreal_mult',simp_all)
              qed
              show "\<And>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * ennreal (spmf (discrete_laplace_rat t s) z))
                    = ennreal (((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))"
                by(rewrite p, rewrite ennreal_mult''[of "(inverse 2 * (spmf (discrete_laplace_rat t s) z))"],simp_all)  
            qed
            have 2:"\<And>x.  ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2 * ennreal 1
                       = ennreal (((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2)"
            proof -
              have p:"inverse 2 * ennreal 1 = ennreal(inverse 2)"
                by simp
              then show "\<And>x.  ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2 * ennreal 1
                       = ennreal (((1 - exp (- (1 / real t))) * exp (- (real x / real t))) * inverse 2)"
                using ennreal_mult''[of "inverse 2"] by simp
            qed
            show ?thesis using 1 2 by simp
          qed
          also have "... = ennreal ((\<Sum>x\<in>{0..s-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t)))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))
                          +ennreal ((\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. ((1 - exp (- (1 / real t))) * exp (- (real x / real t)))) * inverse 2)"
            by(rewrite sum_distrib_right,rewrite sum_distrib_right,simp)
          also have "... = ennreal (((1 - exp (- (1 / real t))) * (\<Sum>x\<in>{0..s-1}. exp (- (real x / real t)))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))
                          +ennreal ((1 - exp (- (1 / real t))) * (\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}.  exp (- (real x / real t))) * inverse 2)"
            by(rewrite sum_distrib_left, rewrite sum_distrib_left,simp)
          also have "... = ennreal (((1 - exp (- (1 / real t))) * (1-exp(-s/t))/(1-exp(-1/t))) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)))
                          +ennreal ((1 - exp (- (1 / real t))) * (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))/(1-exp(-1/t))) * inverse 2)"
          proof -
            have 1:"(\<Sum>x\<in>{0..s-1}. exp(-(x/t))) = (1-exp(-s/t))/(1-exp(-1/t))"
              using assms exp_sum[of "t" "s-1"] by simp
            have p1:"s*nat(-z) \<le> s*(nat(-z)+1)-1"
              using assms by simp
            have "(\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. exp (- (x/t))) = (exp ((-(s*nat (- z)))/t) - exp((-(s*(nat (- z) + 1)))/t))/(1-exp(-1/t))"
              using exp_sum_general[of"t" "s*nat(-z)" "s*(nat(-z)+1)-1"] assms p1
              by simp
            also have "... = exp(-s*(nat(-z))/t) * (1- exp(-s/t))/(1-exp(-1/t))"
            proof -
              have "exp ((-(s*nat (- z)))/t) - exp((-(s*(nat (- z) + 1)))/t) = exp(-s*(nat(-z))/t) * (1- exp(-s/t))"
              proof-
                have "exp((-(s*(nat (- z) + 1)))/t) = exp(-s*(nat(-z))/t) * exp(-s/t)"
                proof -
                  have "-(s*(nat (- z) + 1)) = -s*(nat(-z)) + (-s)"
                    by simp
                  then have "(-(s*(nat (- z) + 1)))/t = -s*(nat(-z))/t + (-s/t)"
                    using add_divide_distrib[of "-s*(nat(-z))" "(-s)" "t"]
                    by auto
                  then show ?thesis 
                    using exp_add[of "-s*(nat(-z))/t" "(-s/t)"]
                    by simp
                qed
                then show ?thesis 
                  using right_diff_distrib[of"exp(-s*(nat(-z))/t)" "1" "exp(-s/t)"]
                  by simp
              qed
              then show ?thesis by simp
            qed
            also have "... = exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))/(1-exp(-1/t))"
            proof -
              have "nat (-z) = \<bar>z\<bar>"
                using z by simp
              then show ?thesis by simp
            qed
            finally have 2:"(\<Sum>x\<in>{s*nat(-z)..s*(nat(-z)+1)-1}. exp (- (x/t))) = exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))/(1-exp(-1/t))"
              by simp
            show ?thesis using 1 2 by auto
          qed
          also have "... = ennreal ((1-exp(-s/t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)) + (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))) * inverse 2)"
            by(rewrite ennreal_plus,simp_all)
          finally have "(\<Sum>x. ennreal ((1 - exp (- (1 / real t))) * exp (- (real x / real t))) *
        (inverse 2 * ennreal (if calculate_y x s = 0 then spmf (discrete_laplace_rat t s) z else indicat_real {Some z} (Some (int (calculate_y x s)))) +
         inverse 2 * ennreal (indicat_real {Some z} (Some (- int (calculate_y x s)))))) 
                      = ennreal ((1-exp(-s/t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)) + (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))) * inverse 2)"
            by simp
          then have 2:"ennreal (spmf (discrete_laplace_rat t s)z) = ennreal ((1-exp(-s/t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)) + (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))) * inverse 2)"
            using 1 by simp
          have "spmf (discrete_laplace_rat t s)z = (1-exp(-s/t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)) + (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))) * inverse 2"
          proof -
            have p1:"0\<le>spmf (discrete_laplace_rat t s)z " 
              by simp
            have p2:"0\<le>(1-exp(-s/t)) * (inverse 2 * (spmf (discrete_laplace_rat t s) z)) + (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t))) * inverse 2"
              by(simp)
            show ?thesis using 2 p1 p2 ennreal_inj by blast
          qed
          then have "(spmf (discrete_laplace_rat t s)z) * (1+exp(-s/t)) = (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t)))"
            by algebra
          then have "spmf (discrete_laplace_rat t s)z = (exp(-s*\<bar>z\<bar>/t) * (1- exp(-s/t)))/(1+exp(-s/t))"
            using eq_divide_imp[of "(1+exp(-s/t))"] by fastforce
          also have "... = (1- exp(-s/t))/(1+exp(-s/t)) * exp(-s*\<bar>z\<bar>/t)"
            by simp
          also have "... = (exp(s/t)-1)/(exp(s/t)+1) * exp(-s*\<bar>z\<bar>/t)"
          proof -
            have 1:"exp(s/t) * (1- exp(-s/t)) = exp(s/t)-1"
              using exp_minus_inverse right_diff_distrib[of"exp(s/t)" "1" "exp(-s/t)"]
              by auto
            have 2:"exp(s/t) * (1+ exp(-s/t)) = exp(s/t)+1"
              using exp_minus_inverse ring_distribs(1)[of"exp(s/t)" "1" "exp(-s/t)"]
              by auto
            have "(1- exp(-s/t))/(1+exp(-s/t)) = (exp(s/t) * (1- exp(-s/t)))/(exp(s/t)*(1+exp(-s/t)))"
              by simp
            also have "... = (exp(s/t)-1)/(exp(s/t)+1)"
              using 1 2 by simp
            finally have "(1- exp(-s/t))/(1+exp(-s/t)) = (exp(s/t)-1)/(exp(s/t)+1)"
              by simp
            then show ?thesis by simp
          qed
          finally have "spmf (discrete_laplace_rat t s) z = (exp(s/t)-1)/(exp(s/t)+1) * exp(-s*\<bar>z\<bar>/t)"
            by simp
          then show ?thesis by simp
        qed
      qed
    qed
  qed
  then show ?thesis by simp
qed

end
