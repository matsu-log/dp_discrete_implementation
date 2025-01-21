section \<open>Bernoulli distribution that take exp(-p) as parameter, where p is a rational number\<close>
theory Bernoulli_exp_minus_rat
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
          "Bernoulli_rat"
          "Bernoulli_exp_minus_real"
begin

subsection \<open>Definite bernoulli_exp_minus_rat\<close>
context notes [[function_internals]] begin
partial_function (spmf) bernoulli_exp_minus_rat_from_0_to_1_loop :: "rat  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "bernoulli_exp_minus_rat_from_0_to_1_loop \<gamma> k = 
    do {
       a \<leftarrow> let (n,d) = quotient_of \<gamma> in bernoulli_rat (nat n) (nat (d*k));
      if a then bernoulli_exp_minus_rat_from_0_to_1_loop \<gamma> (k+1) else return_spmf k
    }
"
end

definition  bernoulli_exp_minus_rat_from_0_to_1 :: "rat \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat_from_0_to_1 \<gamma> = 
    do {
        k \<leftarrow> bernoulli_exp_minus_rat_from_0_to_1_loop \<gamma> 1;
        if odd k then return_spmf True else return_spmf False
    }
  "
context notes [[function_internals]] begin
partial_function (spmf) bernoulli_exp_minus_rat_loop :: "nat \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat_loop k = (if 1\<le>k then do {
                                b \<leftarrow> bernoulli_exp_minus_rat_from_0_to_1 1;
                                if b then bernoulli_exp_minus_rat_loop (k-1) else return_spmf False
                                } 
                else return_spmf True)"
end

definition bernoulli_exp_minus_rat :: "rat  \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat \<gamma> = 
  (
    if \<gamma> < 0 then return_spmf True  
    else if 0 \<le> \<gamma> & \<gamma>\<le>1  then bernoulli_exp_minus_rat_from_0_to_1 \<gamma>
    else
     do {
        b \<leftarrow> bernoulli_exp_minus_rat_loop (nat (floor \<gamma>));
        if b then bernoulli_exp_minus_rat_from_0_to_1 (\<gamma>- (of_int (floor \<gamma>))) else return_spmf b
      }
  )
"

subsection \<open>Properties of bernoulli_exp_minus_rat\<close>

lemma bernoulli_exp_minus_rat_from_0_to_1_loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>bernoulli_exp_minus_rat_from_0_to_1_loop. P (curry bernoulli_exp_minus_rat_from_0_to_1_loop))"
    and "P (\<lambda>bernoulli_exp_minus_rat_from_0_to_1_loop p. return_pmf None)"
    and "(\<And>bernoulli_exp_minus_rat_from_0_to_1_loop'. P bernoulli_exp_minus_rat_from_0_to_1_loop' \<Longrightarrow> P (\<lambda>a aa. (let a = quotient_of a in case a of (n, d) \<Rightarrow> bernoulli_rat (nat n) (nat (d * int aa))) \<bind> (\<lambda>aaa. if aaa then bernoulli_exp_minus_rat_from_0_to_1_loop' a (aa + 1) else return_spmf aa)))"
  shows "P bernoulli_exp_minus_rat_from_0_to_1_loop"
  using assms by (rule bernoulli_exp_minus_rat_from_0_to_1_loop.fixp_induct)

lemma bernoulli_exp_minus_rat_loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>bernoulli_exp_minus_rat_loop. return_pmf None)"
and "(\<And>k. P k \<Longrightarrow>
      P (\<lambda>ka. if 1 \<le> ka then bernoulli_exp_minus_rat_from_0_to_1 1 \<bind> (\<lambda>b. if b then k (ka - 1) else return_spmf False)
               else return_spmf True))"
shows "P bernoulli_exp_minus_rat_loop"
  using assms by (rule bernoulli_exp_minus_rat_loop.fixp_induct)

lemma sublemma_for_bernoulli_exp_minus_rat_from_0_to_1_loop_eq_bernoulli_exp_minus_real_from_0_to_1_loop:
  fixes p::rat and k::nat
  assumes "0\<le>p"
  shows "(let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) = (bernoulli (of_rat p/k))"
proof-
  have 1:"(let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) = (bernoulli (of_rat p/k)) 
      = (let (n,d) = quotient_of p in (bernoulli_rat (nat n) (nat (d*k)) = (bernoulli (of_rat p/k))))"
    by auto
  have 2:"let (n,d) = quotient_of p in (bernoulli_rat (nat n) (nat (d*k))) = (bernoulli (of_rat p/k))"
  proof (simp,rule)
    fix n d
    assume asm:"quotient_of p = (n,d)"    
    have "0\<le>n" and "0\<le>d"
      using asm assms quotient_of_div[of "p" "n" "d"] quotient_of_denom_pos[of "p" "n" "d"]
            Fract_of_int_quotient zero_le_Fract_iff by(simp_all)
    then have "nat n/nat (d*k) = n/(d*k)"
      by simp
    also have "... = of_rat p/k"
      using asm quotient_of_div[of "p" "n" "d"] 
      by (simp add: of_rat_divide)
    finally have 0:"nat n/nat (d*k) = of_rat p/k"
      by simp
    show "bernoulli_rat (nat n) (nat (d*k)) = bernoulli (of_rat p/k)"
      by (simp add: "0" bernoulli_eq_bernoulli_pmf bernoulli_rat_eq_bernoulli_pmf)
  qed
  show ?thesis 
    using 1 2 by simp
qed

lemma bernoulli_exp_minus_rat_from_0_to_1_loop_eq_bernoulli_exp_minus_real_from_0_to_1_loop:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "bernoulli_exp_minus_rat_from_0_to_1_loop \<gamma> 1 = bernoulli_exp_minus_real_from_0_to_1_loop (of_rat \<gamma>) 1" 
proof - 
  have "bernoulli_exp_minus_rat_from_0_to_1_loop \<gamma> x = bernoulli_exp_minus_real_from_0_to_1_loop (of_rat \<gamma>) x" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule :bernoulli_exp_minus_rat_from_0_to_1_loop_fixp_induct)
      case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next
      case (step loop1')
      then show ?case 
        apply(rewrite bernoulli_exp_minus_real_from_0_to_1_loop.simps)
        apply(rewrite sublemma_for_bernoulli_exp_minus_rat_from_0_to_1_loop_eq_bernoulli_exp_minus_real_from_0_to_1_loop)
        apply(simp add:assms)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        done
    qed
  next
    show "ord_spmf (=) ?rhs ?lhs"
    proof(induction arbitrary: x and x rule: bernoulli_exp_minus_real_from_0_to_1_loop_fixp_induct)
      case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next
      case (step loop1')
      then show ?case 
        apply(rewrite bernoulli_exp_minus_rat_from_0_to_1_loop.simps)
        apply(rewrite sublemma_for_bernoulli_exp_minus_rat_from_0_to_1_loop_eq_bernoulli_exp_minus_real_from_0_to_1_loop)
        apply(simp add:assms)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        done
    qed
  qed
  from this[of 1] show ?thesis by simp
qed

lemma bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "bernoulli_exp_minus_rat_from_0_to_1 \<gamma> = bernoulli_exp_minus_real_from_0_to_1 (of_rat \<gamma>)"
  apply(rewrite bernoulli_exp_minus_rat_from_0_to_1_def)
  apply(rewrite bernoulli_exp_minus_real_from_0_to_1_def)
  using bernoulli_exp_minus_rat_from_0_to_1_loop_eq_bernoulli_exp_minus_real_from_0_to_1_loop assms by simp

lemma bernoulli_exp_minus_rat_loop_eq_bernoulli_exp_minus_real_loop:
  shows "bernoulli_exp_minus_rat_loop k = bernoulli_exp_minus_real_loop k"
proof (rule spmf.leq_antisym)
  show "ord_spmf (=) (bernoulli_exp_minus_rat_loop k) (bernoulli_exp_minus_real_loop k)"
  proof(induction arbitrary:k rule: bernoulli_exp_minus_rat_loop_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step k)
    then show ?case
      apply(rewrite bernoulli_exp_minus_real_loop.simps)
      apply(rewrite bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1,simp)
      by(clarsimp intro!: ord_spmf_bind_reflI)
  qed
next
  show "ord_spmf (=) (bernoulli_exp_minus_real_loop k) (bernoulli_exp_minus_rat_loop k)"
  proof(induction arbitrary:k rule: bernoulli_exp_minus_real_loop_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step k)
    then show ?case
      apply(rewrite bernoulli_exp_minus_rat_loop.simps)
      apply(rewrite bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1,simp)
      by(clarsimp intro!: ord_spmf_bind_reflI)
  qed
qed


lemma sublemma_for_bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "bernoulli_exp_minus_rat_from_0_to_1 (\<gamma> - rat_of_int \<lfloor>\<gamma>\<rfloor>) = bernoulli_exp_minus_real_from_0_to_1 (of_rat \<gamma> - real_of_int \<lfloor>real_of_rat \<gamma>\<rfloor>)"
proof -
  have "of_rat (\<gamma> - rat_of_int \<lfloor>\<gamma>\<rfloor>) = of_rat \<gamma> - real_of_int \<lfloor>real_of_rat \<gamma>\<rfloor>"
    by (simp add: of_rat_diff)
  then show ?thesis
    using  assms bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1 by simp
qed

lemma bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "bernoulli_exp_minus_rat \<gamma> = bernoulli_exp_minus_real (of_rat \<gamma>)"
  apply(rewrite bernoulli_exp_minus_rat_def)
  apply(rewrite bernoulli_exp_minus_real_def)
  apply(simp add: bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1)
  apply(rewrite sublemma_for_bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real)
  by(simp_all add: assms bernoulli_exp_minus_rat_loop_eq_bernoulli_exp_minus_real_loop)

lemma lossless_bernoulli_exp_minus_rat:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "lossless_spmf (bernoulli_exp_minus_rat \<gamma>)"
  using assms  bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real by simp

lemma spmf_bernoulli_exp_minus_rat_True[simp]:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "spmf (bernoulli_exp_minus_rat \<gamma>) True = exp(-(of_rat \<gamma>))"
proof -
  have "spmf (bernoulli_exp_minus_rat \<gamma>) True = spmf (bernoulli_exp_minus_real (of_rat \<gamma>)) True"
    using bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real assms by simp
  also have "... = exp(-(of_rat \<gamma>))"
    using assms by simp
  finally show ?thesis by simp
qed

lemma spmf_bernoulli_exp_minus_rat_False[simp]:
  fixes \<gamma>::rat
  assumes "0\<le>\<gamma>"
  shows "spmf (bernoulli_exp_minus_rat \<gamma>) False = 1-exp(-(of_rat \<gamma>))"
proof -
  have "spmf (bernoulli_exp_minus_rat \<gamma>) False = spmf (bernoulli_exp_minus_real (of_rat \<gamma>)) False"
    using bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real assms by simp
  also have "... = 1 - exp(-(of_rat \<gamma>))"
    using assms by simp
  finally show ?thesis by simp
qed
end
