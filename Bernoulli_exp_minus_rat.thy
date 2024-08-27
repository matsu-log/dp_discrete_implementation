theory Bernoulli_exp_minus_rat_2
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
          "Bernoulli_rat"
          "Bernoulli_exp_minus_real"
begin

context notes [[function_internals]] begin
partial_function (spmf) loop1_alt :: "rat  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "loop1_alt p k = 
    do {
       a \<leftarrow> let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k));
      if a then loop1_alt p (k+1) else return_spmf k
    }
"
end

definition  bernoulli_exp_minus_rat_from_0_to_1 :: "rat \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat_from_0_to_1 p = 
    do {
        k \<leftarrow> loop1_alt p 1;
        if odd k then return_spmf True else return_spmf False
    }
  "

context notes [[function_internals]] begin
partial_function (spmf) loop2_alt :: "rat \<Rightarrow> nat \<Rightarrow> bool spmf" where
  "loop2_alt p k = (if 1\<le>k then do {
                                b \<leftarrow> bernoulli_exp_minus_rat_from_0_to_1 1;
                                if b then loop2_alt p (k-1) else return_spmf False
                                } 
                else return_spmf True)"
end

definition bernoulli_exp_minus_rat :: "rat  \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat p = 
  (
    if p < 0 then return_spmf True  
    else if 0 \<le> p & p\<le>1  then bernoulli_exp_minus_rat_from_0_to_1 p
    else
     do {
        b \<leftarrow> loop2_alt p (nat (floor p));
        if b then bernoulli_exp_minus_rat_from_0_to_1 (p- (of_int (floor p))) else return_spmf b
      }
  )
"
lemma loop1_alt_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop1_alt. P (curry loop1_alt))"
    and "P (\<lambda>loop1_alt p. return_pmf None)"
    and "(\<And>loop1_alt'. P loop1_alt' \<Longrightarrow> P (\<lambda>a aa. (let a = quotient_of a in case a of (n, d) \<Rightarrow> bernoulli_rat (nat n) (nat (d * int aa))) \<bind> (\<lambda>aaa. if aaa then loop1_alt' a (aa + 1) else return_spmf aa)))"
  shows "P loop1_alt"
  using assms by (rule loop1_alt.fixp_induct)

thm loop2_alt.fixp_induct

lemma loop2_alt_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop2_alt. P (curry loop2_alt))"
    and "P (\<lambda>loop2_alt p. return_pmf None)"
    and "(\<And>loop2_alt'. P loop2_alt' \<Longrightarrow> P (\<lambda>a b. if 1 \<le> b then bernoulli_exp_minus_rat_from_0_to_1 1 \<bind> (\<lambda>ba. if ba then loop2_alt' a (b - 1) else return_spmf False) else return_spmf True))"
  shows "P loop2_alt"
  using assms by (rule loop2_alt.fixp_induct)

lemma sublemma_for_loop1_alt_eq_loop1:
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

lemma loop1_alt_eq_loop1:
  fixes p::rat
  assumes "0\<le>p"
  shows "loop1_alt p 1 = loop1 (of_rat p) 1" 
proof - 
  have "loop1_alt p x = loop1 (of_rat p) x" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule :loop1_alt_fixp_induct)
      case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next
      case (step loop1')
      then show ?case 
        apply(rewrite loop1.simps)
        apply(rewrite sublemma_for_loop1_alt_eq_loop1)
        apply(simp add:assms)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        done
    qed
  next
    show "ord_spmf (=) ?rhs ?lhs"
    proof(induction arbitrary: x and x rule: loop1_fixp_induct)
      case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next
      case (step loop1')
      then show ?case 
        apply(rewrite loop1_alt.simps)
        apply(rewrite sublemma_for_loop1_alt_eq_loop1)
        apply(simp add:assms)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        done
    qed
  qed
  from this[of 1] show ?thesis by simp
qed

lemma bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1:
  fixes p::rat
  assumes "0\<le>p"
  shows "bernoulli_exp_minus_rat_from_0_to_1 p = bernoulli_exp_minus_real_from_0_to_1 (of_rat p)"
  apply(rewrite bernoulli_exp_minus_rat_from_0_to_1_def)
  apply(rewrite bernoulli_exp_minus_real_from_0_to_1_def)
  using loop1_alt_eq_loop1 assms by simp

lemma loop2_alt_eq_loop2:
  fixes p::rat
  assumes "0\<le>p"
  shows "loop2_alt p k = loop2 (of_rat p) k" (is "?lhs = ?rhs")
proof (rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof (induction arbitrary: k rule: loop2_alt_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step loop2_alt')
    then show ?case 
      apply(rewrite loop2.simps)
      apply(simp add: bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      done
  qed
  show "ord_spmf (=) ?rhs ?lhs"
  proof (induction arbitrary: k rule: loop2_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step loop2)
    then show ?case 
      apply(rewrite loop2_alt.simps)
      apply(simp add: bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      done
  qed
qed

lemma sublemma_for_bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real:
  fixes p::rat
  assumes "0\<le>p"
  shows "bernoulli_exp_minus_rat_from_0_to_1 (p - rat_of_int \<lfloor>p\<rfloor>) = bernoulli_exp_minus_real_from_0_to_1 (of_rat p - real_of_int \<lfloor>real_of_rat p\<rfloor>)"
proof -
  have "of_rat (p - rat_of_int \<lfloor>p\<rfloor>) = of_rat p - real_of_int \<lfloor>real_of_rat p\<rfloor>"
    by (simp add: of_rat_diff)
  then show ?thesis
    using  assms bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1 by simp
qed

lemma bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real:
  fixes p::rat
  assumes "0\<le>p"
  shows "bernoulli_exp_minus_rat p = bernoulli_exp_minus_real (of_rat p)"
  apply(rewrite bernoulli_exp_minus_rat_def)
  apply(rewrite bernoulli_exp_minus_real_def)
  apply(simp add: loop2_alt_eq_loop2 bernoulli_exp_minus_rat_from_0_to_1_eq_bernoulli_exp_minus_real_from_0_to_1)
  apply(rewrite sublemma_for_bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real)
  by(simp_all add: assms)

lemma spmf_bernoulli_exp_minus_rat_True[simp]:
  fixes p::rat
  assumes "0\<le>p"
  shows "spmf (bernoulli_exp_minus_rat p) True = exp(-(of_rat p))"
proof -
  have "spmf (bernoulli_exp_minus_rat p) True = spmf (bernoulli_exp_minus_real (of_rat p)) True"
    using bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real assms by simp
  also have "... = exp(-(of_rat p))"
    using spmf_bernoulli_exp_minus_real_True assms by simp
  finally show ?thesis by simp
qed
end
