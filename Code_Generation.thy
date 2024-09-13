theory Code_Generation 
  imports "Executable_Randomized_Algorithms.Randomized_Algorithm"
          "Discrete_Laplace_rat"
          "Bernoulli_exp_minus_rat"
          "Bernoulli_rat"
          "Probabilistic_While.Fast_Dice_Roll"
begin
context fixes n :: nat notes [[function_internals]] begin

partial_function (random_alg) fast_dice_roll_ra :: "nat \<Rightarrow> nat \<Rightarrow> nat random_alg"
where
  "fast_dice_roll_ra v c = 
  (if v \<ge> n then if c < n then return_ra c else fast_dice_roll_ra (v - n) (c - n)
   else do {
     b \<leftarrow> coin_ra;
     fast_dice_roll_ra (2 * v) (2 * c + (if b then 1 else 0)) } )"

declare fast_dice_roll_ra.simps[code]

definition fast_uniform_ra :: "nat random_alg"
  where "fast_uniform_ra = fast_dice_roll_ra 1 0"
end

lemma fast_dice_roll_ra_correct:
"spmf_of_ra (fast_dice_roll_ra n v c) = fast_dice_roll n v c"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) (\<lambda>pair. fast_dice_roll n (fst pair) (snd pair)) (\<lambda>pair. fast_dice_roll_ra n (fst pair) (snd pair))"
    unfolding fast_dice_roll_def fast_dice_roll_ra_def curry_def
    apply(simp add: Basic_BNF_LFPs.xtor_rel)
    apply(rule fixp_ra_parametric)
    using fast_dice_roll.mono 
    unfolding curry_def apply(simp)
    using fast_dice_roll_ra.mono 
    unfolding curry_def apply(simp)
    by(transfer_prover)
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by simp
qed

lemma fast_uniform_ra_correct:
"spmf_of_ra (fast_uniform_ra n)= (fast_uniform n)"
  unfolding fast_uniform_def fast_uniform_ra_def
  by (simp add: fast_dice_roll_ra_correct)


context
  includes lifting_syntax
begin

lemma fast_uniform_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) fast_uniform fast_uniform_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def 
  using fast_uniform_ra_correct by auto

end


definition bernoulli_rat_ra :: "nat \<Rightarrow> nat \<Rightarrow> bool random_alg" where
"bernoulli_rat_ra n d = 
  (if d=0 then return_ra False
   else do {
            x \<leftarrow> fast_uniform_ra d;
            return_ra (x<n)
})"

lemma spmf_of_ra_if:
  assumes "spmf_of_ra ra_1 = spmf_1" and "spmf_of_ra ra_2 = spmf_2"
  shows "spmf_of_ra (if b then ra_1 else ra_2) = (if b then spmf_1 else spmf_2)"
  by (simp add: assms(1) assms(2))

lemma bernoulli_rat_ra_correct:
"spmf_of_ra (bernoulli_rat_ra n d) = bernoulli_rat n d"
  unfolding bernoulli_rat_def bernoulli_rat_ra_def
  by(rule spmf_of_ra_if,simp add: spmf_of_ra_simps, simp add:fast_uniform_ra_correct spmf_of_ra_simps)

context
  includes lifting_syntax
begin

lemma bernoulli_rat_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) (\<lambda>(n, d). bernoulli_rat n d) (\<lambda>(n, d). bernoulli_rat_ra n d)"
  unfolding rel_fun_def rel_spmf_of_ra_def 
  using bernoulli_rat_ra_correct by auto

end

context notes [[function_internals]] begin
partial_function (random_alg) loop1_alt_ra :: "rat  \<Rightarrow> nat  \<Rightarrow> nat random_alg" where
 "loop1_alt_ra p k = 
    do {
       a \<leftarrow> let (n,d) = quotient_of p in bernoulli_rat_ra (nat n) (nat (d*k));
      if a then loop1_alt_ra p (k+1) else return_ra k
    }
"
end

declare loop1_alt_ra.simps[code]

definition  bernoulli_exp_minus_rat_from_0_to_1_ra :: "rat \<Rightarrow> bool random_alg" where
  "bernoulli_exp_minus_rat_from_0_to_1_ra p = 
    do {
        k \<leftarrow> loop1_alt_ra p 1;
        if odd k then return_ra True else return_ra False
    }
  "

context notes [[function_internals]] begin
partial_function (random_alg) loop2_alt_ra :: "rat \<Rightarrow> nat \<Rightarrow> bool random_alg" where
  "loop2_alt_ra p k = (if 1\<le>k then do {
                                b \<leftarrow> bernoulli_exp_minus_rat_from_0_to_1_ra 1;
                                if b then loop2_alt_ra p (k-1) else return_ra False
                                } 
                else return_ra True)"
end

declare loop2_alt_ra.simps[code]

definition bernoulli_exp_minus_rat_ra :: "rat  \<Rightarrow> bool random_alg" where
  "bernoulli_exp_minus_rat_ra p = 
  (
    if p < 0 then return_ra True  
    else if 0 \<le> p & p\<le>1  then bernoulli_exp_minus_rat_from_0_to_1_ra p
    else
     do {
        b \<leftarrow> loop2_alt_ra p (nat (floor p));
        if b then bernoulli_exp_minus_rat_from_0_to_1_ra (p- (of_int (floor p))) else return_ra b
      }
  )
"

lemma loop1_alt_ra_correct:
"spmf_of_ra (loop1_alt_ra p k) = loop1_alt p k"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) (\<lambda>pair. loop1_alt (fst pair) (snd pair)) (\<lambda>pair. loop1_alt_ra (fst pair) (snd pair))"
    unfolding loop1_alt_def loop1_alt_ra_def curry_def
    apply(simp add: Basic_BNF_LFPs.xtor_rel)
    apply(rule fixp_ra_parametric)
    using loop1_alt.mono 
    unfolding curry_def apply(simp)
    using loop1_alt_ra.mono 
    unfolding curry_def apply(simp)
  proof -
    have 1:" (\<lambda>loop1_alt (p, k). (case quotient_of p of (n, d) \<Rightarrow> bernoulli_rat (nat n) (nat (d * int k))) \<bind> (\<lambda>a. if a then loop1_alt (p, k + 1) else return_spmf k))
        =  (\<lambda>loop1_alt (p, k). (bernoulli_rat (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k))) \<bind> (\<lambda>a. if a then loop1_alt (p, k + 1) else return_spmf k))"
      by (simp add: split_def)
    have 2:" (\<lambda>loop1_alt_ra (p, k). (case quotient_of p of (n, d) \<Rightarrow> bernoulli_rat_ra (nat n) (nat (d * int k))) \<bind> (\<lambda>a. if a then loop1_alt_ra (p, k + 1) else return_ra k))
        =  (\<lambda>loop1_alt_ra (p, k). (bernoulli_rat_ra (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k))) \<bind> (\<lambda>a. if a then loop1_alt_ra (p, k + 1) else return_ra k))"
      by (simp add: split_def)
    have 3:"(((=) ===> rel_spmf_of_ra) ===> (=) ===> rel_spmf_of_ra)
     (\<lambda>loop1_alt (p, k). (bernoulli_rat (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k))) \<bind> (\<lambda>a. if a then loop1_alt (p, k + 1) else return_spmf k))
     (\<lambda>loop1_alt_ra (p, k). (bernoulli_rat_ra (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k))) \<bind> (\<lambda>a. if a then loop1_alt_ra (p, k + 1) else return_ra k))"
    proof-
      have 1:"bernoulli_rat (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k)) = (\<lambda>(n, d). bernoulli_rat n d) (nat (fst(quotient_of p)),nat ((snd(quotient_of p)) * int k))" by simp
      have 2:"bernoulli_rat_ra (nat (fst(quotient_of p))) (nat ((snd(quotient_of p)) * int k)) = (\<lambda>(n, d). bernoulli_rat_ra n d) (nat (fst(quotient_of p)),nat ((snd(quotient_of p)) * int k))" by simp
      have 3:"(((=) ===> rel_spmf_of_ra) ===> (=) ===> rel_spmf_of_ra)
     (\<lambda>loop1_alt (p, k). (\<lambda>(n, d). bernoulli_rat n d) (nat (fst(quotient_of p)),nat ((snd(quotient_of p)) * int k)) \<bind> (\<lambda>a. if a then loop1_alt (p, k + 1) else return_spmf k))
     (\<lambda>loop1_alt_ra (p, k). (\<lambda>(n, d). bernoulli_rat_ra n d) (nat (fst(quotient_of p)),nat ((snd(quotient_of p)) * int k))\<bind> (\<lambda>a. if a then loop1_alt_ra (p, k + 1) else return_ra k))"
        by transfer_prover
      show ?thesis using 1 2 3 by simp
    qed
    show "(((=) ===> rel_spmf_of_ra) ===> (=) ===> rel_spmf_of_ra)
     (\<lambda>loop1_alt (p, k). (case quotient_of p of (n, d) \<Rightarrow> bernoulli_rat (nat n) (nat (d * int k))) \<bind> (\<lambda>a. if a then loop1_alt (p, k + 1) else return_spmf k))
     (\<lambda>loop1_alt_ra (p, k). (case quotient_of p of (n, d) \<Rightarrow> bernoulli_rat_ra (nat n) (nat (d * int k))) \<bind> (\<lambda>a. if a then loop1_alt_ra (p, k + 1) else return_ra k)) "
      using 1 2 3 by simp
  qed
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by simp
qed

lemma bernoulli_exp_minus_rat_from_0_to_1_ra_correct:
"spmf_of_ra (bernoulli_exp_minus_rat_from_0_to_1_ra p) = bernoulli_exp_minus_rat_from_0_to_1 p"
  unfolding bernoulli_exp_minus_rat_from_0_to_1_def bernoulli_exp_minus_rat_from_0_to_1_ra_def
  by(simp add: spmf_of_ra_simps loop1_alt_ra_correct,rule bind_spmf_cong,simp_all add:spmf_of_ra_simps)

context
  includes lifting_syntax
begin

lemma bernoulli_exp_minus_rat_from_0_to_1_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) (bernoulli_exp_minus_rat_from_0_to_1) (bernoulli_exp_minus_rat_from_0_to_1_ra)"
  unfolding rel_fun_def rel_spmf_of_ra_def 
  using bernoulli_exp_minus_rat_from_0_to_1_ra_correct by auto

end

lemma loop2_alt_ra_correct:
"spmf_of_ra (loop2_alt_ra p k) = loop2_alt p k"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) (\<lambda>pair. loop2_alt (fst pair) (snd pair)) (\<lambda>pair. loop2_alt_ra (fst pair) (snd pair))"
    unfolding loop2_alt_def loop2_alt_ra_def curry_def
    apply(simp add: Basic_BNF_LFPs.xtor_rel)
    apply(rule fixp_ra_parametric)
    using loop2_alt.mono 
    unfolding curry_def apply(simp)
    using loop2_alt_ra.mono 
    unfolding curry_def apply(simp)
      by(transfer_prover)
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by simp
qed

lemma bernoulli_exp_minus_rat_ra_correct:
"spmf_of_ra (bernoulli_exp_minus_rat_ra p) = bernoulli_exp_minus_rat p"
  unfolding bernoulli_exp_minus_rat_def bernoulli_exp_minus_rat_ra_def
  by(simp add: spmf_of_ra_simps bernoulli_exp_minus_rat_from_0_to_1_ra_correct loop2_alt_ra_correct spmf_of_ra_if)

context
  includes lifting_syntax
begin

lemma bernoulli_exp_minus_rat_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) (bernoulli_exp_minus_rat) (bernoulli_exp_minus_rat_ra)"
  unfolding rel_fun_def rel_spmf_of_ra_def 
  using bernoulli_exp_minus_rat_ra_correct by auto

end

context notes [[function_internals]] begin
partial_function (random_alg) loop_ra :: "nat \<Rightarrow> nat random_alg" where
"loop_ra v = do {
              a \<leftarrow> bernoulli_exp_minus_rat_ra 1;
              if a = False then return_ra v
              else  loop_ra (v+1)
}"
end

declare loop_ra.simps[code]

context notes [[function_internals]] begin
partial_function (random_alg) discrete_laplace_rat_ra :: "nat \<Rightarrow> nat \<Rightarrow> int random_alg" where
"discrete_laplace_rat_ra t s = bind_ra 
                              (fast_uniform_ra t) 
                              (\<lambda>u. bind_ra 
                                      (bernoulli_exp_minus_rat_ra (Rat.Fract u t))
                                      (\<lambda>d. if \<not>d then (discrete_laplace_rat_ra t s)
                                           else bind_ra (loop_ra 0) (\<lambda>v. let x = u + t * v in
                                                                        let y = floor (x/s) in 
                                                                        bind_ra 
                                                                                 (bernoulli_rat_ra 1 2) 
                                                                                 (\<lambda>b. if (\<not>b \<and> (y=0)) then discrete_laplace_rat_ra t s 
                                                                                      else if b then return_ra (-y) 
                                                                                           else return_ra y ) )))
"
end

declare discrete_laplace_rat_ra.simps[code]

lemma loop_ra_correct:
"spmf_of_ra (loop_ra n) = loop n"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) loop loop_ra"
    unfolding loop_def loop_ra_def 
    apply(simp add: Basic_BNF_LFPs.xtor_rel)
    apply(rule fixp_ra_parametric)
    using loop.mono 
    unfolding curry_def apply(simp)
    using loop_ra.mono 
    unfolding curry_def apply(simp)
      by(transfer_prover)
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by simp
qed

context
  includes lifting_syntax
begin
lemma loop_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) loop loop_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def 
  using loop_ra_correct by auto
end

lemma let_2_simps: "(let x = e1;y=e2 x in e3 y) = e3 (e2 e1)"
  by simp

lemma bernoulli_rat_lambda:
"bernoulli_rat n d = (\<lambda>(n,d). bernoulli_rat n d) (n,d)"
  by simp


lemma bernoulli_rat_ra_lambda:
"bernoulli_rat_ra n d = (\<lambda>(n,d). bernoulli_rat_ra n d) (n,d)"
  by simp

lemma discrete_laplace_rat_ra_correct:
"spmf_of_ra (discrete_laplace_rat_ra t s) = discrete_laplace_rat t s"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) (\<lambda>pair. discrete_laplace_rat (fst pair) (snd pair)) (\<lambda>pair. discrete_laplace_rat_ra (fst pair) (snd pair))"
    unfolding discrete_laplace_rat_def discrete_laplace_rat_ra_def 
    apply(simp add: Basic_BNF_LFPs.xtor_rel)
    apply(rule fixp_ra_parametric)
    using discrete_laplace_rat.mono 
    unfolding curry_def apply(simp)
    using discrete_laplace_rat_ra.mono 
    unfolding curry_def apply(simp)
    by(rewrite let_2_simps,rewrite let_2_simps,rewrite bernoulli_rat_lambda, rewrite bernoulli_rat_ra_lambda, transfer_prover)
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by simp
qed

export_code discrete_laplace_rat_ra in Scala


end