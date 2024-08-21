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
       a \<leftarrow> bernoulli (of_rat p / real k) ;
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

lemma test: 
  fixes p::rat and k::nat
  assumes "0\<le>p"
  shows "(let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) = (bernoulli (of_rat p/k))"
proof-
  have 1:"spmf (let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) True = spmf (bernoulli (of_rat p/k)) True"
    apply(simp)
    sorry
  have 2:"spmf (let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) False = spmf (bernoulli (of_rat p/k)) False"
    sorry
  have "\<And> i. spmf (let (n,d) = quotient_of p in bernoulli_rat (nat n) (nat (d*k))) i = spmf (bernoulli (of_rat p/k)) i" using 1 2 by (rule bool.induct)
  then show ?thesis by (rule spmf_eqI)
qed

lemma loop1_alt_eq_loop1:
  fixes p::rat
  assumes "0\<le>p"
  shows "loop1_alt p 1 = loop1 (of_rat p) 1"
  apply(rewrite loop1_alt_def)
  apply(rewrite loop1_def)
  sorry
lemma bernoulli_exp_minus_rat_eq_bernoulli_exp_minus_real:
  fixes p::rat
  assumes "0\<le>p"
  shows "bernoulli_exp_minus_rat p = bernoulli_exp_minus_real (of_rat p)"
  sorry

end