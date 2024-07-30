theory Bernoulli_exp_minus_rat
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
          "Bernoulli_rat"
begin





context notes [[function_internals]] begin
partial_function (spmf) loop1 :: "nat \<Rightarrow> nat  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "loop1 n d k =
    (
    do {
      a \<leftarrow> bernoulli_rat n (d*k);
      if a then loop1 n d (k+1) else return_spmf k
    }
)
"
end

definition  bernoulli_exp_minus_rat_from_0_to_1 :: "nat \<Rightarrow> nat \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat_from_0_to_1 n d = 
    do {
        k \<leftarrow> loop1 n d 1;
        if odd k then return_spmf True else return_spmf False
    }
  "

context notes [[function_internals]] begin
partial_function (spmf) loop2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool spmf" where
  "loop2 n d k = (if 1\<le>k & k\<le> (floor (n/d)) then do {
                                              b \<leftarrow> bernoulli_exp_minus_rat_from_0_to_1 1 1;
                                              if b then loop2 n d (k+1) else return_spmf False
                                              } 
                else return_spmf True)"
end

definition bernoulli_exp_minus_rat :: "nat \<Rightarrow> nat  \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_rat n d = 
  (
    if 0 \<le> n & n\<le> d then bernoulli_exp_minus_rat_from_0_to_1 n d
    else
     do {
        b \<leftarrow> loop2 n d 1;
        if b then bernoulli_exp_minus_rat_from_0_to_1 (n mod d) d else return_spmf b
      }
  )
"

thm "loop1.fixp_induct"

lemma loop1_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop1. P (curry (curry loop1)))"
    and "P (\<lambda>loop1 n d. return_pmf None)"
    and "(\<And>k. P k \<Longrightarrow> P (\<lambda>a b c. bernoulli_rat a (b*c) \<bind> (\<lambda>aa. if aa then k a b (c + 1) else return_spmf c)))"
  shows "P loop1"
  using assms by (rule loop1.fixp_induct)

thm "loop2.fixp_induct"

lemma loop2_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop2. P (curry (curry loop2)))"
    and "P (\<lambda>loop2 n d. return_pmf None)"
    and "(\<And>k. P k \<Longrightarrow>
      P (\<lambda>a b c.
             if 1 \<le> c \<and> int c \<le> \<lfloor>real a / real b\<rfloor> then bernoulli_exp_minus_rat_from_0_to_1 1 1 \<bind> (\<lambda>ba. if ba then k a b (c + 1) else return_spmf False)
             else return_spmf True))"
  shows "P loop2"
  using assms by (rule loop2.fixp_induct)

context
  fixes n :: "nat"
  and d :: "nat"
  and body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
  assumes cond1:"d \<ge> 1" and cond2:"n \<le> d"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_rat  n (d*k')))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv>  (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_rat  n (d*k')))" 
  by(fact body_def)

lemma loop1_conv_while:
 "loop1 n d 1 = map_spmf snd (while (True, 1))"
proof -
  have "(loop1 n d x) = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule: loop1_fixp_induct)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step loop1')
      show ?case using step.IH[of "Suc x"]
        apply(rewrite while.simps)
        apply(clarsimp)
        apply(clarsimp simp add: map_spmf_bind_spmf)
        apply(clarsimp simp add:bind_map_spmf)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        apply(rewrite loop_spmf.while.simps)
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
        by(rewrite loop1.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

end

lemma lossless_loop1 [simp]: "lossless_spmf (loop1 n d 1)"
  sorry
(*
proof -
  let ?body = " (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_spmf  (n/(d*k'))))"
  have loop1:"lossless_spmf (while (True, k))"
    if k1: "n < d * k" and k2: "1 \<le> k"
    for k
  proof(rule termination_0_1_immediate; clarify?)
    have condi1:"0 \<le> real n / (real d * real k)" using k1 k2 by auto
    have condi2:"real n / (real d * real k) < 1" using k1 k2 
      by (smt (verit) divide_less_eq_1 less_imp_of_nat_less of_nat_less_0_iff of_nat_mult)
    show goal2: "0 < 1-(n/d)" using condi2 by 
    have "1-(n/d)\<le>  spmf (map_spmf fst (map_spmf (\<lambda>b'. (if b' then (True,k+1) else (False,k))) (bernoulli_spmf  (n/(d*k))))) False" 
    proof -
      have eq1: "spmf (map_spmf fst (map_spmf (\<lambda>b'. (if b' then (True,k+1) else (False,k))) (bernoulli_spmf  (n/(d*k))))) False = spmf (map_spmf fst (?body (True,k))) False"  by simp
      have leq4:"1-(n/d) \<le> spmf (map_spmf fst (map_spmf (\<lambda>b'. (if b' then (True,k+1) else (False,k))) (bernoulli_spmf  (n/(d*k))))) False" using cond1 cond2
        apply(simp add: spmf.map_comp)
        apply(simp add: o_def)
        apply(simp add: bernoulli_spmf_def)
        done
      show ?thesis using eq1 leq4 by auto
*)

thm "spmf_bind"
thm "spmf_ub_tight"
term "fact 1" 
value "fact 0::nat"
find_theorems "frac "

lemma loop1_a [simp]:
  assumes "l > m"
  shows "spmf (loop1 n d l) m = 0"
  sorry


lemma spmf_loop1:
  assumes asm1:"n/d\<le> 1" and asm2:"1\<le>m"
  shows "spmf (loop1 n d 1) m = (n/d)^(m-1)/(fact (m-1)) - (n/d)^m/(fact (m))" (is "?lhs m = ?rhs m")
(*
proof (rule spmf_ub_tight)
  fix m
  have "ennreal (?lhs m) \<le> ennreal (?rhs m)" using assms
  proof(induction arbitrary: m rule:loop1_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step loop1')
    then show ?case
    proof(cases "m=1")
      case True
      have "Suc (Suc 0) > Suc 0" by simp
      then show ?thesis using assms True
        apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        apply(simp add: UNIV_bool)
        apply(simp add: nn_integral_count_space_finite)
*)
 sorry



lemma lossless_bernoulli_exp_minus_rat_from_0_to_1 [simp]:
  shows "lossless_spmf (bernoulli_exp_minus_rat_from_0_to_1 n d)"
  using lossless_loop1 by(simp add: bernoulli_exp_minus_rat_from_0_to_1_def)
  

lemma spmf_bernoulli_exp_minus_rat_from_0_to_1_True[simp]:
  assumes  "n \<le> d"
  shows "spmf (bernoulli_exp_minus_rat_from_0_to_1 n d) True = exp(-n/d) "
  sorry

lemma spmf_bernoulli_exp_minus_rat_from_0_to_1_False[simp]:
  assumes  "n\<le>d"
  shows "spmf (bernoulli_exp_minus_rat_from_0_to_1 n d) False =  1 - exp(-n/d)" 
  using assms by(simp add:spmf_False_conv_True)

context
  fixes n :: "nat"
  and d :: "nat"
  and body :: "bool \<Rightarrow> bool spmf"
  assumes cond1:"d \<ge> 1" and cond2:"n \<le> d"
defines [simp]: "body \<equiv> (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_rat_from_0_to_1 1 1))"

begin
interpretation loop_spmf id body 
  rewrites "body \<equiv>  (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_rat_from_0_to_1 1 1))"
  by(fact body_def)


lemma loop2_conv_iter:
  shows "loop2 n d 1 = iter (nat (floor (n/d))) True"
  sorry

end

lemma lossless_loop2 [simp]:
  shows "lossless_spmf (loop2 n d 1)"
  sorry

thm "spmf_False_conv_True"

lemma spmf_loop2_True [simp]: 
  assumes "1\<le>d" "d < n"
  shows "spmf (loop2 n d 1) True = exp(-floor(n/d))"
  sorry
lemma spmf_loop2_False [simp]:
  assumes "1\<le>d" "d<n"
  shows "spmf (loop2 n d 1) False = 1 - exp(-floor(n/d))"
  by (metis One_nat_def lossless_loop2 of_int_minus spmf_False_conv_True spmf_loop2_True)

lemma lossless_bernoulli_exp_minus_rat[simp]:
  shows "lossless_spmf (bernoulli_exp_minus_rat n d)"
  using lossless_loop2 by(simp add:bernoulli_exp_minus_rat_def)


lemma spmf_bernoulli_exp_minus_rat_True[simp]:
  shows "spmf (bernoulli_exp_minus_rat n d) True = exp(-n/d)"
  apply(simp add: bernoulli_exp_minus_rat_def)
  sorry

lemma spmf_bernoulli_exp_minus_rat_False[simp]:
  shows "spmf (bernoulli_exp_minus_rat n d) False = 1-exp(-n/d)"
  by(simp add:spmf_False_conv_True)







end