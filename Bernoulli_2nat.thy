theory Bernoulli_2nat
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
begin

value "bernoulli_pmf (of_rat 1/3)"
value "bernoulli_pmf (1/3)"

value "Fract 1 (2*(1::nat))"

definition bernoulli_spmf :: "real \<Rightarrow> bool spmf" where
 "bernoulli_spmf p = do{
                      a \<leftarrow> bernoulli_pmf p;
                      return_spmf a
                      }"


context notes [[function_internals]] begin
partial_function (spmf) loop1 :: "nat \<Rightarrow> nat  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "loop1 n d k =
    (
    do {
      a \<leftarrow> bernoulli_spmf (n/(d*k));
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
value "(4::nat)/(3::nat)"
value "4/3::real"
value "floor (4/3::real)"
value "(3::nat) mod (2::nat)"

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

term "spmf (bernoulli_exp_rat (Fract 1 3)) True"
value "spmf (bernoulli_exp_rat (Fract 1 3)) True"


(*we need define fixpoint as part of  while loop*)

thm "loop1.fixp_induct"

lemma loop1_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop1. P (curry (curry loop1)))"
    and "P (\<lambda>loop1 n d. return_pmf None)"
    and "(\<And>k. P k \<Longrightarrow> P (\<lambda>a b c. bernoulli_spmf (real a / (real b * real c)) \<bind> (\<lambda>aa. if aa then k a b (c + 1) else return_spmf c)))"
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

term "fact"
term "power 2 3"
value "(power 2 3):: nat"
value "(Fract 3 2) / 2"
value " (1::nat)"
value "real_of_rat (Fract 3 2)"
term "spmf (loop1 1 2 1) 3"
value "1- (2/3::rat)"
value "(1::nat)/(2::nat)"
value "(1::nat)/((2::nat)*(3::nat))"
term "(1::nat)/(2::nat)"

context
  fixes n :: "nat"
  and d :: "nat"
  and body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (b,k'+1) else (\<not>b,k'))) (bernoulli_spmf  (n/(d*k'))))"
(*
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). do {
                                             a \<leftarrow> bernoulli_pmf (n/(d*k')); 
                                             if a then  return_spmf (b,k'+1) else return_spmf (\<not>b,k'::nat) 
                                            })"
*)
begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv>  (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (b,k'+1) else (\<not>b,k'))) (bernoulli_spmf  (n/(d*k'))))" 
  by(fact body_def)
(*
  rewrites "body \<equiv>  (\<lambda>(b,k'::nat). do {
                                             a \<leftarrow> bernoulli_pmf (n/(d*k')); 
                                             if a then  return_spmf (b,k'+1) else return_spmf (\<not>b,k'::nat) 
                                            })" 
*)

thm spmf.map_comp
thm o_def
thm bind_spmf_cong_simp
thm ord_spmf_bind_reflI
term "while"
thm "while.simps"
find_theorems name: "loop_spmf.while"
thm ""

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

lemma lossless_loop1 [simp]: "lossless_spmf (loop1 n d 1)"
proof -
  let ?body = " (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (b,k'+1) else (\<not>b,k'))) (bernoulli_spmf  (n/(d*k'))))"
  have "lossless_spmf (while (True, 1))"
  proof(rule termination_0_1_immediate_invar)
  
  
qed

end

(*
lemma lossless_geometric [simp]: "lossless_spmf (geometric_spmf p) \<longleftrightarrow> p > 0"
proof(cases "0 < p \<and> p < 1")
  case True
  let ?body = "\<lambda>(b, x :: nat). map_spmf (\<lambda>b'. (\<not> b', x + (if b' then 0 else 1))) (bernoulli p)"
  have "lossless_spmf (while (True, 0))"
  proof(rule termination_0_1_immediate)
    have "{x. x} = {True}" by auto
    then show "p \<le> spmf (map_spmf fst (?body s)) False" for s :: "bool \<times> nat" using True
      by(cases s)(simp add: spmf.map_comp o_def spmf_map vimage_def spmf_conv_measure_spmf[symmetric])
    show "0 < p" using True by simp
  qed(clarsimp)
  with True show ?thesis by(simp add: geometric_spmf_conv_while)
qed(auto simp add: spmf_geometric_nonpos spmf_geometric_ge_1)
*)


end