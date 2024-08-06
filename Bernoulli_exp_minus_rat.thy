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

(* declare[[show_types,show_sorts]]*)

term List.bind
ML \<open>@{term  "(\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f ((n, d), l)}. spmf p m)"}\<close>

thm admissible_leI[OF ccpo_spmf, cont_intro]
term spmf.lub_fun
term measure_pmf.prob
term lub_spmf

lemma spmf_loop1_zero_fixp_induct_case_adm:
  shows "spmf.admissible (\<lambda>loop1. \<forall>l>m. spmf (curry (curry loop1) n d l) m = 0)"
proof(simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf, clarify)
  fix A l
  assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
  H: "\<forall>x\<in>A.\<forall>l>m. spmf (x ((n, d), l)) m = 0" and
  L: "l>m" 
  have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f ((n, d), l)}) m =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f ((n, d), l)}. spmf p m)"
  proof(rule spmf_lub_spmf)
    show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f ((n, d), l)}" 
      by (simp add: CA chain_fun)
  next 
    show "{y. \<exists>f\<in>A. y = f ((n, d), l)} \<noteq> {}" using A by blast
  qed
  have "... =  \<Squnion>{0}"
  proof (rule cong[where f=Sup and g=Sup],simp)
    show " (\<lambda>p. spmf p m) ` {y. \<exists>f\<in>A. y = f ((n, d), l)} = {0}"
      using A H L by (auto simp add: image_def)
  qed
  also have "... = 0"
    by simp
  finally show  "spmf (lub_spmf {y. \<exists>f\<in>A. y = f ((n, d), l)}) m = 0"
    using P by presburger
qed

lemma spmf_loop1_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (loop1 n d l) m = 0"
proof (induction rule: loop1_fixp_induct)
  case adm
  then show ?case 
    using spmf_loop1_zero_fixp_induct_case_adm by fastforce
next
  case bottom
  then show ?case by simp
next
  case (step k)
  then show ?case  
  proof (clarify)
    fix l
    assume Step:"\<forall>l>m. spmf (k n d l) m = 0" and L:"l>m"
    have "ennreal (spmf (bernoulli_rat n (d * l) \<bind> (\<lambda>aa. if aa then k n d (l + 1) else return_spmf l)) m) =ennreal 0"
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
      using L Step not_less_eq option.inject order_less_imp_not_less singletonD apply(auto)
      done
    then show " \<forall>l>m. spmf (k n d l) m = 0 \<Longrightarrow> m < l \<Longrightarrow> spmf (bernoulli_rat n (d * l) \<bind> (\<lambda>aa. if aa then k n d (l + 1) else return_spmf l)) m = 0" by simp
  qed
qed

lemma Prod_sequence:
  fixes k:: nat and l:: nat
  shows "k*\<Prod>{k+1..k + l} = \<Prod>{k..k + l}"
proof -
  have "k \<le> k+l" by simp
  then have "k*\<Prod>{k+1..k + l} =k* (fact (k+l) div fact k)"
    using fact_div_fact by simp
  show ?thesis
    sorry
qed

lemma Prod_sequence2:
  shows "(k * \<Prod>{k+1..k+l+1}) = \<Prod>{k..k+l+1}"
  sorry

find_theorems "ennreal _ = ennreal _"

lemma spmf_loop1:
  assumes asm1:"n/d\<le> 1" and asm2:"1\<le>m"
  shows "spmf (loop1 n d 1) m = (n/d)^(m-1)/fact (m-1) - (n/d)^m/fact m" (is "?lhs m = ?rhs m")
proof -
  have P:"\<forall>k l::nat . 1\<le>k \<longrightarrow> ennreal (spmf (loop1 n d k) (k+l)) = (n/d)^l /\<Prod>{k..(k+l-1)} - (n/d)^(l+1)/\<Prod>{k..(k+l)}"
  proof (clarify)
    fix l
    show "\<And>k.1 \<le> k \<Longrightarrow>
           ennreal (spmf (loop1 n d k) (k + l)) =
           ennreal ((real n / real d) ^ l / real (\<Prod>{k..k + l - 1}) - (real n / real d) ^ (l + 1) / real (\<Prod>{k..k + l}))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have "ennreal (spmf (loop1 n d k) (k + 0)) = ennreal (spmf (bernoulli_rat n (d * k)) False) + ennreal (spmf (bernoulli_rat n (d * k)) True) * ennreal (spmf (loop1 n d (k+1)) k)"
          apply(rewrite loop1.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal (1-n/(d*k))"
          proof - 
            have n_divide_dK: "n/(d*k)\<le>1" using 0 
              by (smt (verit) Multiseries_Expansion.intyness_1 Num.of_nat_simps(5) assms(1) divide_divide_eq_left divide_le_eq_1_pos of_nat_le_iff)
            then show "ennreal (spmf (bernoulli_rat n (d * k)) False) + ennreal (spmf (bernoulli_rat n (d * k)) True) * ennreal (spmf (loop1 n d (k + 1)) k) =  ennreal (1-n/(d*k))"
              using spmf_loop1_zero by simp
          qed
        also have "... = ennreal ((n/d)^0/\<Prod>{k..k+0-1} - (n/d)^(0+1)/\<Prod>{k..k + 0})" 
          proof - 
            have "k-1 < k" using 0 by simp
            then have "{k..k+0-1} = {}" by simp
            then show "ennreal (1-n/(d*k)) = ennreal ((n/d)^0/\<Prod>{k..k+0-1} - (n/d)^(0+1)/\<Prod>{k..k + 0})"
              by simp
          qed
        finally show "ennreal (spmf (loop1 n d k) (k + 0)) = ennreal ((n/d)^0/\<Prod>{k..k+0-1} - (n/d)^(0+1)/\<Prod>{k..k + 0})" by simp
      qed 
    next
      case (Suc l)
      then show ?case
      proof - 
          assume step:"\<And>k. 1 \<le> k \<Longrightarrow>
          ennreal (spmf (loop1 n d k) (k + l)) =
          ennreal ((n/d)^l/\<Prod>{k..k+l-1} - (n/d)^(l+1)/\<Prod>{k..k + l})"
            and K: "1\<le>k"
          have "ennreal (spmf (loop1 n d k) (k + Suc l)) = ennreal ((spmf (bernoulli_rat n (d * k)) True) * (spmf (loop1 n d (k+1)) (k+l+1)))"
            apply(rewrite loop1.simps)
            apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite ennreal_mult)
            done
          also have "... = ennreal ((n/d)^(l+1) / \<Prod>{k..k+l} - (n/d)^(l+2) / \<Prod>{k..k+l+1})"
          proof -
            have n_divide_dK: "n/(d*k)\<le>1" using K
              by (smt (verit) Multiseries_Expansion.intyness_1 Num.of_nat_simps(5) assms(1) divide_divide_eq_left divide_le_eq_1_pos of_nat_le_iff) 
            then have Bernoulli:"ennreal (spmf (bernoulli_rat n (d * k)) True) = n/(d*k)" by simp
            have H:"ennreal (spmf (loop1 n d (k+1)) (k+l+1)) = ennreal ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1})" 
              using step 
              by (metis diff_add_inverse2 le_add2 semiring_norm(163) semiring_norm(174))
            have "ennreal (spmf (bernoulli_rat n (d * k)) True * spmf (loop1 n d (k + 1)) (k + l + 1))=ennreal (spmf (bernoulli_rat n (d * k)) True) *ennreal (spmf (loop1 n d (k + 1)) (k + l + 1))"
              by(simp add: ennreal_mult)
            also have "...=ennreal (n/(d*k)) * ennreal ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1})"
              apply(rewrite Bernoulli)
              apply(rewrite H)
              apply(simp)
              done
            also have "... = ennreal ( ((n/d)^(l+1)/\<Prod>{k..k+l} - (n/d)^(l+2)/\<Prod>{k..k+l+1}))"
            proof - 
              have "(n/(d*k)) * ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1}) =  (n/d)^(l+1)/(\<Prod>{k..k+l}) - (n/d)^(l+2)/(\<Prod>{k..k+l+1})"
              proof -
                have "(n/(d*k)) * ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1}) = 1/k*(n/d) * ((n/d)^(l)/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1})"
                  by simp
                also have "... = 1/k* ((n/d)*(n/d)^(l)/\<Prod>{k+1..k+l} - (n/d)*(n/d)^(l+1)/\<Prod>{k+1..k+l+1})" 
                  by argo
                also have "... =  1/k* ((n/d)^(l+1)/\<Prod>{k+1..k+l} - (n/d)^(l+2)/\<Prod>{k+1..k+l+1})" by simp
                also have "... =  1/k*(n/d)^(l+1)/\<Prod>{k+1..k+l} - 1/k*(n/d)^(l+2)/\<Prod>{k+1..k+l+1}" by argo
                also have "... = (n/d)^(l+1)/(k*\<Prod>{k+1..k+l}) - (n/d)^(l+2)/(k*\<Prod>{k+1..k+l+1})" 
                  by (metis Num.of_nat_simps(5) arithmetic_simps(78) divide_divide_eq_left times_divide_eq_left)
                also have "... = (n/d)^(l+1)/(\<Prod>{k..k+l}) - (n/d)^(l+2)/(\<Prod>{k..k+l+1})"
                  apply(rewrite Prod_sequence)
                  apply(rewrite Prod_sequence2)
                  apply(simp)
                  done
                finally show "(n/(d*k)) * ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1}) = (n/d)^(l+1)/(\<Prod>{k..k+l}) - (n/d)^(l+2)/(\<Prod>{k..k+l+1})"
                  by simp
              qed
              then show "ennreal (n/(d*k)) * ennreal ((n/d)^l/\<Prod>{k+1..k+l} - (n/d)^(l+1)/\<Prod>{k+1..k+l+1}) = ennreal ( (n/d)^(l+1)/(\<Prod>{k..k+l}) - (n/d)^(l+2)/(\<Prod>{k..k+l+1}))"
                by (smt (verit, del_insts) ennreal_mult' of_nat_0_le_iff real_of_nat_div4)
            qed
            finally show "ennreal (spmf (bernoulli_rat n (d * k)) True * spmf (loop1 n d (k + 1)) (k + l + 1))
                          = ennreal ( (n/d)^(l+1)/(\<Prod>{k..k+l}) - (n/d)^(l+2)/(\<Prod>{k..k+l+1}))"
              by simp
          qed
          also have "ennreal ((n/d)^(l+1) / \<Prod>{k..k+l} - (n/d)^(l+2) / \<Prod>{k..k+l+1}) = ennreal ((n/d)^Suc l/\<Prod>{k..k + Suc l - 1} - (n/d)^(Suc l+1)/\<Prod>{k..k + Suc l})"
          proof -
            have 1:"l+1=Suc l" by simp
            have 2:"k+l = k+ Suc l -1" by simp
            have 3:"l+2 = Suc l + 1" by simp
            have 4:"k+l+1 = k+ Suc l" by simp
            show "ennreal ((n/d)^(l+1) / \<Prod>{k..k+l} - (n/d)^(l+2) / \<Prod>{k..k+l+1}) = ennreal ((n/d)^Suc l/\<Prod>{k..k + Suc l - 1} - (n/d)^(Suc l+1)/\<Prod>{k..k + Suc l})"
              using 1 2 3 4 by simp
          qed
          finally show "ennreal (spmf (loop1 n d k) (k + Suc l)) = ennreal ((n/d)^Suc l/\<Prod>{k..k+Suc l-1} - (n/d)^(Suc l+1)/\<Prod>{k..k+Suc l})"
            by simp
      qed
    qed
  qed
  then have ennreal_eq:"ennreal (spmf (loop1 n d 1) m) = ennreal ((n/d)^(m-1)/(fact (m-1)) - (n/d)^m/(fact (m)))" 
  proof - 
    have "ennreal (spmf (loop1 n d 1) m) = ennreal (spmf (loop1 n d 1) (1+(m-1)))" using asm2 by simp
    also have "... = (n/d)^(m-1) /\<Prod>{1..1+(m-1)-1} - (n/d)^(m-1+1)/\<Prod>{1..1+(m-1)}" using P
    proof -
      have "(1::nat)\<le>1" by simp 
      then show "ennreal (spmf (loop1 n d 1) (1 + (m - 1))) =
                 ennreal ( (n/d)^(m-1) /\<Prod>{1..1+(m-1)-1} - (n/d)^(m-1+1)/\<Prod>{1..1+(m-1)})"
        apply(rewrite P)
         apply(simp_all)
        done
    qed
    also have "... =  (n/d)^(m-1) /\<Prod>{1..m-1} - (n/d)^(m)/\<Prod>{1..m}" using assms by simp
    also have "... = (n/d)^(m-1) /fact (m-1) - (n/d)^(m)/fact m" by (simp add:fact_prod)
    finally show "ennreal (spmf (loop1 n d 1) m) = ennreal ((n/d)^(m-1)/(fact (m-1)) - (n/d)^m/(fact (m)))" by simp
  qed
  then show "spmf (loop1 n d 1) m = (n/d)^(m-1)/fact (m-1) - (n/d)^m/fact m"
  proof - 
    have 1:"0 \<le> spmf (loop1 n d 1) m" by simp
    then have 2:"0 \<le> (n/d)^(m-1)/fact (m-1) - (n/d)^m/fact m" 
    proof -
      have 1:"(n/d)^m \<le> (n/d)^(m-1)" 
        apply(rewrite power_decreasing)
        apply(simp_all add:assms) 
        done
      have 2:"fact(m-1) \<le> fact m"
      proof -
        have "m-1\<le>m" by simp
        then show "fact (m-1) \<le> fact m"
          sorry
      qed
      find_theorems "0 < fact _"
      have 3: "0 < fact (m-1)" 
        sorry
      have "(n/d)^m/fact m \<le> (n/d)^(m-1)/fact (m-1) " using 1 2 3 
        sorry
      then show "0 \<le> (n/d)^(m-1)/fact (m-1) - (n/d)^m/fact m" by simp
    qed
    show "spmf (loop1 n d 1) m = (n/d)^(m-1)/fact (m-1) - (n/d)^m/fact m" using 1 2 ennreal_eq by simp
  qed
qed

lemma lossless_bernoulli_exp_minus_rat_from_0_to_1 [simp]:
  shows "lossless_spmf (bernoulli_exp_minus_rat_from_0_to_1 n d)"
  using lossless_loop1 by(simp add: bernoulli_exp_minus_rat_from_0_to_1_def)

find_theorems "inverse"

lemma spmf_bernoulli_exp_minus_rat_from_0_to_1_True[simp]:
  assumes  "n \<le> d"
  shows "spmf (bernoulli_exp_minus_rat_from_0_to_1 n d) True = exp(-n/d) "
proof -
  have "ennreal (spmf (bernoulli_exp_minus_rat_from_0_to_1 n d) True) = exp(-n/d)"
    apply(simp add:bernoulli_exp_minus_rat_from_0_to_1_def ennreal_spmf_bind nn_integral_measure_spmf exp_def inverse_eq_divide)
  proof -
    have "\<forall>x. spmf (if odd x then return_spmf True else return_spmf False) True 
          = (if odd x then 1 else 0)"
    proof 
      show "\<And>x. spmf (if odd x then return_spmf True else return_spmf False) True 
          = (if odd x then 1 else 0 )"
        using spmf_return_spmf_0 spmf_return_spmf_1 by presburger
    qed
    then have " (\<Sum>\<^sup>+ x. ennreal (spmf (loop1 n d 1) x) * ennreal (spmf (if odd x then return_spmf True else return_spmf False) True))
                = (\<Sum>\<^sup>+ x. ennreal (spmf (loop1 n d 1) x) *  (if odd x then 1 else 0))"
      by (smt (verit, best) ennreal_0 ennreal_1 nn_integral_cong)
    have "... = (\<Sum>\<^sup>+ x. (if odd x then spmf (loop1 n d 1) x  else 0))" 
      by (smt (verit, ccfv_threshold) ennreal_0 mult_zero_right nn_integral_cong verit_prod_simplify(2))
    have "... = (\<Sum>\<^sup>+x \<in>{y\<in>Nats. odd y}. (spmf (loop1 n d 1) x)) "
      sledgehammer
      sorry
    have "... = (\<Sum>\<^sup>+x. (spmf (loop1 n d 1) (2*x+1)))"
      sorry
    show "(\<Sum>\<^sup>+ x.
       ennreal (spmf (loop1 n d (Suc 0)) x) *
       ennreal (spmf (if odd x then return_spmf True else return_spmf False) True)) =
    ennreal (\<Sum>na. (- (real n / real d)) ^ na/fact na)"
      sorry
  qed
  then show ?thesis sorry
qed


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