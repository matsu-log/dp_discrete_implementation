theory Bernoulli_exp_minus_real
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
          "Probabilistic_While.Bernoulli"
begin





context notes [[function_internals]] begin
partial_function (spmf) loop1 :: "real  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "loop1 p k =
    (
    do {
      a \<leftarrow> bernoulli (p/k);
      if a then loop1 p (k+1) else return_spmf k
    }
)
"
end

definition  bernoulli_exp_minus_real_from_0_to_1 :: "real \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_real_from_0_to_1 p = 
    do {
        k \<leftarrow> loop1 p 1;
        if odd k then return_spmf True else return_spmf False
    }
  "

context notes [[function_internals]] begin
partial_function (spmf) loop2 :: "real \<Rightarrow> nat \<Rightarrow> bool spmf" where
  "loop2 p k = (if 1\<le>k & k\<le> nat(floor p) then do {
                                              b \<leftarrow> bernoulli_exp_minus_real_from_0_to_1 1;
                                              if b then loop2 p (k+1) else return_spmf False
                                              } 
                else return_spmf True)"
end



definition bernoulli_exp_minus_real :: "real  \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_real p = 
  (
    if p < 0 then return_spmf True  
    else if 0 \<le> p & p\<le>1  then bernoulli_exp_minus_real_from_0_to_1 p
    else
     do {
        b \<leftarrow> loop2 p 1;
        if b then bernoulli_exp_minus_real_from_0_to_1 (p-floor p) else return_spmf b
      }
  )
"

thm "loop1.fixp_induct"

lemma loop1_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop1. P (curry loop1))"
    and "P (\<lambda>loop1 p. return_pmf None)"
    and "(\<And>loop1'. P loop1' \<Longrightarrow> P (\<lambda>a b. bernoulli (a / b) \<bind> (\<lambda>aa. if aa then loop1' a (b + 1) else return_spmf b)))"
  shows "P loop1"
  using assms by (rule loop1.fixp_induct)

thm "loop2.fixp_induct"

lemma loop2_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>loop2. P (curry loop2))"
    and "P (\<lambda>loop2 p. return_pmf None)"
    and "(\<And>loop2'. P loop2' \<Longrightarrow>
      P (\<lambda>a b. if 1 \<le> b \<and> b \<le> nat \<lfloor>a\<rfloor>
                then bernoulli_exp_minus_real_from_0_to_1 1 \<bind> (\<lambda>ba. if ba then loop2' a (b + 1) else return_spmf False)
                else return_spmf True))"
  shows "P loop2"
  using assms by (rule loop2.fixp_induct)

context
  fixes p :: "real"
  and body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
  assumes cond1:"0\<le>p" and cond2:"p\<le>1"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli  (p/k')))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv>  (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli (p/k')))" 
  by(fact body_def)

lemma loop1_conv_while:
 "loop1 p 1 = map_spmf snd (while (True, 1))"
proof -
  have "(loop1 p x) = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
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
        by(rewrite loop1.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

lemma lossless_loop1 [simp]: "lossless_spmf (loop1 p 1)"
proof-
  let ?body = "(\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli (p/k')))" 
  have "lossless_spmf (while (True, 1))"
  proof - 
    let ?I = "\<lambda>(b,k'::nat). 2\<le>k'"
    let ?p = "1-p/2"
    have lossless_over_2:"lossless_spmf (while (True, 2))"
    proof(rule termination_0_1_immediate_invar)
      show "\<And>s. fst s \<Longrightarrow> ?I s \<Longrightarrow> ?p \<le> spmf (map_spmf fst (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (p / real k')))) False"
      proof clarify
        fix a::bool and  b::nat
        assume "fst (a,b)" and I_b:"2\<le>b"
        show "1 - p / 2 \<le> spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (p / real b)))) False"
        proof -
          have "ennreal (1-p/2)\<le> ennreal (spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (p / real b)))) False)"
          apply(simp add: ennreal_spmf_map_conv_nn_integral)
          apply(simp add: nn_integral_measure_spmf)
          apply(simp add: UNIV_bool)               
          apply(simp add: nn_integral_count_space_finite)
          proof-
            have "{a.\<not>a} = {False}" by auto
            then have "(\<Sum>a | \<not> a. spmf (bernoulli (p /b)) a) = spmf (bernoulli (p/b)) False " by simp
            also have "... = 1 - p/b" using cond1 cond2 I_b by simp
            also have "...  \<ge>  1-p/2" using I_b cond1 
            proof-
              find_theorems "_/_\<le>_/_"
              have "p/b \<le>p/2" 
                apply(rule divide_left_mono)
                using cond1 I_b apply(simp_all)
                done
              then show "1-p/2 \<le> 1-p/b" by simp
            qed
            finally have 1:"(\<Sum>a | \<not> a. spmf (bernoulli (p /b)) a) \<ge> 1-p/2" by simp
            have 2:"0\<le>1-p/2" using cond2 by simp
            show " ennreal (1 - p / 2) \<le> ennreal (\<Sum>a | \<not> a. spmf (bernoulli (p / real b)) a)" using 1 2 by simp
          qed
          then show "1 - p / 2 \<le> spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (p / real b)))) False" by simp
        qed
      qed
      show "0<?p" using cond2 by simp
      show "\<And>s. fst s \<Longrightarrow> ?I s \<Longrightarrow> lossless_spmf (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (p / real k')))" 
      proof clarify
        fix a::bool and b::nat
        assume "fst (a,b)" and "2\<le>b"
        show "lossless_spmf (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (p / real b))) " by simp
      qed
      show "\<And>s s'. s' \<in> set_spmf (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (p / real k'))) \<Longrightarrow> ?I s \<Longrightarrow> fst s \<Longrightarrow> ?I s'"
      proof clarify
        fix a aa::bool and b ba::nat
        assume step:" (aa, ba) \<in> set_spmf (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (p / real b)))"
           and I_b:"2\<le>b" and guard:"fst(a,b)"
        show "2\<le>ba" 
        proof -
          have "b\<le>ba" using step by auto
          then show "2\<le>ba" using I_b by simp
        qed
      qed
      show "?I (True,2)" using cond2 by simp
    qed
    have lossless_False_1: "lossless_spmf (while (False,1))" 
      apply(rewrite while.simps)
      apply(simp)
      done
    show "lossless_spmf (while (True,1))"
      apply(rewrite while.simps)
      apply(simp add:bind_map_spmf)
    proof 
      fix x
      assume "x \<in> set_spmf (bernoulli p)"
      show "(x \<longrightarrow> lossless_spmf (local.while (True, Suc (Suc 0)))) \<and> (\<not> x \<longrightarrow> lossless_spmf (local.while (False, Suc 0)))"
      proof 
        show "x \<longrightarrow> lossless_spmf (local.while (True, Suc (Suc 0)))"
          using lossless_over_2 by (simp add: numeral_2_eq_2)
        show " \<not> x \<longrightarrow> lossless_spmf (local.while (False, Suc 0))"
          using lossless_False_1 by simp
      qed
    qed
  qed
  then show "lossless_spmf (loop1 p 1)" 
    using loop1_conv_while by simp
qed
 
    
  


end
(* declare[[show_types,show_sorts]]*)

term List.bind
ML \<open>@{term  "(\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f ((n, d), l)}. spmf p m)"}\<close>

thm admissible_leI[OF ccpo_spmf, cont_intro]
term spmf.lub_fun
term measure_pmf.prob
term lub_spmf

lemma spmf_loop1_zero_fixp_induct_case_adm:
  shows "spmf.admissible (\<lambda>loop1. \<forall>l>m. spmf ((curry loop1) p l) m = 0)"
proof(simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf, clarify)
  fix A l
  assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
  H: "\<forall>x\<in>A.\<forall>l>m. spmf (x (p, l)) m = 0" and
  L: "l>m" 
  have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f (p, l)}) m =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f (p, l)}. spmf p m)"
  proof(rule spmf_lub_spmf)
    show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f (p, l)}" 
      by (simp add: CA chain_fun)
  next 
    show "{y. \<exists>f\<in>A. y = f (p, l)} \<noteq> {}" using A by blast
  qed
  have "... =  \<Squnion>{0}"
  proof (rule cong[where f=Sup and g=Sup],simp)
    show " (\<lambda>p. spmf p m) ` {y. \<exists>f\<in>A. y = f (p, l)} = {0}"
      using A H L by (auto simp add: image_def)
  qed
  also have "... = 0"
    by simp
  finally show  "spmf (lub_spmf {y. \<exists>f\<in>A. y = f (p, l)}) m = 0"
    using P by presburger
qed

lemma spmf_loop1_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (loop1 p l) m = 0"
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
    assume Step:"\<forall>l>m. spmf (k p l) m = 0" and L:"l>m"
    have "ennreal (spmf (bernoulli (p/l) \<bind> (\<lambda>aa. if aa then k p (l + 1) else return_spmf l)) m) = ennreal 0"
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
      using L Step not_less_eq option.inject order_less_imp_not_less singletonD apply(auto)
      done
    then show " \<forall>l>m. spmf (k p l) m = 0 \<Longrightarrow> m < l \<Longrightarrow> spmf (bernoulli (p/l) \<bind> (\<lambda>aa. if aa then k p (l + 1) else return_spmf l)) m = 0" by simp
  qed
qed

lemma Prod_sequence:
  fixes k:: nat and l:: nat
  shows "k*\<Prod>{k+1..k + l} = \<Prod>{k..k + l}"
proof -
  have "{k..k+l} = {k} \<union> {k+1..k+l}"
    by auto
  then show ?thesis by simp
qed

lemma Prod_sequence2:
  fixes k::nat and l::nat
  shows "(k * \<Prod>{k+1..k+l+1}) = \<Prod>{k..k+l+1}"
proof-
  have "{k..k+l+1} = {k} \<union> {k+1..k+l+1}" by auto
  then show ?thesis by simp
qed

lemma Prod_sequence_eq_fact_divide:
  fixes k::nat and l::nat
  shows "\<Prod>{k+1..k+l}=fact (k+l)/ fact k"
proof-
  have "\<Prod>{1..k+l}=\<Prod>{1..k}*\<Prod>{k+1..k+l}" 
  proof -
    have "{1..k+l} = {1..k}\<union>{k+1..k+l}" by auto
    then show "\<Prod>{1..k+l}=\<Prod>{1..k}*\<Prod>{k+1..k+l}" 
      using le_add2 prod.ub_add_nat by blast
  qed
  then have "\<Prod>{k+1..k+l} = \<Prod>{1..k+l}/\<Prod>{1..k}" by auto
  then show "\<Prod>{k+1..k+l} = fact (k+l)/fact k"
    apply(rewrite fact_prod[of "k"]) 
    apply(rewrite fact_prod[of "k+l"]) 
    by simp
qed

find_theorems "ennreal _ = ennreal _"
find_theorems "fact _ \<le> fact _"


lemma spmf_loop1[simp]:
  assumes asm1:"0\<le>p" "p\<le> 1" and asm2:"1\<le>m"
  shows "spmf (loop1 p 1) m = p^(m-1)/fact (m-1) - p^m/fact m" (is "?lhs m = ?rhs m")
proof -
  have P:"\<forall>k l::nat . 1\<le>k \<longrightarrow> ennreal (spmf (loop1 p k) (k+l)) = p^l /\<Prod>{k..(k+l-1)} - p^(l+1)/\<Prod>{k..(k+l)}"
  proof rule+
    fix l
    show "\<And>k.1 \<le> k \<Longrightarrow>
           ennreal (spmf (loop1 p k) (k + l)) =
           ennreal (p^l /(\<Prod>{k..k + l - 1}) - p^(l+1)/(\<Prod>{k..k + l}))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have "ennreal (spmf (loop1 p k) (k + 0)) = ennreal (spmf (bernoulli (p/k)) False) + ennreal (spmf (bernoulli (p/k)) True) * ennreal (spmf (loop1 p (k+1)) k)"
          apply(rewrite loop1.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal (1-(p/k))"
          proof - 
            have p_divide_k_0_1: "p/k\<le>1" "0\<le>p/k"using asm1 0 by auto
            then show "ennreal (spmf (bernoulli (p/k)) False) + ennreal (spmf (bernoulli (p/k)) True) * ennreal (spmf (loop1 p (k + 1)) k) =  ennreal (1-(p/k))"
              using spmf_loop1_zero by simp
          qed
        also have "... = ennreal (p^0/\<Prod>{k..k+0-1} - p^(0+1)/\<Prod>{k..k + 0})" 
          proof - 
            have "k-1 < k" using 0 by simp
            then have "{k..k+0-1} = {}" by simp
            then show "ennreal (1-(p/k)) = ennreal (p^0/\<Prod>{k..k+0-1} - p^(0+1)/\<Prod>{k..k + 0})"
              by simp
          qed
        finally show "ennreal (spmf (loop1 p k) (k + 0)) = ennreal (p^0/\<Prod>{k..k+0-1} - p^(0+1)/\<Prod>{k..k + 0})" by simp
      qed 
    next
      case (Suc l)
      then show ?case
      proof - 
          assume step:"\<And>k. 1 \<le> k \<Longrightarrow>
          ennreal (spmf (loop1 p k) (k + l)) =
          ennreal (p^l/\<Prod>{k..k+l-1} - p^(l+1)/\<Prod>{k..k + l})"
            and K: "1\<le>k"
          have "ennreal (spmf (loop1 p k) (k + Suc l)) = ennreal ((spmf (bernoulli (p/k)) True) * (spmf (loop1 p (k+1)) (k+l+1)))"
            apply(rewrite loop1.simps)
            apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite ennreal_mult)
            done
          also have "... = ennreal (p^(l+1) / \<Prod>{k..k+l} - p^(l+2) / \<Prod>{k..k+l+1})"
          proof -
            have n_divide_p_0_1: "0\<le> p/k" "p/k\<le>1" using K asm1 by auto
            then have Bernoulli:"ennreal (spmf (bernoulli  (p/k)) True) = p/k" by simp
            have H:"ennreal (spmf (loop1 p (k+1)) (k+1+l)) = ennreal (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})" 
              apply (rewrite step)
              apply(simp_all)
              done
            have "ennreal (spmf (bernoulli (p/k)) True * spmf (loop1 p (k + 1)) (k + l + 1))=ennreal (spmf (bernoulli (p/k)) True) *ennreal (spmf (loop1 p (k + 1)) (k + 1 + l))"
              by(simp add: ennreal_mult)
            also have "...=ennreal (p/k) * ennreal (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})"
              apply(rewrite Bernoulli)
              apply(rewrite H)
              apply(simp)
              done
            also have "... = ennreal ((p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1}))"
              using ennreal_mult' n_divide_p_0_1(1) by presburger
            also have "... = ennreal ( (p^(l+1)/\<Prod>{k..k+l} - p^(l+2)/\<Prod>{k..k+l+1}))"
            proof - 
              have eq1:"(p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1}) =  p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1})"
              proof -
                have "(p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1}) = 1/k * p * (p^(l)/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})"
                  by simp
                also have "... = 1/k* (p*p^(l)/\<Prod>{k+1..k+l} - p*p^(l+1)/\<Prod>{k+1..k+l+1})" 
                  by argo
                also have "... =  1/k* (p^(l+1)/\<Prod>{k+1..k+l} - p^(l+2)/\<Prod>{k+1..k+l+1})" by simp
                also have "... =  1/k*p^(l+1)/\<Prod>{k+1..k+l} - 1/k*p^(l+2)/\<Prod>{k+1..k+l+1}" by argo
                also have "... = p^(l+1)/(k*\<Prod>{k+1..k+l}) - p^(l+2)/(k*\<Prod>{k+1..k+l+1})" by simp
                also have "... = p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1})" 
                  apply(rewrite Prod_sequence)
                  apply(rewrite Prod_sequence2)
                  apply(simp)
                  done
                finally show "((p/k)) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1}) = p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1})"
                  by simp
              qed
              then show "ennreal ((p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})) = ennreal ( p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1}))"
              proof -                
                have p_l_prod_k:" p^(l+1)/\<Prod>{k+1..k+l+1} \<le> p^l/\<Prod>{k+1..k+l}"
                proof -
                  have 1:"p^(l+1) \<le> p^l" using asm1 power_decreasing le_add1 by blast
                  have 2:"\<Prod>{k+1..k+l} \<le> \<Prod>{k+1..k+l+1}" by simp
                  have 3:"0 < \<Prod>{k+1..k+l}"
                    using Prod_sequence_eq_fact_divide by simp
                  show "p^(l+1)/\<Prod>{k+1..k+l+1} \<le> p^l/\<Prod>{k+1..k+l}"
                    apply(rule frac_le)
                    using asm1 apply(simp)
                    using 1 apply(simp)
                    using 3 apply (linarith)
                    using 2 by linarith
                qed
                have left_ge_zero:"0\<le>(p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})"
                proof- 
                  have "0\<le> p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1}"
                    using p_l_prod_k by linarith
                  then show "0\<le>(p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})" 
                    by (simp add: asm1)
                qed
                have right_ge_zero: "0 \<le>  p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1})"
                  using eq1 left_ge_zero by linarith
                show "ennreal ((p/k) * (p^l/\<Prod>{k+1..k+l} - p^(l+1)/\<Prod>{k+1..k+l+1})) = ennreal ( p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1}))"
                  using left_ge_zero right_ge_zero eq1 by presburger
              qed
            qed
            finally show "ennreal (spmf (bernoulli (p/k)) True * spmf (loop1 p (k + 1)) (k + l + 1))
                          = ennreal ( p^(l+1)/(\<Prod>{k..k+l}) - p^(l+2)/(\<Prod>{k..k+l+1}))"
              by simp
          qed
          also have "ennreal (p^(l+1) / \<Prod>{k..k+l} - p^(l+2) / \<Prod>{k..k+l+1}) = ennreal (p^Suc l/\<Prod>{k..k + Suc l - 1} - p^(Suc l+1)/\<Prod>{k..k + Suc l})"
            by simp
          finally show "ennreal (spmf (loop1 p k) (k + Suc l)) = ennreal (p^Suc l/\<Prod>{k..k+Suc l-1} - p^(Suc l+1)/\<Prod>{k..k+Suc l})"
            by simp
      qed
    qed
  qed
  then have ennreal_eq:"ennreal (spmf (loop1 p 1) m) = ennreal (p^(m-1)/(fact (m-1)) - p^m/(fact (m)))" 
  proof - 
    have "ennreal (spmf (loop1 p 1) m) = ennreal (spmf (loop1 p 1) (1+(m-1)))" using asm2 by simp
    also have "... = p^(m-1) /\<Prod>{1..1+(m-1)-1} - p^(m-1+1)/\<Prod>{1..1+(m-1)}" using P
    proof -
      have "(1::nat)\<le>1" by simp 
      then show "ennreal (spmf (loop1 p 1) (1 + (m - 1))) =
                 ennreal ( p^(m-1) /\<Prod>{1..1+(m-1)-1} - p^(m-1+1)/\<Prod>{1..1+(m-1)})"
        apply(rewrite P)
         apply(simp_all)
        done
    qed
    also have "... =  p^(m-1) /\<Prod>{1..m-1} - p^(m)/\<Prod>{1..m}" using assms by simp
    also have "... = p^(m-1) /fact (m-1) - p^(m)/fact m" by (simp add:fact_prod)
    finally show "ennreal (spmf (loop1 p 1) m) = ennreal (p^(m-1)/(fact (m-1)) - p^m/(fact (m)))" by simp
  qed
  then show "spmf (loop1 p 1) m = p^(m-1)/fact (m-1) - p^m/fact m"
  proof - 
    have 1:"0 \<le> spmf (loop1 p 1) m" by simp
    then have 2:"0 \<le> p^(m-1)/fact (m-1) - p^m/fact m" 
    proof -
      have 1:"p^m \<le> p^(m-1)" 
        apply(rewrite power_decreasing)
        apply(simp_all add:assms) 
        done
      have 2:"(fact (m-1::nat)::nat) \<le> fact m" 
        by(rule fact_mono[of "m-1" "m"]) auto
      have "p^m/((fact m)::nat) \<le> p^(m-1)/((fact (m-1))::nat) "
        apply(rule frac_le)
        using 1 2 asm1 apply(simp_all)
        by (simp add: fact_mono)
      then show "0 \<le> p^(m-1)/fact (m-1) - p^m/fact m" by simp
    qed
    show "spmf (loop1 p 1) m = p^(m-1)/fact (m-1) - p^m/fact m" using 1 2 ennreal_eq by simp
  qed
qed

lemma lossless_bernoulli_exp_minus_real_from_0_to_1 [simp]:
  assumes "0\<le>p" and "p\<le>1"
  shows "lossless_spmf (bernoulli_exp_minus_real_from_0_to_1 p)"
  apply(rewrite bernoulli_exp_minus_real_from_0_to_1_def)
  using assms lossless_loop1 by fastforce

lemma spmf_bernoulli_exp_minus_real_from_0_to_1_True[simp]:
  assumes  "0\<le>p" and "p\<le>1"
  shows "spmf (bernoulli_exp_minus_real_from_0_to_1 p) True = exp(-p) "
proof -
  have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1 p) True) = exp(-p)"
    apply(simp add:bernoulli_exp_minus_real_from_0_to_1_def ennreal_spmf_bind nn_integral_measure_spmf exp_def inverse_eq_divide)
  proof -
     have " (\<Sum>\<^sup>+ x::nat. ennreal (spmf (loop1 p (Suc (0::nat))) x) * ennreal (spmf (if odd x then return_spmf True else return_spmf False) True))
                =   (\<Sum>\<^sup>+ x::nat. ennreal (spmf (loop1 p 1) x) * (if odd x then 1 else 0))"
     proof - 
       have 1:"\<And> x. ennreal (spmf (if odd x then return_spmf True else return_spmf False) True) = (if odd x then 1 else 0)" by simp
       show ?thesis
         by(simp add: 1)  
     qed
     also have "... = (\<Sum>\<^sup>+ x::nat. (if odd x then ennreal (spmf (loop1 p 1) x)* 1 else ennreal (spmf (loop1 p 1) x) * 0))"
     proof -
       have "(\<forall>n. (ennreal (spmf (loop1 p 1) n) * (if odd n then 1 else 0) = ennreal (spmf (loop1 p 1) n) * 0 \<or> odd n) \<and> (ennreal (spmf (loop1 p 1) n) * (if odd n then 1 else 0) = ennreal (spmf (loop1 p 1) n) * 1 \<or> even n)) \<or> (\<Sum>\<^sup>+ n. ennreal (spmf (loop1 p 1) n) * (if odd n then 1 else 0)) = (\<Sum>\<^sup>+ n. if odd n then ennreal (spmf (loop1 p 1) n) * 1 else ennreal (spmf (loop1 p 1) n) * 0)"
         by presburger
       then show ?thesis
         by meson
     qed
     also have "... = (\<Sum>\<^sup>+ x::nat. (if odd x then ennreal (spmf (loop1 p 1) x) else  0))" 
       by (meson mult.right_neutral mult_zero_right)
     also have "... = (\<Sum> x::nat. (if odd x then ennreal (spmf (loop1 p 1) x) else  0))" 
       by (simp add: nn_integral_count_space_nat)
     also have "... = (\<Sum>n::nat. if odd (2 * n + 1) then ennreal (spmf (loop1 p 1) (2 * n + 1)) else 0)" 
     proof(subst suminf_mono_reindex[of "\<lambda>n::nat. 2*n+1" "(\<lambda>x::nat. (if odd x then ennreal (spmf (loop1 p 1) x) else  0))",symmetric])
       show "strict_mono (\<lambda>n::nat. 2 * n + 1)" 
         by (simp add: strict_mono_Suc_iff)
       show "\<And>n. n \<notin> range (\<lambda>n::nat. 2 * n + 1) \<Longrightarrow> (if odd n then ennreal (spmf (loop1 p 1) n) else 0) = 0" using oddE by fastforce
       show "(\<Sum>n. if odd (2 * n + 1) then ennreal (spmf (loop1 p 1) (2 * n + 1)) else 0) =
             (\<Sum>n. if odd (2 * n + 1) then ennreal (spmf (loop1 p 1) (2 * n + 1)) else 0)" by simp
     qed
     also have "... = (\<Sum>n::nat. ennreal (spmf (loop1 p 1) (2 * n + 1)))" 
       by auto 
     also have "... = (\<Sum>n::nat. ennreal (p^(2*n)/fact (2*n) - p^(2*n+1)/fact (2*n+1)))" 
       by(subst spmf_loop1,auto simp:assms)
     also have "... = (\<Sum>n::nat. p^(2*n)/fact (2*n) - p^(2*n+1)/fact (2*n+1))"
       sorry
     also have "... = (\<Sum>n::nat. (-p)^(2*n)/fact (2*n) + (-p)^(2*n+1)/fact (2*n+1))" 
       by auto
     also have "... = (\<Sum>n::nat. (-p)^(n)/fact n)"    
       sorry
     also have "... = ennreal (\<Sum>n. (-p)^(n)/fact n)" 
       by blast
     finally show "(\<Sum>\<^sup>+ x::nat. ennreal (spmf (loop1 p (Suc (0::nat))) x) * ennreal (spmf (if odd x then return_spmf True else return_spmf False) True))
                  = ennreal (\<Sum>n. (- p) ^ n / fact n)"  try
       
   qed
   find_theorems "(\<Sum> _ . _) = (\<Sum> _ . _)"
   thm suminf_mono_reindex[of "\<lambda>n. 2*n+1"]
   thm suminf_mono_reindex[of "\<lambda>n. 2*n+1" "(\<lambda>x::nat. (if odd x then ennreal (spmf (loop1 p 1) x) else  0))"]
   show ?thesis
     sorry
 qed


lemma spmf_bernoulli_exp_minus_real_from_0_to_1_False[simp]:
  assumes  "0\<le>p" and "p\<le>1"
  shows "spmf (bernoulli_exp_minus_real_from_0_to_1 p) False =  1 - exp(-p)" 
  using assms by(simp add:spmf_False_conv_True)

context
  fixes p:: real
  and body :: "bool \<Rightarrow> bool spmf"
  assumes "1\<le>p"
defines [simp]: "body \<equiv> (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_real_from_0_to_1 1))"

begin
interpretation loop_spmf id body 
  rewrites "body \<equiv>  (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_real_from_0_to_1 1))"
  by(fact body_def)

lemma loop2_iter_simps:
  shows "iter n True = (if 1 \<le> n then  map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (n - 1)
                       else return_spmf True)"
proof -
  have "1\<le>n \<Longrightarrow> iter n True = map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (n - 1)"
  proof (cases "1\<le>n")
    case True
    then show ?thesis 
  next
    case False
    then show ?thesis sorry
  qed


value "nat (-1)"
lemma loop2_conv_iter:
  shows "loop2 p 1 = iter (nat (floor p)) True" 
proof - 
  have "loop2 p x = iter (nat ((floor p) - nat(x-1))) True" (is "?lhs = ?rhs") for x
proof(rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof (induction arbitrary: x rule: loop2_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step loop2')
    then show ?case using step.IH[of "Suc x"]
    proof -
      thm iter.simps
      have cond1:"1\<le> nat (\<lfloor>p\<rfloor> - int (nat (int (x - (1::nat))))) \<Longrightarrow> iter (nat (\<lfloor>p\<rfloor> - int (nat (int (x - (1::nat))))) ) True =   (if id True then map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (nat \<lfloor>p\<rfloor> - 1) else return_spmf True)"
        sorry
      have cond2:"nat (floor p) < 1 \<Longrightarrow> iter (nat \<lfloor>p\<rfloor>) True = return_spmf True"
        by simp
      have "iter (nat \<lfloor>p\<rfloor>) True = (if 1 \<le> nat (floor p) then  (if id True then map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (nat \<lfloor>p\<rfloor> - 1) else return_spmf True)
                                    else return_spmf True)"
        using cond1 cond2
        by (meson Suc_le_eq not_less_eq_eq)
      also have "... = (if 1 \<le> nat (floor p) then map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (nat \<lfloor>p\<rfloor> - 1)
                        else return_spmf True)"
        by simp
      finally have 1:"iter (nat \<lfloor>p\<rfloor>) True =  (if 1 \<le> nat (floor p) then map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (nat \<lfloor>p\<rfloor> - 1)
                                            else return_spmf True)"
        by simp
      have 2:"ord_spmf (=)
     (if (1::nat) \<le> (1::nat) \<and> (1::nat) \<le> nat \<lfloor>p\<rfloor> then bernoulli_exp_minus_real_from_0_to_1 (1::real) \<bind> (\<lambda>ba::bool. if ba then loop2' p ((1::nat) + (1::nat)) else return_spmf False)
      else return_spmf True)
      (if 1 \<le> nat (floor p) then  map_spmf (\<lambda>b'::bool. if b' then True else False) (bernoulli_exp_minus_real_from_0_to_1 (1::real)) \<bind> iter (nat \<lfloor>p\<rfloor> - 1)
       else return_spmf True)"
        apply(clarsimp simp add: map_spmf_bind_spmf)
        apply(clarsimp intro!: ord_spmf_bind_reflI)
        sorry
      show ?thesis using 1 2 by argo 
  qed
  show "ord_spmf (=) ?rhs ?lhs"
    sorry
qed

lemma lossless_loop2 [simp]:
  shows "lossless_spmf (loop2 p 1)"
proof -
  have "lossless_spmf (iter (nat (floor p)) True)"
    using lossless_iter by simp
  then show ?thesis
    using loop2_conv_iter by simp
qed
end

thm "spmf_False_conv_True"

lemma spmf_loop2_True [simp]: 
  assumes "1\<le>p" 
  shows "spmf (loop2 p 1) True = exp(-floor(p))"
  sorry
lemma spmf_loop2_False [simp]:
  assumes "1\<le>p"
  shows "spmf (loop2 p 1) False = 1 - exp(-floor(p))"
  using assms lossless_loop2 spmf_False_conv_True spmf_loop2_True by auto

lemma lossless_bernoulli_exp_minus_real[simp]:
  shows "lossless_spmf (bernoulli_exp_minus_real p)"
proof -
  have 1:"0\<le>p - real_of_int \<lfloor>p\<rfloor>" by simp
  have 2:"p - real_of_int \<lfloor>p\<rfloor>\<le>1" 
    by linarith
  show ?thesis
    apply(rewrite bernoulli_exp_minus_real_def)
    using 1 2 lossless_bernoulli_exp_minus_real_from_0_to_1 lossless_loop2
    by simp
qed

lemma spmf_bernoulli_exp_minus_rat_True[simp]:
  shows "spmf (bernoulli_exp_minus_real p) True = exp(-p)"
  apply(simp add: bernoulli_exp_minus_real_def)
  sorry

lemma spmf_bernoulli_exp_minus_rat_False[simp]:
  shows "spmf (bernoulli_exp_minus_real p) False = 1-exp(-p)"
  by(simp add:spmf_False_conv_True)







end