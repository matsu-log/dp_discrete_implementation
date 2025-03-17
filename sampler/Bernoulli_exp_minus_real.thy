section \<open>Bernoulli distribution that take exp(-p) as parameter\<close>

theory Bernoulli_exp_minus_real
  imports "Probabilistic_While.While_SPMF"
          "HOL-Probability.Probability"
          "Probabilistic_While.Bernoulli"
begin

subsection \<open>auxiliary lemmas\<close>

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

(*this lemma for summable_2i_2i_plus_1*)
lemma power_divide_fact :
  fixes p::real and n m::nat
  assumes "0\<le>p" and "p\<le>1" and "n\<le>m"
  shows "p^m/fact m \<le> p^n/ fact n"
proof -
  have 1:"0\<le> p^n"
    using assms by simp
  have 2:"p^m \<le> p^n" 
    using assms by(simp add: power_decreasing)
  show ?thesis 
    using 1 2
    by (simp add: assms(3) fact_mono frac_le)
qed

lemma summable_2i_2i_plus_1:
  fixes p:: real
  assumes "0\<le>p" and "p\<le>1"
  shows "summable (\<lambda>i. p ^ (2 * i) / fact (2 * i) - p ^ (2 * i + 1) / fact (2 * i + 1))"
proof (rule summable_diff)
  have 1: "summable (\<lambda>i. p^i / fact i)"
    using summable_exp_generic[of "p"] by (simp add:inverse_eq_divide)
  show summable_2i:"summable (\<lambda>i. p ^ (2 * i) / fact (2 * i))"
  proof (subst summable_comparison_test[of "\<lambda>i. p^(2*i) / fact (2*i)" "\<lambda>i. p^i / fact i"])
    show "\<exists>N. \<forall>n\<ge>N. norm (p ^ (2 * n) / fact (2 * n)) \<le> p ^ n / fact n"
    proof -
      have "\<forall>n. p ^ (2 * n) / fact (2 * n) \<le> p ^ n / fact n"
      proof 
        fix n
        show "p ^ (2 * n) / fact (2 * n) \<le> p ^ n / fact n"
          using assms by(rule power_divide_fact[of "p" "n" "2*n"],simp_all)
      qed
      then show ?thesis
        by simp
    qed
    show "summable (\<lambda>i. p ^ i / fact i)" 
      using 1 by simp
    show "True" by simp
  qed
  show summable_2i_plus_1:"summable (\<lambda>i. p ^ (2 * i + 1) / fact (2 * i + 1))"
  proof (subst summable_comparison_test[of "\<lambda>i. p^(2*i+1) / fact (2*i+1)" "\<lambda>i. p^i / fact i"])
    show "\<exists>N. \<forall>n\<ge>N. norm (p^(2*n+1)/fact (2*n+1)) \<le> p^n/fact n"
    proof -
      have "\<forall>n. norm (p^(2*n+1)/fact (2*n+1)) \<le> p^n/fact n"
      proof 
        fix n
        show "norm (p^(2*n+1)/fact (2*n+1)) \<le> p^n/fact n"
        proof -
          have 1:"norm (p^(2*n+1)/fact (2*n+1)) = p^(2*n+1)/fact (2*n+1)"
          proof-
            have 1:"norm (p^(2*n+1)/fact (2*n+1)) = \<bar>(p^(2*n+1)/fact (2*n+1))\<bar>"
              by simp
            have 2:"0\<le> p^(2*n+1)/fact (2*n+1)"
              by (simp add: assms(1))
            show ?thesis using 1 2 
              by argo
          qed
          have 2:"p^(2*n+1)/fact (2*n+1)\<le> p^n/fact n"
            using assms by(rule power_divide_fact[of "p" "n" "2*n+1"],simp_all)
          show ?thesis using 1 2 by simp
        qed
      qed
      then show ?thesis
        by simp
    qed
    show "summable (\<lambda>i. p ^ i / fact i)" 
      using 1 by simp
    show "True" by simp
  qed
qed

subsection \<open>Define bernoulli_exp_minus_real\<close>

context notes [[function_internals]] begin
partial_function (spmf) bernoulli_exp_minus_real_from_0_to_1_loop :: "real  \<Rightarrow> nat  \<Rightarrow> nat spmf" where
 "bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k =
    (
    do {
      a \<leftarrow> bernoulli (\<gamma>/k);
      if a then bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k+1) else return_spmf k
    }
)
"
end

definition  bernoulli_exp_minus_real_from_0_to_1 :: "real \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_real_from_0_to_1 \<gamma> = 
    do {
        k \<leftarrow> bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1;
        if odd k then return_spmf True else return_spmf False
    }
  "

context notes [[function_internals]] begin
partial_function (spmf) bernoulli_exp_minus_real_loop :: "nat \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_real_loop k = (if 1\<le>k then do {
                                b \<leftarrow> bernoulli_exp_minus_real_from_0_to_1 1;
                                if b then bernoulli_exp_minus_real_loop (k-1) else return_spmf False
                                } 
                else return_spmf True)"
end

definition bernoulli_exp_minus_real :: "real  \<Rightarrow> bool spmf" where
  "bernoulli_exp_minus_real \<gamma> = 
  (
    if \<gamma> < 0 then return_spmf True  
    else if 0 \<le> \<gamma> & \<gamma>\<le>1  then bernoulli_exp_minus_real_from_0_to_1 \<gamma>
    else
     do {
        b \<leftarrow> bernoulli_exp_minus_real_loop (nat (floor \<gamma>));
        if b then bernoulli_exp_minus_real_from_0_to_1 (\<gamma>-floor \<gamma>) else return_spmf b
      }
  )
"

subsection \<open>Properties of bernoulli_exp_minus_real\<close>

lemma bernoulli_exp_minus_real_from_0_to_1_loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>bernoulli_exp_minus_real_from_0_to_1_loop. P (curry bernoulli_exp_minus_real_from_0_to_1_loop))"
    and "P (\<lambda>bernoulli_exp_minus_real_from_0_to_1_loop \<gamma>. return_pmf None)"
    and "(\<And>bernoulli_exp_minus_real_from_0_to_1_loop'. P bernoulli_exp_minus_real_from_0_to_1_loop' \<Longrightarrow> P (\<lambda>a b. bernoulli (a / b) \<bind> (\<lambda>aa. if aa then bernoulli_exp_minus_real_from_0_to_1_loop' a (b + 1) else return_spmf b)))"
  shows "P bernoulli_exp_minus_real_from_0_to_1_loop"
  using assms by (rule bernoulli_exp_minus_real_from_0_to_1_loop.fixp_induct)

lemma bernoulli_exp_minus_real_loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>bernoulli_exp_minus_real_loop. return_pmf None)"
and "(\<And>k. P k \<Longrightarrow>
      P (\<lambda>ka. if 1 \<le> ka
               then bernoulli_exp_minus_real_from_0_to_1 1 \<bind> (\<lambda>b. if b then k (ka - 1) else return_spmf False)
               else return_spmf True))"
shows "P bernoulli_exp_minus_real_loop"
  using assms by (rule bernoulli_exp_minus_real_loop.fixp_induct)

context
  fixes \<gamma> :: "real"
  and body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
  assumes cond1:"0\<le>\<gamma>" and cond2:"\<gamma>\<le>1"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli  (\<gamma>/k')))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv>  (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli (\<gamma>/k')))" 
  by(fact body_def)

lemma bernoulli_exp_minus_real_from_0_to_1_loop_conv_while:
 "bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1 = map_spmf snd (while (True, 1))"
proof -
  have "bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> x = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule: bernoulli_exp_minus_real_from_0_to_1_loop_fixp_induct)
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
        by(rewrite bernoulli_exp_minus_real_from_0_to_1_loop.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

lemma lossless_bernoulli_exp_minus_real_from_0_to_1_loop [simp]: "lossless_spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1)"
proof-
  have "lossless_spmf (while (True, 1))"
  proof -
    have False_1:"lossless_spmf (while (False,1))"
      by(simp add:while.simps)
    have True_2:"lossless_spmf (while (True,2))"
    proof(rule termination_0_1_immediate_invar)
      let ?I = "\<lambda>(b,k'::nat). 2\<le>k'"
      let ?p = "1-\<gamma>/2"
      show "\<And>s. fst s \<Longrightarrow> ?I s \<Longrightarrow> ?p \<le> spmf (map_spmf fst (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (\<gamma> / real k')))) False"     
      proof clarify
        fix a::bool and  b::nat 
        assume "fst (a,b)" and I_b:"2\<le>b"
        show "1 - \<gamma> / 2 \<le> spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (\<gamma> / real b)))) False"
        proof -
          have "ennreal (spmf (map_spmf fst (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (\<gamma> / real b)))) False) =  ennreal (\<Sum>a | \<not> a. spmf (bernoulli (\<gamma> / real b)) a)"
            apply(simp add: ennreal_spmf_map_conv_nn_integral)
            apply(simp add: nn_integral_measure_spmf)
            apply(simp add: UNIV_bool)
            by(simp add: nn_integral_count_space_finite)  
          also have "... =  ennreal (spmf (bernoulli (\<gamma>/b)) False)"
          proof -
            have "{a.\<not>a} = {False}" by auto
            then show ?thesis by simp
          qed
          also have "... \<ge> 1-\<gamma>/2"
          proof -
            have "\<gamma>/b \<le>\<gamma>/2"
              apply(rule divide_left_mono)
              using cond1 I_b by(simp_all)
            then have p:"1-\<gamma>/2 \<le> 1-\<gamma>/b" by simp
            have "1 - \<gamma> / 2 \<le> spmf (bernoulli (\<gamma>/b)) False"
              using cond1 cond2 I_b p
              by simp
            then show ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
      qed
      show "0<?p" using cond2 by simp
      show "\<And>s. fst s \<Longrightarrow> ?I s \<Longrightarrow> lossless_spmf (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (\<gamma> / real k')))"
      proof clarify
        fix a::bool and b::nat
        assume "fst (a,b)" and "2\<le>b"
        show "lossless_spmf (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (\<gamma> / real b))) " by simp
      qed
      show "\<And>s s'. s' \<in> set_spmf (case s of (b, k') \<Rightarrow> map_spmf (\<lambda>b'. if b' then (True, k' + 1) else (False, k')) (bernoulli (\<gamma> / real k'))) \<Longrightarrow> ?I s \<Longrightarrow> fst s \<Longrightarrow> ?I s'"
      proof clarify
        fix a aa::bool and b ba::nat
        assume step:" (aa, ba) \<in> set_spmf (map_spmf (\<lambda>b'. if b' then (True, b + 1) else (False, b)) (bernoulli (\<gamma> / real b)))"
          and I_b:"2\<le>b" and guard:"fst(a,b)"
        show "2\<le>ba"
        proof -
          have "b\<le>ba" using step by auto  
          then show "2\<le>ba" using I_b by simp 
        qed
      qed
      show "?I (True,2)" using cond2 by simp
    qed
    show "lossless_spmf (while (True,1))"
      apply(rewrite while.simps,simp add:bind_map_spmf)
      using True_2 False_1
      by (simp add: numeral_2_eq_2)
  qed
  then show "lossless_spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1)" 
    using bernoulli_exp_minus_real_from_0_to_1_loop_conv_while by simp
qed
end

lemma spmf_bernoulli_exp_minus_real_from_0_to_1_loop_zero_fixp_induct_case_adm:
  shows "spmf.admissible (\<lambda>bernoulli_exp_minus_real_from_0_to_1_loop. \<forall>l>m. spmf ((curry bernoulli_exp_minus_real_from_0_to_1_loop) \<gamma> l) m = 0)"
proof -
  have "\<forall>A. Complete_Partial_Order.chain spmf.le_fun A \<longrightarrow> A \<noteq> {} \<longrightarrow> (\<forall>x\<in>A. \<forall>l>m. spmf (x (\<gamma>, l)) m = 0) \<longrightarrow> (\<forall>l>m. spmf (lub_spmf {y. \<exists>f\<in>A. y = f (\<gamma>, l)}) m = 0) "
  proof clarify
    fix A l
    assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
      H: "\<forall>x\<in>A.\<forall>l>m. spmf (x (\<gamma>, l)) m = 0" and
      L: "l>m" 
    have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f (\<gamma>, l)}) m =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f (\<gamma>, l)}. spmf p m)"
    proof(rule spmf_lub_spmf)
      show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f (\<gamma>, l)}" 
        by (simp add: CA chain_fun)
    next 
      show "{y. \<exists>f\<in>A. y = f (\<gamma>, l)} \<noteq> {}" using A by blast
    qed
    have "... =  \<Squnion>{0}"
    proof (rule cong[where f=Sup and g=Sup])
      show "Sup = Sup" by simp
      show " (\<lambda>p. spmf p m) ` {y. \<exists>f\<in>A. y = f (\<gamma>, l)} = {0}"
        using A H L by (auto simp add: image_def)
    qed
    also have "... = 0"
      by simp
    finally show  "spmf (lub_spmf {y. \<exists>f\<in>A. y = f (\<gamma>, l)}) m = 0"
      using P by presburger
  qed
  then show ?thesis
    by (simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf)
qed

lemma spmf_bernoulli_exp_minus_real_from_0_to_1_loop_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> l) m = 0"
proof (induction rule: bernoulli_exp_minus_real_from_0_to_1_loop_fixp_induct)
  case adm
  then show ?case 
    using spmf_bernoulli_exp_minus_real_from_0_to_1_loop_zero_fixp_induct_case_adm by fastforce
next
  case bottom
  then show ?case by simp
next
  case (step k)
  then show ?case  
  proof (clarify)
    fix l
    assume Step:"\<forall>l>m. spmf (k \<gamma> l) m = 0" and L:"l>m"
    have "ennreal (spmf (bernoulli (\<gamma>/l) \<bind> (\<lambda>aa. if aa then k \<gamma> (l + 1) else return_spmf l)) m) = ennreal 0"
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
      using L Step not_less_eq option.inject order_less_imp_not_less singletonD 
      by auto
    then show "spmf (bernoulli (\<gamma>/l) \<bind> (\<lambda>aa. if aa then k \<gamma> (l + 1) else return_spmf l)) m = 0" by simp
  qed
qed

lemma spmf_bernoulli_exp_minus_real_from_0_to_1_loop[simp]:
  assumes asm1:"0\<le>\<gamma>" "\<gamma>\<le> 1" and asm2:"1\<le>m"
  shows "spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m = \<gamma>^(m-1)/fact (m-1) - \<gamma>^m/fact m" (is "?lhs m = ?rhs m")
proof -
  have P:"\<forall>k l::nat . 1\<le>k \<longrightarrow> ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k+l)) = \<gamma>^l /\<Prod>{k..(k+l-1)} - \<gamma>^(l+1)/\<Prod>{k..(k+l)}"
  proof clarify
    fix l
    show "\<And>k.1 \<le> k \<Longrightarrow>
           ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + l)) =
           ennreal (\<gamma>^l /(\<Prod>{k..k + l - 1}) - \<gamma>^(l+1)/(\<Prod>{k..k + l}))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + 0)) = ennreal (spmf (bernoulli (\<gamma>/k)) False) + ennreal (spmf (bernoulli (\<gamma>/k)) True) * ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k+1)) k)"
          apply(rewrite bernoulli_exp_minus_real_from_0_to_1_loop.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal (1-(\<gamma>/k))"
          proof - 
            have p_divide_k_0_1: "\<gamma>/k\<le>1" "0\<le>\<gamma>/k"using asm1 0 by auto
            then show "ennreal (spmf (bernoulli (\<gamma>/k)) False) + ennreal (spmf (bernoulli (\<gamma>/k)) True) * ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k + 1)) k) =  ennreal (1-(\<gamma>/k))"
              using spmf_bernoulli_exp_minus_real_from_0_to_1_loop_zero by simp
          qed
        also have "... = ennreal (\<gamma>^0/\<Prod>{k..k+0-1} - \<gamma>^(0+1)/\<Prod>{k..k + 0})" 
          proof - 
            have "k-1 < k" using 0 by simp
            then have "{k..k+0-1} = {}" by simp
            then show "ennreal (1-(\<gamma>/k)) = ennreal (\<gamma>^0/\<Prod>{k..k+0-1} - \<gamma>^(0+1)/\<Prod>{k..k + 0})"
              by simp
          qed
        finally show "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + 0)) = ennreal (\<gamma>^0/\<Prod>{k..k+0-1} - \<gamma>^(0+1)/\<Prod>{k..k + 0})" by simp
      qed 
    next
      case (Suc l)
      then show ?case
      proof - 
          assume step:"\<And>k. 1 \<le> k \<Longrightarrow>
          ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + l)) =
          ennreal (\<gamma>^l/\<Prod>{k..k+l-1} - \<gamma>^(l+1)/\<Prod>{k..k + l})"
            and K: "1\<le>k"
          have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + Suc l)) = ennreal ((spmf (bernoulli (\<gamma>/k)) True) * (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k+1)) (k+l+1)))"
            apply(rewrite bernoulli_exp_minus_real_from_0_to_1_loop.simps)
            apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite ennreal_mult)
            done
          also have "... = ennreal (\<gamma>^(l+1) / \<Prod>{k..k+l} - \<gamma>^(l+2) / \<Prod>{k..k+l+1})"
          proof -
            have n_divide_p_0_1: "0\<le> \<gamma>/k" "\<gamma>/k\<le>1" using K asm1 by auto
            then have Bernoulli:"ennreal (spmf (bernoulli  (\<gamma>/k)) True) = \<gamma>/k" by simp
            have H:"ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k+1)) (k+1+l)) = ennreal (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})" 
              apply (rewrite step)
              apply(simp_all)
              done
            have "ennreal (spmf (bernoulli (\<gamma>/k)) True * spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k + 1)) (k + l + 1))=ennreal (spmf (bernoulli (\<gamma>/k)) True) *ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k + 1)) (k + 1 + l))"
              by(simp add: ennreal_mult)
            also have "...=ennreal (\<gamma>/k) * ennreal (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})"
              apply(rewrite Bernoulli)
              apply(rewrite H)
              apply(simp)
              done
            also have "... = ennreal ((\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1}))"
              using ennreal_mult' n_divide_p_0_1(1) by presburger
            also have "... = ennreal ( (\<gamma>^(l+1)/\<Prod>{k..k+l} - \<gamma>^(l+2)/\<Prod>{k..k+l+1}))"
            proof - 
              have eq1:"(\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1}) =  \<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1})"
              proof -
                have "(\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1}) = 1/k * \<gamma> * (\<gamma>^(l)/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})"
                  by simp
                also have "... = 1/k* (\<gamma>*\<gamma>^(l)/\<Prod>{k+1..k+l} - \<gamma>*\<gamma>^(l+1)/\<Prod>{k+1..k+l+1})" 
                  by argo
                also have "... =  1/k* (\<gamma>^(l+1)/\<Prod>{k+1..k+l} - \<gamma>^(l+2)/\<Prod>{k+1..k+l+1})" by simp
                also have "... =  1/k*\<gamma>^(l+1)/\<Prod>{k+1..k+l} - 1/k*\<gamma>^(l+2)/\<Prod>{k+1..k+l+1}" by argo
                also have "... = \<gamma>^(l+1)/(k*\<Prod>{k+1..k+l}) - \<gamma>^(l+2)/(k*\<Prod>{k+1..k+l+1})" by simp
                also have "... = \<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1})" 
                  apply(rewrite Prod_sequence)
                  apply(rewrite Prod_sequence2)
                  apply(simp)
                  done
                finally show "((\<gamma>/k)) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1}) = \<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1})"
                  by simp
              qed
              then show "ennreal ((\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})) = ennreal ( \<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1}))"
              proof -                
                have p_l_prod_k:" \<gamma>^(l+1)/\<Prod>{k+1..k+l+1} \<le> \<gamma>^l/\<Prod>{k+1..k+l}"
                proof -
                  have 1:"\<gamma>^(l+1) \<le> \<gamma>^l" using asm1 power_decreasing le_add1 by blast
                  have 2:"\<Prod>{k+1..k+l} \<le> \<Prod>{k+1..k+l+1}" by simp
                  have 3:"0 < \<Prod>{k+1..k+l}"
                    using Prod_sequence_eq_fact_divide by simp
                  show "\<gamma>^(l+1)/\<Prod>{k+1..k+l+1} \<le> \<gamma>^l/\<Prod>{k+1..k+l}"
                    apply(rule frac_le)
                    using asm1 apply(simp)
                    using 1 apply(simp)
                    using 3 apply (linarith)
                    using 2 by linarith
                qed
                have left_ge_zero:"0\<le>(\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})"
                proof- 
                  have "0\<le> \<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1}"
                    using p_l_prod_k by linarith
                  then show "0\<le>(\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})" 
                    by (simp add: asm1)
                qed
                have right_ge_zero: "0 \<le>  \<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1})"
                  using eq1 left_ge_zero by linarith
                show "ennreal ((\<gamma>/k) * (\<gamma>^l/\<Prod>{k+1..k+l} - \<gamma>^(l+1)/\<Prod>{k+1..k+l+1})) = ennreal (\<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1}))"
                  using left_ge_zero right_ge_zero eq1 by presburger
              qed
            qed
            finally show "ennreal (spmf (bernoulli (\<gamma>/k)) True * spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (k + 1)) (k + l + 1))
                          = ennreal (\<gamma>^(l+1)/(\<Prod>{k..k+l}) - \<gamma>^(l+2)/(\<Prod>{k..k+l+1}))"
              by simp
          qed
          also have "ennreal (\<gamma>^(l+1) / \<Prod>{k..k+l} - \<gamma>^(l+2) / \<Prod>{k..k+l+1}) = ennreal (\<gamma>^Suc l/\<Prod>{k..k + Suc l - 1} - \<gamma>^(Suc l+1)/\<Prod>{k..k + Suc l})"
            by simp
          finally show "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> k) (k + Suc l)) = ennreal (\<gamma>^Suc l/\<Prod>{k..k+Suc l-1} - \<gamma>^(Suc l+1)/\<Prod>{k..k+Suc l})"
            by simp
      qed
    qed
  qed
  then have ennreal_eq:"ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m) = ennreal (\<gamma>^(m-1)/(fact (m-1)) - \<gamma>^m/(fact (m)))" 
  proof - 
    have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m) = ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (1+(m-1)))" using asm2 by simp
    also have "... = \<gamma>^(m-1) /\<Prod>{1..1+(m-1)-1} - \<gamma>^(m-1+1)/\<Prod>{1..1+(m-1)}" using P
    proof -
      have "(1::nat)\<le>1" by simp 
      then show "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (1 + (m - 1))) =
                 ennreal (\<gamma>^(m-1) /\<Prod>{1..1+(m-1)-1} - \<gamma>^(m-1+1)/\<Prod>{1..1+(m-1)})"
        apply(rewrite P)
         apply(simp_all)
        done
    qed
    also have "... =  \<gamma>^(m-1) /\<Prod>{1..m-1} - \<gamma>^(m)/\<Prod>{1..m}" using assms by simp
    also have "... = \<gamma>^(m-1) /fact (m-1) - \<gamma>^(m)/fact m" by (simp add:fact_prod)
    finally show "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m) = ennreal (\<gamma>^(m-1)/(fact (m-1)) - \<gamma>^m/(fact (m)))" by simp
  qed
  then show "spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m = \<gamma>^(m-1)/fact (m-1) - \<gamma>^m/fact m"
  proof - 
    have 1:"0 \<le> spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m" by simp
    then have 2:"0 \<le> \<gamma>^(m-1)/fact (m-1) - \<gamma>^m/fact m" 
    proof -
      have 1:"\<gamma>^m \<le> \<gamma>^(m-1)" 
        apply(rewrite power_decreasing)
        apply(simp_all add:assms) 
        done
      have 2:"(fact (m-1::nat)::nat) \<le> fact m" 
        by(rule fact_mono[of "m-1" "m"]) auto
      have "\<gamma>^m/((fact m)::nat) \<le> \<gamma>^(m-1)/((fact (m-1))::nat) "
        apply(rule frac_le)
        using 1 2 asm1 apply(simp_all)
        by (simp add: fact_mono)
      then show "0 \<le> \<gamma>^(m-1)/fact (m-1) - \<gamma>^m/fact m" by simp
    qed
    show "spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) m = \<gamma>^(m-1)/fact (m-1) - \<gamma>^m/fact m" using 1 2 ennreal_eq by simp
  qed
qed

lemma lossless_bernoulli_exp_minus_real_from_0_to_1 [simp]:
  assumes "0\<le>\<gamma>" and "\<gamma>\<le>1"
  shows "lossless_spmf (bernoulli_exp_minus_real_from_0_to_1 \<gamma>)"
  apply(rewrite bernoulli_exp_minus_real_from_0_to_1_def)
  using assms lossless_bernoulli_exp_minus_real_from_0_to_1_loop by fastforce

lemma lim_zero_for_spmf_bernoulli_exp_minus_real_from_0_to_1:
  fixes p::real
  assumes "0\<le>p" and "p\<le>1"
  shows " (\<lambda>n. \<Sum>i = 0..n. (-p)^(2*i)/fact (2*i) + (-p)^(2*i+1)/fact (2*i+1) - (- p)^i/fact i) \<longlonglongrightarrow> 0"
proof -
  let ?f = "\<lambda>n. (-p)^n/fact n"
  have 1:"(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) = (\<lambda>n. \<Sum>i = n+1..2*n+1. ?f i)"
  proof
    fix n
    show "(\<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) = (\<Sum>i = n + 1..2 * n + 1. ?f i) "
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      then show ?case 
      proof -
        have "(\<Sum>i = 0..Suc n. ?f (2*i) + ?f (2*i+1) - ?f i) 
            = (\<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) + ?f (2*(n+1)) + ?f (2*(n+1)+1) - ?f (n+1) "
          by simp
        also have "... = (\<Sum>i = n+1..2*n+1. ?f i) + ?f (2*(n+1)) + ?f (2*(n+1)+1) - ?f (n+1)"
          using Suc 
          by simp
        also have "... = (\<Sum>i = Suc (n+1)..2*n+1. ?f i) + ?f (2*(n+1)) + ?f (2*(n+1)+1)" 
        proof -
          have "(\<Sum>i = n+1..2*n+1. ?f i) =  ?f (n+1) + (\<Sum>i = Suc (n+1)..2*n+1. ?f i)"
            by(rule sum.atLeast_Suc_atMost[of "n+1" "2*n+1" "?f"],simp)
          then show ?thesis 
            by simp
        qed
        also have "... = (\<Sum>i = Suc n+1..2 *Suc n + 1. ?f i)"
          by simp
        finally show "(\<Sum>i = 0..Suc n. ?f (2*i) + ?f (2*i+1) - ?f i) = (\<Sum>i = Suc n+1..2 *Suc n + 1. ?f i)" by simp
      qed
    qed
  qed
  let ?s1 = "(\<lambda>n. \<Sum>i = 0.. 2*n+1. ?f i)"
  let ?s2 = "(\<lambda>n. \<Sum>i = 0.. n. ?f i)"
  have 2:"(\<lambda>n. \<Sum>i = n+1..2*n+1. ?f i) = ?s1 - ?s2"
  proof -
    have "(\<lambda>n. \<Sum>i = n+1..2*n+1. ?f i) = (\<lambda>n. \<Sum>i = n+1..<2*n+1+1. ?f i)"
    proof -
      have "\<forall>n::nat. {n+1..2*n+1} = {n+1..<2*n+1+1}" by auto
      then show ?thesis by simp
    qed
    also have "... = (\<lambda>n. (\<Sum>i = 0..<2*n+1+1. ?f i) - (\<Sum>i = 0..<n+1. ?f i))"
      by(subst sum_diff_nat_ivl,auto)
    also have "... = (\<lambda>n. (\<Sum>i = 0..2*n+1. ?f i) - (\<Sum>i = 0..n. ?f i))"
    proof -
      have 1:"\<forall>n::nat. {n+1..2*n+1} = {n+1..<2*n+1+1}" by auto
      have 2:"\<forall>n::nat. {0..n} = {0..<n+1}" by auto
      show ?thesis using 1 2 by simp
    qed
    also have "... = ?s1 - ?s2" by auto
    finally show ?thesis by simp
  qed 
  have 3:"?s1-?s2 \<longlonglongrightarrow> 0"
  proof -
    have "(\<Sum>n.?f n) = exp (-p)"
      apply(subst exp_def)
      by (simp add: inverse_eq_divide)
    have 1:"?s2 \<longlonglongrightarrow> (\<Sum>n.?f n) "
    proof -
      have 1:"?s2 =(\<lambda>n. sum ?f {..n})"
        by (simp add: atMost_atLeast0)
      then have 2:"(\<lambda>n. sum ?f {..n})\<longlonglongrightarrow> (\<Sum>n.?f n) "
      proof (subst summable_LIMSEQ')
        show "summable ?f" 
          using summable_exp_generic[of "-p"] by (simp add: inverse_eq_divide)
        show "True" by simp
      qed
      show ?thesis
        using 1 2 by simp
    qed
    have 2:"?s1 \<longlonglongrightarrow> (\<Sum>n.?f n) "
    proof -
      have "?s1 = ((\<lambda>n. \<Sum>i = 0..n. (- p) ^ i / fact i) \<circ> (\<lambda>n. 2 * n + 1))"
        by auto
      also have "... \<longlonglongrightarrow> (\<Sum>n.?f n)"
      proof (rule LIMSEQ_subseq_LIMSEQ[of "(\<lambda>n. \<Sum>i = 0.. n. ?f i)" "(\<Sum>n. (- p) ^ n / fact n)" "\<lambda>n. 2*n+1"])
        show "?s2 \<longlonglongrightarrow> (\<Sum>n.?f n) " 
          using 1 by simp
        show "strict_mono (\<lambda>n::nat. 2*n + 1)" 
          by (simp add: strict_monoI)
      qed
      finally show ?thesis by simp
    qed
    show ?thesis 
    proof -
      have "?s1 - ?s2 = (\<lambda>n. (\<Sum>i=0..2*n+1. (-p)^i/fact i)+(-(\<lambda>n. \<Sum>i = 0..n. (-p)^i/fact i)) n)"
        by auto
      also have "... \<longlonglongrightarrow> (\<Sum>n. ?f n) + - (\<Sum>n. ?f n)"
      proof (rule tendsto_add[of "?s1" "(\<Sum>n.?f n)" "sequentially" "-?s2" "-(\<Sum>n.?f n)"])
        show "?s1 \<longlonglongrightarrow> (\<Sum>n. (- p) ^ n / fact n)"
          using 2 by simp
        show "-?s2 \<longlonglongrightarrow> -(\<Sum>n. ?f n)" 
        proof -
          have "-?s2 = (\<lambda>n. -(\<Sum>i = 0..n. (- p) ^ i / fact i))"
            by auto
          also have "... \<longlonglongrightarrow> -(\<Sum>n. ?f n)"
            using 1 tendsto_minus[of "?s2" "(\<Sum>n.?f n)" "sequentially"] by simp
          finally show ?thesis by simp
        qed
      qed
      also have "(\<Sum>n. ?f n) + - (\<Sum>n. ?f n) = 0" by simp
      finally show ?thesis by blast
    qed
  qed
  show ?thesis using 1 2 3 by simp
qed

lemma spmf_bernoulli_exp_minus_real_from_0_to_1_True[simp]:
  assumes  "0\<le>\<gamma>" and "\<gamma>\<le>1"
  shows "spmf (bernoulli_exp_minus_real_from_0_to_1 \<gamma>) True = exp(-\<gamma>) "
proof -
  have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1 \<gamma>) True) = exp(-\<gamma>)"
  proof -
    have "ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1 \<gamma>) True) = (\<Sum>\<^sup>+ x::nat. ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> (Suc 0)) x) * ennreal (spmf (if odd x then return_spmf True else return_spmf False) True))"
      unfolding bernoulli_exp_minus_real_from_0_to_1_def
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf exp_def inverse_eq_divide)
     also have "... = (\<Sum>\<^sup>+ x::nat. ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x) * (if odd x then 1 else 0))"
     proof -
       have 1:"\<And> x. ennreal (spmf (if odd x then return_spmf True else return_spmf False) True) = (if odd x then 1 else 0)" by simp
       show ?thesis
         by(simp add: 1)  
     qed
     also have "... = (\<Sum>\<^sup>+ x::nat. (if odd x then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x)* 1 else ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x) * 0))"
     proof -
       have "(\<forall>n. (ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * (if odd n then 1 else 0) = ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * 0 \<or> odd n) \<and> (ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * (if odd n then 1 else 0) = ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * 1 \<or> even n)) \<or> (\<Sum>\<^sup>+ n. ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * (if odd n then 1 else 0)) = (\<Sum>\<^sup>+ n. if odd n then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * 1 else ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) * 0)"
         by presburger
       then show ?thesis
         by meson
     qed
     also have "... = (\<Sum>\<^sup>+ x::nat. (if odd x then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x) else  0))" 
       by (meson mult.right_neutral mult_zero_right)
     also have "... = (\<Sum> x::nat. (if odd x then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x) else  0))" 
       by (simp add: nn_integral_count_space_nat)
     also have "... = (\<Sum>n::nat. if odd (2 * n + 1) then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (2 * n + 1)) else 0)" 
     proof(subst suminf_mono_reindex[of "\<lambda>n::nat. 2*n+1" "(\<lambda>x::nat. (if odd x then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) x) else  0))",symmetric])
       show "strict_mono (\<lambda>n::nat. 2 * n + 1)" 
         by (simp add: strict_mono_Suc_iff)
       show "\<And>n. n \<notin> range (\<lambda>n::nat. 2 * n + 1) \<Longrightarrow> (if odd n then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) n) else 0) = 0" using oddE by fastforce
       show "(\<Sum>n. if odd (2 * n + 1) then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (2 * n + 1)) else 0) =
             (\<Sum>n. if odd (2 * n + 1) then ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (2 * n + 1)) else 0)" by simp
     qed
     also have "... = (\<Sum>n::nat. ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1_loop \<gamma> 1) (2 * n + 1)))" 
       by auto 
     also have "... = (\<Sum>n::nat. ennreal (\<gamma>^(2*n)/fact (2*n) - \<gamma>^(2*n+1)/fact (2*n+1)))" 
       by(subst spmf_bernoulli_exp_minus_real_from_0_to_1_loop,auto simp:assms)
     also have "... = (\<Sum>n::nat. \<gamma>^(2*n)/fact (2*n) - \<gamma>^(2*n+1)/fact (2*n+1))"
     proof (rule suminf_ennreal2)
       show "\<And>n::nat. 0 \<le> \<gamma> ^ (2 * n) / fact (2 * n) - \<gamma> ^ (2 * n + 1) / fact (2 * n + 1)"
       proof -
         fix n
         show "0 \<le> \<gamma> ^ (2 * n) / fact (2 * n) - \<gamma> ^ (2 * n + 1) / fact (2 * n + 1)"
         proof -
           have "\<gamma> ^ (2 * n + 1) / fact (2 * n + 1) \<le> \<gamma> ^ (2 * n) / fact (2 * n)"
           proof -
             have 1:"\<gamma> ^ (2 * n + 1) \<le> \<gamma> ^ (2 * n)" using assms 
               by (simp add: mult_left_le_one_le)
             have 2:"(fact (2 * n)::nat) \<le> fact ((2 * n + 1)::nat)" 
               by(rule fact_mono_nat,simp)
             have 3:"0 < (fact (2 * n)::nat)" by simp 
             show "\<gamma> ^ (2 * n + 1) / fact (2 * n + 1) \<le> \<gamma> ^ (2 * n) / fact (2 * n)"
               using 1 2 3 by(simp add:frac_le)
           qed
           then show ?thesis by simp
         qed
       qed
       show "summable (\<lambda>i. \<gamma> ^ (2 * i) / fact (2 * i) - \<gamma> ^ (2 * i + 1) / fact (2 * i + 1))" using summable_2i_2i_plus_1 assms by simp
     qed
     also have "... = (\<Sum>n::nat. (-\<gamma>)^(2*n)/fact (2*n) + (-\<gamma>)^(2*n+1)/fact (2*n+1))" 
       by auto
     also have "... = (\<Sum>n::nat. (-\<gamma>)^(n)/fact n)" 
     proof -
       have " (\<Sum>n. (- \<gamma>) ^ (2 * n) / fact (2 * n) + (- \<gamma>) ^ (2 * n + 1) / fact (2 * n + 1)) = (\<Sum>n. (- \<gamma>) ^ n / fact n)"
       proof -
         have " (\<Sum>n. (- \<gamma>) ^ (2 * n) / fact (2 * n) + (- \<gamma>) ^ (2 * n + 1) / fact (2 * n + 1)) - (\<Sum>n. (- \<gamma>) ^ n / fact n) 
              = (\<Sum>n. (- \<gamma>) ^ (2 * n) / fact (2 * n) + (- \<gamma>) ^ (2 * n + 1) / fact (2 * n + 1) - (- \<gamma>) ^ n / fact n)"
         proof (rule suminf_diff)
           show "summable (\<lambda>n. (- \<gamma>) ^ (2 * n) / fact (2 * n) + (- \<gamma>) ^ (2 * n + 1) / fact (2 * n + 1))" using summable_2i_2i_plus_1 assms by simp
           show "summable (\<lambda>n. (- \<gamma>) ^ n / fact n)" 
             using summable_exp_generic[of"-\<gamma>"] 
             by (simp add: inverse_eq_divide)
         qed
         also have "... = 0"
           unfolding suminf_def sums_def'
         proof 
           let ?f = "\<lambda>n. (-\<gamma>)^n/fact n"
           show 1:"(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) \<longlonglongrightarrow> 0"
             using lim_zero_for_spmf_bernoulli_exp_minus_real_from_0_to_1 assms by simp
           show "\<And>s. (\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) \<longlonglongrightarrow> s \<Longrightarrow> s = 0"
           proof -
             fix s
             assume a:"(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) \<longlonglongrightarrow> s"
             show "s = 0"
             proof(rule LIMSEQ_unique[of "(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i) " "s" "0"])
               show "(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i)  \<longlonglongrightarrow> s" using a by simp
               show "(\<lambda>n. \<Sum>i = 0..n. ?f (2*i) + ?f (2*i+1) - ?f i)  \<longlonglongrightarrow> 0" using 1 by simp
             qed
           qed
         qed
         finally have "(\<Sum>n. (- \<gamma>) ^ (2 * n) / fact (2 * n) + (- \<gamma>) ^ (2 * n + 1) / fact (2 * n + 1)) - (\<Sum>n. (- \<gamma>) ^ n / fact n) = 0" by simp
         then show ?thesis by simp
       qed
       then show ?thesis by simp
     qed
     also have "... = ennreal (exp (- \<gamma>))"
       by (simp add:exp_def inverse_eq_divide)    
     finally show ?thesis by simp
   qed
   then show ?thesis by simp
 qed



lemma spmf_bernoulli_exp_minus_real_from_0_to_1_False[simp]:
  assumes  "0\<le>\<gamma>" and "\<gamma>\<le>1"
  shows "spmf (bernoulli_exp_minus_real_from_0_to_1 \<gamma>) False =  1 - exp(-\<gamma>)" 
  using assms by(simp add:spmf_False_conv_True)

context
  fixes body :: "bool \<Rightarrow> bool spmf"
defines [simp]: "body \<equiv> (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_real_from_0_to_1 1))"

begin
interpretation loop_spmf id body 
  rewrites "body \<equiv>  (\<lambda>b. map_spmf (\<lambda>b'. (if b' then True else False)) (bernoulli_exp_minus_real_from_0_to_1 1))"
  by(fact body_def)

lemma iter_simps_for_bernoulli_exp_minus_real_loop:
  shows "iter k True = (if 1\<le>k then (bernoulli_exp_minus_real_from_0_to_1 1) \<bind> (\<lambda>b. if b then iter (k-1) True else return_spmf False) else return_spmf True)"
proof (cases "1\<le>k")
  case True
  then show ?thesis 
  proof -
    have "iter k True = iter (Suc (k-1)) True" using True by simp
    also have "... = (bernoulli_exp_minus_real_from_0_to_1 1) \<bind> iter (k-1)" by simp
    also have "... = (if 1 \<le> k then (bernoulli_exp_minus_real_from_0_to_1 1) \<bind>  (\<lambda>b. if b then iter (k-1) True else return_spmf False) else return_spmf True)"
    proof -
      have "iter (k-1) = (\<lambda>b. if b then iter (k-1) True else return_spmf False)" by fastforce
      then show ?thesis using True by simp
    qed
    finally show ?thesis by simp
  qed
next
  case False
  then show ?thesis 
  proof -
    have "iter k True = iter 0 True" using False 
      by (simp add: not_less_eq_eq)
    also have "... = return_spmf True" by simp
    also have "... = (if 1 \<le> k then (bernoulli_exp_minus_real_from_0_to_1 1) \<bind> (\<lambda>b. if b then iter (k-1) True else return_spmf False) else return_spmf True)"
      using False by simp
    finally show ?thesis by simp
  qed
qed  

lemma bernoulli_exp_minus_real_loop_conv_iter:
  shows "bernoulli_exp_minus_real_loop k = iter k True" (is "?lhs = ?rhs")
proof (induction k)
  case 0
  then show ?case
    apply(rewrite iter_simps_for_bernoulli_exp_minus_real_loop)
    apply(rewrite bernoulli_exp_minus_real_loop.simps)
    by(simp)
next
  case (Suc k)
  then show ?case 
    apply(rewrite iter_simps_for_bernoulli_exp_minus_real_loop)
    apply(rewrite bernoulli_exp_minus_real_loop.simps)
    using diff_Suc_1 by presburger
qed

lemma lossless_bernoulli_exp_minus_real_loop[simp]:
  shows "lossless_spmf (bernoulli_exp_minus_real_loop k)"
proof -
  have "lossless_spmf (iter k True)"
    using lossless_iter by simp
  then show ?thesis
    using bernoulli_exp_minus_real_loop_conv_iter by simp
qed
end

lemma spmf_bernoulli_exp_minus_real_loop_True [simp]: 
  shows "spmf (bernoulli_exp_minus_real_loop k) True = exp(-k)"
proof (induct k)
  case 0
  then show ?case 
    apply(rewrite bernoulli_exp_minus_real_loop.simps)
    using 0 by simp
next
  case (Suc k)
  then show ?case 
  proof -
    assume step:"spmf (bernoulli_exp_minus_real_loop k) True = exp (- real k)"
    have "ennreal (spmf (bernoulli_exp_minus_real_loop (Suc k)) True) = exp(-(Suc k))"
    proof -
      have "ennreal (spmf (bernoulli_exp_minus_real_loop (Suc k)) True) = ennreal (exp (- 1)) * ennreal (exp (- real k))"
        apply(rewrite bernoulli_exp_minus_real_loop.simps)
        apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
        by(simp add: step)
      also have "... = exp (-1) * exp (-k)"
      proof -
        have 1:"0 < exp (-1::real)" by simp
        have 2:"0 < exp (-k::real)" by simp
        show ?thesis 
          using 1 2 by(simp add:ennreal_mult)
      qed
      also have "... = exp (-(k+1))"
        by (simp add: mult_exp_exp)
      finally show ?thesis by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma spmf_bernoulli_exp_minus_real_loop_False [simp]:
  shows "spmf (bernoulli_exp_minus_real_loop k) False = 1 - exp(-k)"
  using lossless_bernoulli_exp_minus_real_loop spmf_False_conv_True spmf_bernoulli_exp_minus_real_loop_True by simp

lemma lossless_bernoulli_exp_minus_real[simp]:
  shows "lossless_spmf (bernoulli_exp_minus_real \<gamma>)"
proof -
  have 1:"0\<le>\<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>" by simp
  have 2:"\<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>\<le>1" 
    by linarith
  show ?thesis
    apply(rewrite bernoulli_exp_minus_real_def)
    using 1 2 lossless_bernoulli_exp_minus_real_from_0_to_1 lossless_bernoulli_exp_minus_real_loop
    by simp
qed

lemma spmf_bernoulli_exp_minus_real_True[simp]:
  assumes "0\<le>\<gamma>"
  shows "spmf (bernoulli_exp_minus_real \<gamma>) True = exp(-\<gamma>)"
proof (cases "\<gamma>\<le>1")
  case True
  then show ?thesis 
    unfolding bernoulli_exp_minus_real_def
    using assms by simp
next
  case False
  then show ?thesis 
  proof -
    have "ennreal (spmf (bernoulli_exp_minus_real \<gamma>) True) = ennreal (spmf (bernoulli_exp_minus_real_loop (nat \<lfloor>\<gamma>\<rfloor>) \<bind> (\<lambda>b. if b then bernoulli_exp_minus_real_from_0_to_1 (\<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>) else return_spmf b)) True)"
      unfolding bernoulli_exp_minus_real_def 
      apply(subst order_class.leD, simp add:assms)
      using False by simp
    also have "...
         = ennreal (spmf (bernoulli_exp_minus_real_loop (nat \<lfloor>\<gamma>\<rfloor>)) True) * ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1 (\<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>)) True)"
      by(simp add:ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
    also have "... = ennreal (exp (- nat \<lfloor>\<gamma>\<rfloor>)) * ennreal (exp (-\<gamma>+ \<lfloor>\<gamma>\<rfloor>))"
    proof(rewrite spmf_bernoulli_exp_minus_real_loop_True)
      show "ennreal (exp (- real (nat \<lfloor>\<gamma>\<rfloor>))) * ennreal (spmf (bernoulli_exp_minus_real_from_0_to_1 (\<gamma> - \<lfloor>\<gamma>\<rfloor>)) True)
          = ennreal (exp (- (nat \<lfloor>\<gamma>\<rfloor>))) * ennreal (exp (- \<gamma> + \<lfloor>\<gamma>\<rfloor>))"
      proof (rewrite spmf_bernoulli_exp_minus_real_from_0_to_1_True)
        show "0 \<le> \<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>" by simp
        show "\<gamma> - \<lfloor>\<gamma>\<rfloor> \<le> 1" using False by linarith
        show "ennreal (exp (- real (nat \<lfloor>\<gamma>\<rfloor>))) * ennreal (exp (- (\<gamma> - real_of_int \<lfloor>\<gamma>\<rfloor>))) = ennreal (exp (real_of_int (- int (nat \<lfloor>\<gamma>\<rfloor>)))) * ennreal (exp (- \<gamma> + real_of_int \<lfloor>\<gamma>\<rfloor>))" by simp
      qed
    qed
    also have "... = exp (-(\<lfloor>\<gamma>\<rfloor>)) * exp (- \<gamma> + \<lfloor>\<gamma>\<rfloor>)"
      using ennreal_mult' assms  by auto
    also have "... = exp (-\<gamma>)"
      by (simp add: mult_exp_exp)
    finally show ?thesis
      by simp
  qed
qed
    
lemma spmf_bernoulli_exp_minus_real_False[simp]:
  assumes "0\<le>\<gamma>"
  shows "spmf (bernoulli_exp_minus_real \<gamma>) False = 1-exp(-\<gamma>)"
  by (simp add: assms spmf_False_conv_True)

end