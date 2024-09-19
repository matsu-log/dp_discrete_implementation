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

term bind_spmf

lemma ord_spmf_bind:
  assumes "ord_spmf (=) f1 f2" and "\<forall>x. ord_spmf (=) (g1 x) (g2 x)"
  shows "ord_spmf (=) (bind_spmf f1 (\<lambda>x. g1 x)) (bind_spmf f2 (\<lambda>x. g2 x))"
  by (simp add: assms(1) assms(2) bind_spmf_mono')

lemma map_spmf_lambda:
"map_spmf f \<circ> (\<lambda>d. g d) = (\<lambda>d. map_spmf f (g d))"
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

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat_unit_loop :: "nat \<Rightarrow> nat spmf" where
"discrete_laplace_rat_unit_loop v = do {
              a \<leftarrow> bernoulli_exp_minus_rat 1;
              if a = False then return_spmf v
              else  discrete_laplace_rat_unit_loop (v+1)
}"
end

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat_unit :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf" where
"discrete_laplace_rat_unit t s = do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract u t);
  if \<not>d then discrete_laplace_rat_unit t s 
  else do {
    v::nat \<leftarrow> discrete_laplace_rat_unit_loop 0;
    return_spmf ((u::nat)+t * v)
}
}"
end

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat :: "nat \<Rightarrow> nat \<Rightarrow> int spmf" where
"discrete_laplace_rat t s = do {
    y::nat \<leftarrow> discrete_laplace_rat_unit t s;
    b::bool \<leftarrow> bernoulli_rat 1 2;
    if (\<not>b \<and> (y=0)) then discrete_laplace_rat t s
    else if b then return_spmf (-y)
         else return_spmf y
}
"
end

thm discrete_laplace_rat_unit_loop.fixp_induct

lemma discrete_laplace_rat_unit_loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>discrete_laplace_rat_unit_loop. return_pmf None)"
and "(\<And>discrete_laplace_rat_unit_loop'. P discrete_laplace_rat_unit_loop' \<Longrightarrow> P (\<lambda>va. bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf va else discrete_laplace_rat_unit_loop' (va + 1))))"
shows "P discrete_laplace_rat_unit_loop"
  using assms by (rule discrete_laplace_rat_unit_loop.fixp_induct)

thm discrete_laplace_rat.fixp_induct

thm discrete_laplace_rat_unit.fixp_induct

lemma discrete_laplace_rat_unit_fixp_induct[case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>discrete_laplace_rat_unit. P (curry discrete_laplace_rat_unit))"
and "P (\<lambda>discrete_laplace_rat_unit t. return_pmf None)"
and "(\<And>s. P s \<Longrightarrow>
      P (\<lambda>a b. fast_uniform a \<bind>
                (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int a)) \<bind> (\<lambda>d. if \<not> d then s a b else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (u + a * v))))))"
shows "P discrete_laplace_rat_unit"
  using assms by (rule discrete_laplace_rat_unit.fixp_induct)

thm discrete_laplace_rat.fixp_induct

lemma discrete_laplace_rat_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>discrete_laplace_rat. P (curry discrete_laplace_rat))"
and "P (\<lambda>discrete_laplace_rat t. return_pmf None)"
and "(\<And>s. P s \<Longrightarrow>
     P (\<lambda>a b. discrete_laplace_rat_unit a b \<bind> (\<lambda>x. bernoulli_rat 1 2 \<bind> (\<lambda>ba. if \<not> ba \<and> int x = 0 then s a b else if ba then return_spmf (- int x) else return_spmf (int x)))))"
shows "P discrete_laplace_rat"
  using assms by (rule discrete_laplace_rat.fixp_induct)

context
  fixes body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"
  by(fact body_def)

lemma discrete_laplace_rat_unit_loop_conv_while:
  "discrete_laplace_rat_unit_loop 1 = map_spmf snd (while (True,1))"
proof -
  have "discrete_laplace_rat_unit_loop x = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule: discrete_laplace_rat_unit_loop_fixp_induct)
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
        by(rewrite discrete_laplace_rat_unit_loop.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

lemma lossless_discrete_laplace_rat_unit_loop [simp]: "lossless_spmf (discrete_laplace_rat_unit_loop 1)"
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
  then show ?thesis using discrete_laplace_rat_unit_loop_conv_while by simp
qed

lemma lossless_discrete_laplace_rat_unit_loop_zero[simp]:
"lossless_spmf (discrete_laplace_rat_unit_loop 0)"
  apply(rewrite discrete_laplace_rat_unit_loop.simps)
proof(simp, auto, simp add:lossless_bernoulli_exp_minus_rat)
  show "lossless_spmf (discrete_laplace_rat_unit_loop (Suc 0)) " using lossless_discrete_laplace_rat_unit_loop by simp
qed

end

lemma spmf_discrete_laplace_rat_unit_loop_zero_fixp_induct_case_adm:
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

lemma spmf_discrete_laplace_rat_unit_loop_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (discrete_laplace_rat_unit_loop  l) m = 0"
proof (induction rule: discrete_laplace_rat_unit_loop_fixp_induct)
  case adm
  then show ?case 
    using spmf_discrete_laplace_rat_unit_loop_zero_fixp_induct_case_adm by blast
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

lemma spmf_discrete_laplace_rat_unit_loop [simp]: 
  shows "spmf (discrete_laplace_rat_unit_loop 0) m = (exp(-1))^(m) * (1-exp(-1))"
proof -
  have P:"\<forall>k l::nat .  ennreal (spmf (discrete_laplace_rat_unit_loop k) (k+l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
  proof rule+
    fix l
    show "\<And>k.
           ennreal (spmf (discrete_laplace_rat_unit_loop k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have 1:"ennreal (spmf (discrete_laplace_rat_unit_loop k) (k + 0)) = ennreal (1 - (exp (- 1)))"
          apply(rewrite discrete_laplace_rat_unit_loop.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          apply(simp add: spmf_discrete_laplace_rat_unit_loop_zero)
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
                    ennreal (spmf (discrete_laplace_rat_unit_loop k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
           
        have "ennreal (spmf (discrete_laplace_rat_unit_loop k) (k + Suc l)) = exp (- 1) * ennreal (spmf (discrete_laplace_rat_unit_loop (Suc k)) (Suc (k + l)))"
          apply(rewrite discrete_laplace_rat_unit_loop.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal ((exp (- 1)) ^ Suc l * (1- (exp (- 1))))"
          using step[of"Suc k"] apply(simp add: ennreal_mult)
          by (rule semiring_normalization_rules(18))
        finally show ?thesis by simp
      qed
    qed
  qed
  have "ennreal (spmf (discrete_laplace_rat_unit_loop 0) m) = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
  proof -
    have "ennreal (spmf (discrete_laplace_rat_unit_loop 0) m) = ennreal (spmf (discrete_laplace_rat_unit_loop 0) (0+m))"
      by auto
    also have "... = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
      using P by blast
    finally show ?thesis by simp
  qed
  then show ?thesis by simp
qed

thm discrete_laplace_rat.simps

context 
  fixes body :: "bool \<times> nat \<times> nat \<times> nat\<Rightarrow> (bool \<times> nat \<times> nat \<times> nat) spmf"
  defines [simp]: "body \<equiv> (\<lambda>(b, t, s, y). do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract u t);
  if \<not>d then return_spmf (True, t, s, 0)
  else do {
    v::nat \<leftarrow> discrete_laplace_rat_unit_loop 0;
    return_spmf (False,t,s,(u::nat)+t * v)
}
})"

begin
interpretation loop_spmf "fst" body 
  rewrites "body \<equiv> (\<lambda>(b, t, s, y). do {
  u::nat \<leftarrow> fast_uniform t;
  d::bool \<leftarrow> bernoulli_exp_minus_rat (Fract u t);
  if \<not>d then return_spmf (True, t, s, 0)
  else do {
    v::nat \<leftarrow> discrete_laplace_rat_unit_loop 0;
    return_spmf (False,t,s,(u::nat)+t * v)
}
})"
  by(fact body_def)

lemma discrete_laplace_rat_unit_conv_while:
"discrete_laplace_rat_unit t s = map_spmf (snd \<circ> snd \<circ> snd) (while (True,t,s,0))" (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof(induction rule: discrete_laplace_rat_unit_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step discrete_laplace_rat_unit)
    show ?case 
      apply(rewrite while.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step by(simp add:while.simps)
  qed
next 
  have "ord_spmf (=) ?rhs ?lhs"
and "\<And>x. ord_spmf (=) (map_spmf (\<lambda>a. snd (snd (snd a))) (while (False, t,s, x))) (return_spmf x)"
  proof(induction rule: while_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case by simp
  next
    case (step while')
    case 1 show ?case
      apply(rewrite discrete_laplace_rat_unit.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step 
      by (simp add: ord_spmf_bind)
    case 2 show ?case by simp
  qed
  then show "ord_spmf (=) ?rhs ?lhs" by simp
qed

lemma lossless_discrete_laplace_rat_unit:
  assumes "1\<le>t" and "1\<le>s"
  shows "lossless_spmf (discrete_laplace_rat_unit t s)"
proof -
  have "lossless_spmf (while (True, t, s, 0))"
  proof (rule termination_0_1_immediate_invar,clarify)
    fix b::bool and  t1 s1 y::nat
    assume "fst (b,t1,s1,y)"
      and I:"(\<lambda>(b,t1,s1,y). t1 = t \<and> s1= s) (b,t1,s1,y)"
    show "(\<Sum>x = 0..t - 1. (1 / t * (exp (- real_of_rat (Fract (int x) (int t))))))\<le> spmf (map_spmf fst
                    (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t1, s1, u + t1 * v))))))
              False"
    proof - 
      have 1:"spmf (map_spmf fst(fast_uniform t1 \<bind>
               (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                     (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf (False, t1, s1, u + t1 * v))))))
          False
            = spmf (fast_uniform t1 \<bind>
               (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                  (\<lambda>d. if \<not> d then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False))))
          False"       
        apply(simp add:map_spmf_bind_spmf map_spmf_bind_spmf_lambda)
        apply(rewrite map_spmf_lambda_if)
        apply(rewrite map_spmf_return_spmf)
        apply(rewrite map_spmf_bind_spmf)
        apply(rewrite map_spmf_lambda)
        apply(rewrite map_spmf_return_spmf)
        apply(rewrite fst_conv, rewrite fst_conv)
        by simp
      have "ennreal (spmf (fast_uniform t1 \<bind>
               (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                  (\<lambda>d. if \<not> d then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False))))
          False)
          =(\<Sum>x\<in>{0..t1-1}. ennreal (1/t1) *
       (\<Sum>\<^sup>+ xa.
          ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) xa) *
          ennreal (spmf (if \<not> xa then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False)))"  
        apply(simp add:ennreal_spmf_bind nn_integral_measure_spmf spmf_fast_uniform nn_integral_count_space_nat)
        apply(rewrite suminf_finite[of"{0..t1-1}"],simp_all)
      proof -
        have "\<And>n. n\<in>{0..t1-1} \<Longrightarrow> (if n < t1 then 1 / real t1 else 0) = 1/t1" by auto
        then show "(\<Sum>n = 0..t1 - Suc 0.
        ennreal (if n < t1 then 1 / real t1 else 0) *
        (\<Sum>\<^sup>+ x.
           ennreal (spmf (bernoulli_exp_minus_rat (Fract (int n) (int t1))) x) *
           ennreal (spmf (if \<not> x then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False))) =
    (\<Sum>x = 0..t1 - Suc 0.
        ennreal (1 / real t1) *
        (\<Sum>\<^sup>+ xa.
           ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) xa) *
           ennreal (spmf (if \<not> xa then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False)))"
          by simp
      qed
      also have "... = (\<Sum>x = 0..t1 - 1.
        ennreal (1 / real t1) *
        (ennreal (exp(-(of_rat(Fract x t1)))) * (ennreal (spmf (discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False))))"
      proof(simp add: UNIV_bool nn_integral_count_space_finite)
        have "\<And>n::nat. n\<in>{0..(t1-1::nat)} \<Longrightarrow> 0\<le>n" by simp
        then have "\<And>n::nat. n\<in>{0..(t1-1::nat)} \<Longrightarrow> 0\<le> Fract n t1"
          by (metis Zero_rat_def eq_rat(2) gr0I int_ops(1) le_numeral_extra(3) of_nat_0_le_iff of_nat_0_less_iff zero_le_Fract_iff)
        then have "\<And>n::nat. n\<in>{0..(t1-1::nat)} \<Longrightarrow> ennreal (spmf (bernoulli_exp_minus_rat (Fract (int n) (int t1))) True) = ennreal (exp(-(of_rat(Fract n t1))))"
          by simp
        then show "(\<Sum>x = 0..t1 - Suc 0.
        ennreal (1 / real t1) *
        (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int x) (int t1))) True) * ennreal (spmf (discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False))) =
    (\<Sum>x = 0..t1 - Suc 0.
        ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int x) (int t1)))) * ennreal (spmf (discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False)) False)))"
          by simp
      qed
      also have "... = (\<Sum>x = 0..t1 - 1.
        ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int x) (int t1))))))"
      proof(simp add: spmf_bind)
        have "weight_spmf (discrete_laplace_rat_unit_loop 0) = 1"
          using lossless_discrete_laplace_rat_unit_loop_zero by (simp add:lossless_spmf_def)
        then show "(\<Sum>x = 0..t1 - Suc 0. ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int x) (int t1)))) * ennreal (weight_spmf (discrete_laplace_rat_unit_loop 0)))) =
    (\<Sum>x = 0..t1 - Suc 0. ennreal (1 / real t1) * ennreal (exp (- real_of_rat (Fract (int x) (int t1)))))"
          by simp
      qed
      also have "... =  (\<Sum>x = 0..t - 1.
        ennreal (1 / t * (exp (- real_of_rat (Fract (int x) (int t))))))"
        using I by(rewrite ennreal_mult,simp_all)
      also have "... =  (\<Sum>x = 0..t - 1. (1 / t * (exp (- real_of_rat (Fract (int x) (int t))))))"
        by simp
      finally have "ennreal (spmf (fast_uniform t1 \<bind>
               (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                  (\<lambda>d. if \<not> d then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False))))
          False) = (\<Sum>x = 0..t - 1. (1 / t * (exp (- real_of_rat (Fract (int x) (int t))))))"
        by simp
      then have "(\<Sum>x = 0..t - 1. (1 / t * (exp (- real_of_rat (Fract (int x) (int t))))))\<le>(spmf (fast_uniform t1 \<bind>
               (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                  (\<lambda>d. if \<not> d then return_spmf True else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v::nat. return_spmf False))))
          False)"
        using ennreal_le_iff2 by fastforce
      then show ?thesis using 1 by simp
    qed
  next
    show " 0 < (\<Sum>x = 0..t - 1. 1 / real t * exp (- real_of_rat (Fract (int x) (int t))))"
    proof -
      have 1:"0<1/t" using assms by simp
      have 2:"1/t * exp (- real_of_rat (Fract (int 0) (int t))) = 1/t"
        by (simp add: rat_number_collapse(1))
      have "0 < (\<Sum>x=0..0. 1/t * exp (- real_of_rat (Fract (int x) (int t))))" 
        using 1 2 by simp
      also have "... \<le> (\<Sum>x = 0..t - 1. 1 / real t * exp (- real_of_rat (Fract (int x) (int t))))"
        by (rule sum_mono2,simp_all)
      finally show ?thesis by simp
    qed
  next
    show "\<And>sa. fst sa \<Longrightarrow>
          (case sa of (b, t1, s1, y) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow>
          lossless_spmf
           (case sa of
            (b, t, s, y) \<Rightarrow>
              fast_uniform t \<bind>
              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                   (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t, s, u + t * v)))))"
    proof(clarify, simp,rewrite lossless_bernoulli_exp_minus_rat,simp_all)
      fix u::nat
      have "0\<le>u" by simp
      then show "0 \<le> Fract (int u) (int t)"
        using assms(1) zero_le_Fract_iff by auto
      show "0<t" using assms by simp
    qed
  next
    show "\<And>sa s'.
       s' \<in> set_spmf
              (case sa of
               (b, t, s, y) \<Rightarrow>
                 fast_uniform t \<bind>
                 (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                      (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t, s, u + t * v))))) \<Longrightarrow>
       (case sa of (b, t1, s1, y) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow> fst sa \<Longrightarrow> case s' of (b, t1, s1, y) \<Rightarrow> t1 = t \<and> s1 = s"
    proof(clarify,simp)
      fix b1 t1 s1 y1 b2 t2 s2 y2
      assume H:"(b2, t2, s2, y2)
       \<in> set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t, s, u + t * v))))) "
      then show "t2=t \<and> s2=s"
      proof- 
        have "set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t, s, u + t * v)))))
= (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (discrete_laplace_rat_unit_loop 0  \<bind> (\<lambda>v::nat. return_spmf (False, t, s, u + t * v)))))"
          apply(simp add: set_bind_spmf o_def)
          by(rewrite set_spmf_if, simp)
        also have "... = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then {(True,t,s,0)}
                      else set_spmf (discrete_laplace_rat_unit_loop 0)  \<bind> (\<lambda>v::nat. {(False, t, s, u + t * v)})))"
          by(rewrite set_return_spmf, rewrite set_bind_spmf, rewrite o_def, rewrite set_return_spmf, simp)
        also have "...\<subseteq> {(True,t,s,0)} \<union> {(False, t1, s1, y). y \<in> Nats \<and> t1=t \<and>s1 = s}"
        proof (rewrite set_spmf_bind_set,simp_all)
          fix u::nat
          show "set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
         (\<lambda>d. if \<not> d then {(True, t, s, 0)} else set_spmf (discrete_laplace_rat_unit_loop 0) \<bind> (\<lambda>v. {(False, t, s, u + t * v)}))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, y). y \<in> \<nat> \<and> t1 = t \<and> s1 = s}"
          proof (rewrite set_spmf_bind_set,simp_all,rule)
            fix d
            show "set_spmf (discrete_laplace_rat_unit_loop 0) \<bind> (\<lambda>v. {(False, t, s, u + t * v)}) \<subseteq> insert (True, t, s, 0) {(False, t1, s1, y). y \<in> \<nat> \<and> t1 = t \<and> s1 = s}"
            proof (rewrite set_spmf_bind_set,simp_all)
              fix v::nat
              show "u + t * v \<in> \<nat> " unfolding Nats_def by simp
            qed
          qed
        qed
        finally have "set_spmf
   (fast_uniform t \<bind>
    (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
         (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0) else discrete_laplace_rat_unit_loop 0 \<bind> (\<lambda>v. return_spmf (False, t, s, u + t * v)))))
  \<subseteq> {(True, t, s, 0)} \<union> {(False, t1, s1, y). y \<in> \<nat> \<and> t1 = t \<and> s1 = s} "
          by simp 
        then show ?thesis using H by auto
      qed
    qed
  next
    show "case (True, t, s, 0) of (b, t1, s1, y) \<Rightarrow> t1 = t \<and> s1 = s" by simp
  qed
  then show ?thesis using discrete_laplace_rat_unit_conv_while by simp
qed

lemma spmf_discrete_laplace_rat_unit:
  assumes "1\<le>t" and "1\<le>s"
  shows "spmf (discrete_laplace_rat_unit t s) y = 9"

end


context
  fixes body :: "bool \<times> nat \<times> nat \<times> int \<Rightarrow> (bool \<times> nat \<times> nat \<times> int) spmf"
  defines [simp]: "body \<equiv> (\<lambda>(b, t, s, z). 
                            fast_uniform (t::nat) \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t))  \<bind>
                            (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                                 else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s,- y) else return_spmf (False, t, s,y))))))"

begin
interpretation loop_spmf "fst" body 
  rewrites  "body \<equiv> (\<lambda>(b, t, s, z). 
                            fast_uniform (t::nat) \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t))  \<bind>
                            (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                                 else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s,- y) else return_spmf (False, t, s,y))))))"
  by(fact body_def)


lemma discrete_laplace_rat_cov_while:
"discrete_laplace_rat t s = map_spmf (\<lambda>a. snd (snd (snd a))) (while (True, t, s, 0))" (is "?lhs = ?rhs")
proof (rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof (induction rule: discrete_laplace_rat_fixp_induct)
    case adm
    then show ?case by simp
  next
    case bottom
    then show ?case by simp
  next
    case (step discrete_laplace_rat)
    show ?case 
      apply(rewrite while.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step apply(simp)
    proof (clarify)
      fix x::nat 
      have " (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while)) 
            = (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))) "
        by metis
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0)
                                                   else if b then return_spmf (False, t, s, - y) 
                                                   else return_spmf (False, t, s, y))
                                              \<bind>  (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))))) "
        by simp
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (True, t, s, 0)
                                                   else if b then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, - y) 
                                                   else (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, y))
                                              )))) "
        by(rewrite if_else_return_bind_spmf_2, simp)
      also have "... 
            = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              )))) "
      proof -
        have 1:"\<forall>y. (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (False, t, s, y) = return_spmf y"
          by(rewrite o_apply, simp add:while.simps)
        have 2:"(map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while) (True, t, s, 0) = map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))"
          by simp
        show ?thesis 
          using 1 2 by presburger
      qed
      finally have 1:"(loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(x+t * real y)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while)) 
                  = (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              )))) "
        by simp
      have 2:"ord_spmf (=)
                    (loop 0 \<bind>
                      (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
                       in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))
                    (loop 0 \<bind>
                      (\<lambda>v. (let y = \<lfloor>(real x+ real t*real v)/s\<rfloor>
                       in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0))
                                                   else if b then return_spmf (-y) 
                                                   else return_spmf y)
                                              ))))"
      proof (rule ord_spmf_bind, simp, clarify)
        fix v
        show " ord_spmf (=)
          (let y = \<lfloor>(real x + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))
          (let y = \<lfloor>(real x + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a)))(local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))"
        proof -
          have "\<forall>y. ord_spmf (=)
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a)))(local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))"
          proof (clarify, rule ord_spmf_bind,simp,clarify)
            fix y b
            show "ord_spmf (=) (if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)
                               (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (local.while (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y)"
              using step by simp
          qed
          then show ?thesis by meson
        qed
      qed
      show " ord_spmf (=)
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>ba. if \<not> ba \<and> y = 0 then discrete_laplace_rat t s else if ba then return_spmf (- y) else return_spmf y)))
        (loop 0 \<bind>
         (\<lambda>y. (let y = \<lfloor>(real x + real t * real y) / real s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> local.while))"
        using 1 2 by simp
    qed
  qed
next  
  have "ord_spmf (=) ?rhs ?lhs"
  and "\<And>x. ord_spmf (=) (map_spmf (\<lambda>a. snd (snd (snd a))) (while (False, t,s, x))) (return_spmf x)"
  proof (induction rule: while_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case bottom case 2 show ?case by simp
  next
    case (step while')
    case 1 show ?case 
      apply(rewrite discrete_laplace_rat.simps)
      apply(clarsimp)
      apply(clarsimp simp add: map_spmf_bind_spmf)
      apply(clarsimp simp add: map_spmf_bind_spmf_lambda)
      apply(clarsimp intro!: ord_spmf_bind_reflI)
      using step apply(simp)
    proof 
      fix u  
      show "ord_spmf (=)
        (loop 0 \<bind>
         (\<lambda>v. (let y = \<lfloor>(u+t*real v)/s\<rfloor>
               in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
              map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while'))
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(u+t*real v)/s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))"
      proof (rule ord_spmf_bind, simp, clarify)
        fix v
      have "\<forall>y. ord_spmf (=)
        (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
         map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
        (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
      proof 
        fix y
        have 1:"ord_spmf (=)
              (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
              (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) 
                                            else if b then return_spmf (- y) else return_spmf y))"
        proof -
          have "bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
                map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while' 
              = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (True, t, s, 0)
                                                   else if b then (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (False, t, s, - y) 
                                                   else (map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while') (False, t, s, y)))"
            by(simp add: if_else_return_bind_spmf_2)
          also have "... 
               = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                   else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                   else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y))))"
            by(rewrite o_apply, rewrite o_apply,rewrite o_apply,simp)
          finally have 1:"bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
                map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while' 
                      = bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                          else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                          else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y))))"
            by simp
          have 2:"ord_spmf (=) (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
                                                                else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, -y))
                                                                else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y)))))
                             (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) 
                                                           else if b then return_spmf (- y) else return_spmf y))"
          proof (rule ord_spmf_bind, simp ,clarify)
            fix b
            show "ord_spmf (=)
          (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0))
           else if b then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, - y)) else map_spmf (\<lambda>a. snd (snd (snd a))) (while' (False, t, s, y)))
          (if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y)"
              using step.IH(2)[of"y"] step.IH(2)[of"-y"] by simp
          qed
          show ?thesis 
            using 1 2 by simp
        qed
        have 2:"ord_spmf (=) (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then map_spmf (\<lambda>a. snd (snd (snd a))) (while' (True, t, s, 0)) else if b then return_spmf (- y) else return_spmf y))
                             (bernoulli_rat (Suc 0) 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
          by(rule ord_spmf_bind,simp,simp add:step.IH(1))
        show "ord_spmf (=)
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
          (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
          using 1 2 spmf.leq_trans by blast
      qed
      then show "ord_spmf (=)
          ((let y = \<lfloor>(u + real t * real v) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) \<bind>
           map_spmf (\<lambda>a. snd (snd (snd a))) \<circ> while')
          (let y = \<lfloor>(u + real t * real v) / real s\<rfloor> in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y))"
        by meson
      qed
    qed
    case 2 show ?case by simp
  qed
  then show "ord_spmf (=) ?rhs ?lhs" by simp
qed

lemma map_spmf_lambda_if:
"map_spmf f \<circ> (\<lambda>d. if b then spmf_1 else spmf2) = (\<lambda>d. if b then map_spmf f spmf_1 else map_spmf f spmf2)"
  by auto

lemma map_spmf_return_spmf:
"map_spmf f (return_spmf p) = return_spmf (f p)"
  by simp

lemma map_spmf_let:
"map_spmf f \<circ> (\<lambda>v. let x = t;y= g x in h x) = (\<lambda>v. let x = t;y= g x in map_spmf f (h x)) "
  by simp

lemma discrete_laplace_rat_body_map_spmf_fst:
"map_spmf fst
                    (fast_uniform t \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) 
                  = fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))"
proof -
  have "map_spmf fst
                    (fast_uniform t \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) 
          = 
     fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Rat.Fract (int u) (int t)) \<bind>
          map_spmf fst \<circ>  (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                else loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))"   
        by (simp add: map_spmf_bind_spmf map_spmf_bind_spmf_lambda)
      also have "... = 
      fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))"  
      proof (rule bind_spmf_cong,simp,rule bind_spmf_cong,simp_all,clarify)
        fix x xa
        show "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))) =
       loop 0 \<bind> (\<lambda>v. bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> \<lfloor>(real x + real t * real v) / real s\<rfloor> = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
        proof -
          have "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))) =
        (loop 0 \<bind>
          map_spmf fst \<circ>  (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
            by (simp add: map_spmf_bind_spmf)
          also have "...
                   = (loop 0 \<bind>
           (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))"
          proof (rule bind_spmf_cong,simp_all)
            fix xa
            show "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
          bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> \<lfloor>(real x + real t * real xa) / real s\<rfloor> = 0 then return_spmf True else if b then return_spmf False else return_spmf False)"
            proof - 
              have "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in map_spmf fst (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
                by metis
              also have "... = (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
              proof -
                have 1:"\<And>y. map_spmf fst (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))
                         =  bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)"
                  by(simp add:map_spmf_bind_spmf, rule bind_spmf_cong, simp_all)
                show ?thesis by(simp add:1)
              qed
              finally have "map_spmf fst
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))) =
           (let y = \<lfloor>(real x + real t * real xa) / real s\<rfloor>
            in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False))"
                by simp
              then show ?thesis by simp
            qed
          qed
          finally have "map_spmf fst
        (loop 0 \<bind>
         (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))
      = (loop 0 \<bind>
           (\<lambda>v. let y = \<lfloor>(real x + real t * real v) / real s\<rfloor>
              in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))"
            by simp 
          then show ?thesis by simp
        qed
      qed
      ...      finally show ?thesis
        by simp
    qed 



(*declare[[show_types,show_sorts]]*)
lemma lossless_discrete_laplace_rat:
  assumes "1\<le>s" and "1\<le>t"
  shows "lossless_spmf (discrete_laplace_rat t s)"
proof- 
  have "lossless_spmf (while (True,t,s,0))"
  proof (rule termination_0_1_immediate_invar,clarify)
    fix b::bool and t1 s1::nat and z::int
    assume "fst (b,t1,s1,z)"
    and I:"(\<lambda>(b,t1,s1,z). t1=t \<and> s1=s) (b,t1,s1,z)"
    show "1/t * (1 - exp (- 1)) *  (inverse (2::nat)) \<le> spmf (map_spmf fst
                    (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y)))))))
              False"
    proof -
      have "ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False) =
            ennreal (spmf (fast_uniform t1 \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
           (\<lambda>d. if \<not> d then return_spmf True
                else (loop 0 \<bind>
                     (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf True else if b then return_spmf False else return_spmf False)))))) False)"
        by(simp add: discrete_laplace_rat_body_map_spmf_fst)
      also have "... = (\<Sum>u::nat. ennreal (spmf (fast_uniform t1) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t1)) True) *
        (\<Sum>\<^sup>+ v. ennreal (exp (-1)^v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
        apply(simp add:ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_finite UNIV_bool)
        using nn_integral_count_space_nat by blast
      also have "... = (\<Sum>u\<in>{0::nat..t1-1}. ennreal (spmf (fast_uniform t1) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t1)) True) *
        (\<Sum>\<^sup>+ v. ennreal (exp (-1)^v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
      proof (rule suminf_finite)
        show "finite {0::nat..t1-1}" by simp
        fix u 
        assume u:"u \<notin> {0..t1 - 1}"
        show "ennreal (spmf (fast_uniform t1) u) *
         (ennreal (spmf (bernoulli_exp_minus_rat (Fract (int u) (int t1))) True) *
          (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2)))=0"
        proof -
          have "spmf (fast_uniform t1) u = 0"
            using u spmf_fast_uniform by simp 
          then show ?thesis by simp
        qed
      qed
      also have "... \<ge> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
      proof -
        have 1:"\<forall>u\<in>{0::nat..t1-1}. 0 \<le> (Fract u t1)" using I assms
          by (simp add: zero_le_Fract_iff)
        have 2:"\<forall>u\<in>{0::nat..t1-1}. u < t1" 
          using I assms by auto
        show ?thesis using 1 2 spmf_fast_uniform  
          by(simp)
      qed
      finally have 1:"
        ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)
  \<ge> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse 2 * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse 2))))"
        by simp
      have 2:"(\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))))
      \<le>  (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * (inverse (2::nat) * ennreal (spmf (if \<lfloor>(u+t1*real v)/s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + inverse (2::nat)))))"
      proof (rule ordered_comm_monoid_add_class.sum_mono)
        fix u
        have 1:"(\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (inverse (real 2))) \<le> 
               (\<Sum>\<^sup>+ v.
               ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
               (ennreal (inverse (real 2)) * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + ennreal (inverse (real 2))))"
        proof (rewrite nn_integral_mono,simp_all,clarify)
          fix x
          show "ennreal (exp (- 1) ^ x * (1 - exp (- 1))) * (inverse 2::ennreal) \<le> ennreal (exp (- 1) ^ x * (1 - exp (- 1))) * ((inverse 2 + inverse 2)::ennreal)"
          proof -
            have "(inverse 2::ennreal) \<le> (inverse 2 + inverse 2)"
              by simp
            then show ?thesis 
              by (simp add: distrib_left)
          qed
        qed
        have 2:"ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1))))) \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))))"
          by simp
        then show "ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * ennreal (inverse (real 2))))
         \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) *
             (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
                (ennreal (inverse (real 2)) * ennreal (spmf (if \<lfloor>(real u + real t1 * real v) / real s1\<rfloor> = 0 then return_spmf True else return_spmf False) False) + ennreal (inverse (real 2)))))"
          using 1 2 
          by (metis (no_types, lifting) ennreal_eq_0_iff ennreal_mult_cancel_left ennreal_mult_le_mult_iff not_exp_le_zero top_neq_ennreal)
      qed
      have 3:"(\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat))))) \<le> 
         ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)"
        using 1 2 by simp
      have 4:" (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (ennreal (1 - exp (- 1)) *  (inverse (2::nat))))) \<le>
      (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat))))) "
      proof -
        have "ennreal (1 - exp (- 1)) *  (inverse (2::nat)) = (\<Sum> v\<in>{0::nat}. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by simp
        also have "...\<le> (\<Sum> v::nat. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by(rule sum_le_suminf,simp_all)
        also have "... = (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))" 
          using nn_integral_count_space_nat by simp
        finally have 1:"ennreal (1 - exp (- 1)) *  (inverse (2::nat)) \<le> (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
          by simp
        show ?thesis 
        proof (rewrite sum_mono,simp_all)
          fix u 
          show "ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (ennreal (1 - exp (- 1)) * inverse 2))
         \<le> ennreal (1 / real t1) * (ennreal (exp (- real_of_rat (Fract (int u) (int t1)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * inverse 2))"
          proof(rule mult_mono,simp_all,rule mult_mono,simp_all)
            show "ennreal (1 - exp (- 1)) * inverse 2 \<le> (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) * inverse 2)"
            proof -
              have "ennreal (1 - exp (- 1)) *  (inverse 2) = (\<Sum> v\<in>{0::nat}. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
                by simp
              also have "...\<le> (\<Sum> v::nat. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse (2::nat)))"
                by(rule sum_le_suminf,simp_all)
              also have "... = (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *  (inverse 2))" 
                using nn_integral_count_space_nat by simp
              finally show ?thesis by simp
            qed
          qed
        qed
      qed
      have 5:"ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat))) \<le>
       (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) *
       (ennreal (exp(-(of_rat(Fract u t1)))) *
         (ennreal (1 - exp (- 1)) *  (inverse (2::nat)))))"
      proof -
        have "(ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat)))) = (ennreal (1/t1 * (1 - exp (- 1)) *  (inverse (2::nat))))"
          using I by simp
        also have "... = (ennreal (1/t1) * (ennreal 1 * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
        proof(rewrite ennreal_mult,simp_all)
          have " ennreal ((1 - exp (- 1)) / real t1) * inverse 2 =  ennreal (1/ t1) * ennreal (1 - exp (- 1)) * inverse 2"
            by(simp add: divide_inverse ennreal_mult' mult.commute)
          also have "... = (ennreal (1/t1) * (ennreal 1 * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
            by (simp add: mult.assoc)
          finally show "ennreal ((1 - exp (- 1)) / real t1) * inverse 2 = ennreal (1 / real t1) * (ennreal (1 - exp (- 1)) * inverse 2)"
            by simp
        qed
        also have "... = (ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract 0 t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2)))) "
        proof- 
          have "Fract 0 t1 = 0" by(rule rat_number_collapse)
          then show ?thesis by simp
        qed
        also have "... \<le> 
              (\<Sum>u\<in>{0::nat}. ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract u t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
          by simp
        also have "... \<le> (\<Sum>u\<in>{0::nat..t1-1}. ennreal (1/t1) * (ennreal (exp(-(of_rat(Fract u t1)))) * (ennreal (1 - exp (- 1)) *  (inverse 2))))"
          by(rule sum_mono2, simp_all)
        finally show ?thesis by simp
      qed
      have "ennreal (1/t * (1 - exp (- 1)) *  (inverse (2::nat)))\<le>
             ennreal (spmf (map_spmf fst (fast_uniform t1 \<bind>
                     (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t1)) \<bind>
                          (\<lambda>d. if \<not> d then return_spmf (True, t1, s1, 0)
                               else loop 0 \<bind>
                                    (\<lambda>v. let x = u + t1 * v; y = \<lfloor>real x / real s1\<rfloor>
                                         in bernoulli_rat 1 2 \<bind>
                                            (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t1, s1, 0) else if b then return_spmf (False, t1, s1, - y) else return_spmf (False, t1, s1, y))))))) False)"
        using 3 4 5 by order
      then show ?thesis by simp
    qed
  next
    show "0< 1/t * (1 - exp (- 1)) *  (inverse (2::nat))"
    proof -
      have 1:"0 < 1/t" using assms by auto
      have "exp(-1::real)< 1" 
        by(rewrite exp_less_one_iff,simp)
      then have 2:"0 < 1-exp(-1::real)" by simp
      have 3:"0<inverse (2::nat)" by simp
      show ?thesis using 1 2 3 by auto
    qed
  next
    show "case (True, t, s, 0) of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s" by simp
  next
    show "\<And>sa. fst sa \<Longrightarrow>
          (case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow>
          lossless_spmf
           (case sa of
            (b, t, s, z) \<Rightarrow>
              fast_uniform t \<bind>
              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                   (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                        else loop 0 \<bind>
                             (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                  in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
    proof(clarify,auto)
      show "0<t" using assms by simp
    next
      fix x::nat
      assume A1:"x \<in> set_spmf (fast_uniform t)"
      show "lossless_spmf (bernoulli_exp_minus_rat (Fract (int x) (int t)))"
      proof-
        have "0\<le> Fract (int x) (int t)"
          using assms(2) zero_le_Fract_iff by auto 
        then show ?thesis by(rule lossless_bernoulli_exp_minus_rat)
      qed
    next
      fix a x xa xb
      show "lossless_spmf
        (let y = \<lfloor>(x + real t * xb) / real s\<rfloor>
         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
      proof -
        have 1:"\<And>y. lossless_spmf (bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
          by simp
        show ?thesis 
          by (metis (no_types) "1")
      qed
    qed
  next
    show "\<And>sa s'.
       s' \<in> set_spmf
              (case sa of
               (b, t, s, z) \<Rightarrow>
                 fast_uniform t \<bind>
                 (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                      (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                           else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                     in bernoulli_rat 1 2 \<bind>
                                        (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))) \<Longrightarrow>
       (case sa of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s) \<Longrightarrow> fst sa \<Longrightarrow> (case s' of (b, t1, s1, z) \<Rightarrow> t1 = t \<and> s1 = s)"
    proof (clarify)
      fix b1 t1 s1 z1 b2 t2 s2 z2
      assume H:"(b2,t2,s2,z2)\<in> set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
      then show "t2 = t \<and> s2 = s"
      proof -
        have "set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))
            = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (set_spmf \<circ> (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          by (simp add: set_bind_spmf o_def)
        also have "... = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          by(rewrite set_spmf_if,simp)
        also have "... = (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (set_spmf \<circ> (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
          using set_bind_spmf 
          by metis
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))))"
        proof -
          have "\<And>u. set_spmf \<circ> (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))
                  =  (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))"
            by (metis set_spmf_if)
          then show ?thesis by auto
        qed
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  set_spmf \<circ> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))"
        proof - 
          have "\<And>u. (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))
                  =  (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind> set_spmf \<circ> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))"
            by (meson set_bind_spmf)
          then show ?thesis by auto
        qed
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then set_spmf (return_spmf (True, t, s, 0)) else set_spmf (if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y)))))))"
          by(rewrite set_spmf_if,simp)
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then set_spmf (return_spmf (True, t, s, 0))
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then set_spmf (return_spmf (True, t, s, 0)) else if b then set_spmf(return_spmf (False, t, s, - y)) else set_spmf (return_spmf (False, t, s, y)))))))"
          by(rewrite if_distrib,simp)
        also have "... =  (set_spmf (fast_uniform t))\<bind>
             (\<lambda>u. set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
                 (\<lambda>d. if \<not> d then {(True, t, s, 0)}
                      else set_spmf (loop 0) \<bind>
                           (\<lambda>v. (let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in set_spmf (bernoulli_rat 1 2) \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})))))"
          by(rewrite set_return_spmf, rewrite set_return_spmf, rewrite set_return_spmf, rewrite set_return_spmf, simp)
        also have "... \<subseteq> {(True,t,s,0)} \<union> {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"  
        proof (rewrite set_spmf_bind_set,simp_all)
          fix u
          show "set_spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) \<bind>
         (\<lambda>d. if \<not> d then {(True, t, s, 0)}
              else set_spmf (loop 0) \<bind>
                   (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                        in set_spmf (bernoulli_rat 1 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"
          proof (rewrite set_spmf_bind_set,simp_all,rule)
            fix d
            show "set_spmf (loop 0) \<bind>
         (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
              in set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)}))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
            proof(rewrite set_spmf_bind_set,simp_all)
              fix v::nat 
              have 1:"\<And>y::int. set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)})
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s}"
                unfolding Ints_def
                by(rewrite set_spmf_bind_set,auto)
              show "(let y = \<lfloor>(real u + real t * real v) / real s\<rfloor> in set_spmf (bernoulli_rat (Suc 0) 2) \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then {(True, t, s, 0)} else if b then {(False, t, s, - y)} else {(False, t, s, y)}))
         \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
                using 1 by meson
            qed
          qed
        qed
        finally have "set_spmf
           (fast_uniform t \<bind>
            (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
                 (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                      else loop 0 \<bind>
                           (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s, - y) else return_spmf (False, t, s, y))))))
            \<subseteq> insert (True, t, s, 0) {(False, t1, s1, z). z \<in> \<int> \<and> t1=t \<and>s1 = s} "
          by simp
        then show ?thesis using H by auto
      qed
    qed
  qed
  then show ?thesis by (simp add:discrete_laplace_rat_cov_while)
qed
               
end





lemma spmf_discrete_laplace_rat[simp]:
  assumes "1\<le>s" and "1\<le>t"
  shows "spmf (discrete_laplace_rat t s) z = (exp(t/s)-1)/(exp(t/s)+1) * exp (- abs z * t/s)"
proof (rule spmf_ub_tight)
  fix x
  show "spmf (discrete_laplace_rat t s) x \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
  proof (induction rule: discrete_laplace_rat_fixp_induct)
    case adm
    then show ?case 
    proof (simp add: ccpo.admissible_def fun_lub_def spmf_lub_spmf,clarify)
      fix A
      assume CA: "Complete_Partial_Order.chain spmf.le_fun A" and A: "A \<noteq> {}" and
        H: "\<forall>xa\<in>A. spmf (xa (t, s)) x \<le> (exp (t/s)-1) * exp (- (\<bar>real_of_int x\<bar> * t/s)) / (exp (t/s)+1)"
      have P:"spmf (lub_spmf {y. \<exists>f\<in>A. y = f (t, s)}) x =  (\<Squnion>p\<in>{y. \<exists>f\<in>A. y = f (t, s)}. spmf p x)"
      proof (rule spmf_lub_spmf)
        show "Complete_Partial_Order.chain (ord_spmf (=)) {y. \<exists>f\<in>A. y = f (t, s)}" 
          by (simp add: CA chain_fun)
      next
        show "{y. \<exists>f\<in>A. y = f (t, s)} \<noteq> {}" using A by blast
      qed
      also have "... \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
      proof (rule conditionally_complete_lattice_class.cSUP_least)
        show "{y. \<exists>f\<in>A. y = f (t, s)} \<noteq> {}" using A by auto 
        fix p
        assume "p\<in> {y. \<exists>f\<in>A. y = f (t, s)} "
        then show "spmf p x \<le> (exp (t/s)-1)/(exp (t/s)+1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
          using H by auto
      qed
      finally show "spmf (lub_spmf {y. \<exists>f\<in>A. y = f (t, s)}) x \<le> (exp (t/s)-1) * exp (- (\<bar>real_of_int x\<bar>*t/s))/(exp (t/s)+1)"
        by simp
    qed         
  next
    case bottom
    then show ?case by simp
  next
    case (step discrete_laplace_rat)
    then show ?case
    proof -
      have "ennreal (spmf
     (fast_uniform t \<bind>
      (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t)) \<bind>
           (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                else loop 0 \<bind>
                     (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                          in bernoulli_rat 1 2 \<bind> (\<lambda>ba. if \<not> ba \<and> y = 0 then discrete_laplace_rat t s else if ba then return_spmf (- y) else return_spmf y)))))
      x)
    \<le> (exp (t/s)-1)/(exp (t/s)+1)*exp (- \<bar>real_of_int x\<bar> * t/s)"
      proof -
        have "ennreal (spmf (fast_uniform t \<bind>
                        (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                         (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                              else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                 in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))z) =
                  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
                          (\<Sum>\<^sup>+ d. ennreal (spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) d) *
                                  ennreal (spmf (if \<not> d then discrete_laplace_rat t s
                                                 else loop 0 \<bind>
                                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor> in
                                                     bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                else if b then return_spmf (- y) else return_spmf y)))z)))"
          by (simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        also have "... =  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
          by(simp add: nn_integral_count_space_finite UNIV_bool)
        also have "... = (\<Sum> u::nat. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
          using nn_integral_count_space_nat by blast
        also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )"
        proof (rule suminf_finite)
          show "finite {0::nat..t-1}" by simp
          show "\<And>u. u \<notin>  {0::nat..t-1} \<Longrightarrow> ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z))= 0"
          proof -
            fix u::nat
            assume u:"u \<notin> {0..t - 1}"
            then show "ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z))= 0"
            proof -
            have "spmf (fast_uniform t) u = 0"
              using u spmf_fast_uniform by simp 
            then show ?thesis by simp
          qed
        qed
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             z)
       )
      )" 
      proof -
        have 1:"\<forall>u\<in>{0::nat..t-1}. 0 \<le> (Fract u t)" using assms 
          by (simp add: zero_le_Fract_iff)
        have 2:"\<forall>u\<in>{0::nat..t-1}. u < t" 
          using assms(2) by auto
        show ?thesis using 1 2 spmf_fast_uniform by simp
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *
                                                       ennreal (spmf (let y = \<lfloor>(u+t*real v)/s\<rfloor> in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                            else if b then return_spmf (- y) 
                                                                                                                                 else return_spmf y))
              z))))" 
        by (simp add: ennreal_spmf_bind nn_integral_measure_spmf)
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                                       ennreal (spmf (bernoulli_rat 1 2 \<bind>  (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                  else if b then return_spmf (- y) 
                                                                                                       else return_spmf y))z)))
      ))"
        by metis
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) * (let y = \<lfloor>(u+t*real v)/s\<rfloor> in 
                                             (inverse 2 * ennreal (spmf ((\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                          else if b then return_spmf (- y) 
                                                                                                               else return_spmf y) False) z) 
                                               +
                                              inverse 2 * ennreal (spmf ((\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                          else if b then return_spmf (- y) 
                                                                                                                  else return_spmf y) True) z)
                                             ))
     )))"
        by(simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_finite UNIV_bool) 
      also have  "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (inverse 2 * ennreal (spmf (if y = 0 then discrete_laplace_rat t s 
                                                                              else return_spmf y) z) 
                                               +
                                              inverse 2 * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
        by presburger
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal (spmf (if y = 0 then discrete_laplace_rat t s 
                                                                              else return_spmf y) z) 
                                               +
                                              1/(2::nat) * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
        using inverse_eq_divide[of "2"] by simp
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (spmf (loop 0) v) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal ((if y = 0 then spmf (discrete_laplace_rat t s) z
                                                                     else spmf (return_spmf y) z)) 
                                               +
                                              1/(2::nat) * ennreal (spmf (return_spmf (- y)) z)
                                             )))))"
      proof-
        have "\<forall>y x. (spmf (if y = 0 then discrete_laplace_rat t s else return_spmf y) x) 
                   =(if y = 0 then spmf (discrete_laplace_rat t s) x else spmf (return_spmf y) x)"
          using if_distrib by simp
        then show ?thesis by simp
      qed
      also have "... = (\<Sum> u\<in>{0::nat..t-1}. ennreal (1/t) *
       (ennreal (1-exp(-(of_rat (Fract u t)))) * ennreal (spmf (discrete_laplace_rat t s) z) +
        ennreal (exp(-(of_rat (Fract u t)))) * (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *(let y = \<lfloor>(u+t*real v)/s\<rfloor> in
                                             (1/(2::nat) * ennreal ((if y = 0 then spmf (discrete_laplace_rat t s) z
                                                                     else if y = z then 1 else 0)) 
                                               +
                                              1/(2::nat) * ennreal ( (if (- y)=z then 1 else 0))
                                             )))))"
      proof -
        have 1:"\<forall> x y. spmf (return_spmf y) x = (if y=x then 1 else 0)" by simp
        have 2:"\<forall> x y. spmf (return_spmf (uminus y)) x = (if (uminus y)=x then 1 else 0)" by simp
        show ?thesis by(rewrite 1,rewrite 2,simp) 
      qed
      finally have "ennreal (spmf (fast_uniform t \<bind>
                        (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                         (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                              else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                 in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))z) =
                   (\<Sum>u = 0..t - 1. ennreal (1/t)*
                   (ennreal (1 - exp (- real_of_rat (Fract u t))) * ennreal (spmf (discrete_laplace_rat t s) z) +
                    ennreal (exp (- real_of_rat (Fract u t))) *
                            (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
                                   (let y = \<lfloor>(u+t*real v)/s\<rfloor>
                                    in ennreal (1 / real 2) * ennreal (if y = 0 then spmf (discrete_laplace_rat t s) z else if y = z then 1 else 0) 
                                     + ennreal (1 / real 2) * ennreal (if - y = z then 1 else 0)))))"
        by simp

(*
      then show ?thesis by simp
    qed
  qed
  show "(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = ennreal (weight_spmf (discrete_laplace_rat t s))"
  proof - 
    have 1:"ennreal (weight_spmf (discrete_laplace_rat t s)) = 1"
      using lossless_discrete_laplace_rat lossless_spmf_def by auto
    have 2:"(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = 1" 
*)

end