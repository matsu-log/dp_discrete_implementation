theory Discrete_Laplace_rat
  imports "Bernoulli_exp_minus_rat"
          "Probabilistic_While.Fast_Dice_Roll"
          "Bernoulli_rat"
          "Probabilistic_While.While_SPMF"
begin

term "fast_uniform 3" 

context notes [[function_internals]] begin
partial_function (spmf) loop :: "nat \<Rightarrow> nat spmf" where
"loop v = do {
              a \<leftarrow> bernoulli_exp_minus_rat 1;
              if a = False then return_spmf v
              else  loop (v+1)
}"
end

context notes [[function_internals]] begin
partial_function (spmf) discrete_laplace_rat :: "nat \<Rightarrow> nat \<Rightarrow> int spmf" where
"discrete_laplace_rat t s = bind_spmf 
                              (fast_uniform t) 
                              (\<lambda>u. bind_spmf 
                                      (bernoulli_exp_minus_rat (Fract u t))
                                      (\<lambda>d. if \<not>d then (discrete_laplace_rat t s)
                                           else bind_spmf (loop 0) (\<lambda>v. let x = u + t * v in
                                                                        let y = floor (x/s) in 
                                                                        bind_spmf 
                                                                                 (bernoulli_rat 1 2) 
                                                                                 (\<lambda>b. if (\<not>b \<and> (y=0)) then discrete_laplace_rat t s 
                                                                                      else if b then return_spmf (-y) 
                                                                                           else return_spmf y ) )))
"
end

thm loop.fixp_induct

lemma loop_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>loop. return_pmf None)"
and "(\<And>loop'. P loop' \<Longrightarrow> P (\<lambda>va. bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf va else loop' (va + 1))))"
shows "P loop"
  using assms by (rule loop.fixp_induct)

thm discrete_laplace_rat.fixp_induct

lemma discrete_laplace_rat_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>discrete_laplace_rat. P (curry discrete_laplace_rat))"
and "P (\<lambda>discrete_laplace_rat t. return_pmf None)"
and "(\<And>discrete_laplace_rat. P discrete_laplace_rat \<Longrightarrow>
      P (\<lambda>a b. fast_uniform a \<bind>
                (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int a)) \<bind>
                     (\<lambda>d. if \<not> d then discrete_laplace_rat a b
                          else loop 0 \<bind>
                               (\<lambda>v. let x = u + a * v; y = \<lfloor>real x / real b\<rfloor>
                                    in bernoulli_rat 1 2 \<bind> (\<lambda>ba. if \<not> ba \<and> y = 0 then discrete_laplace_rat a b else if ba then return_spmf (- y) else return_spmf y))))))"
shows "P discrete_laplace_rat"
  using assms by (rule discrete_laplace_rat.fixp_induct)

context
  fixes body :: "bool \<times> nat \<Rightarrow> (bool \<times> nat) spmf"
defines [simp]: "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"

begin
interpretation loop_spmf fst body 
  rewrites "body \<equiv> (\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"
  by(fact body_def)

lemma loop_conv_while:
  "loop 1 = map_spmf snd (while (True,1))"
proof -
  have "loop x = map_spmf snd (while (True, x))" (is "?lhs = ?rhs") for x
  proof (rule spmf.leq_antisym)
    show "ord_spmf (=) ?lhs ?rhs"
    proof (induction arbitrary: x rule: loop_fixp_induct)
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
        by(rewrite loop.simps)(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def intro!: ord_spmf_bind_reflI)
      case 2 show ?case by simp
    qed
    then show "ord_spmf (=) ?rhs ?lhs" by -
  qed
  from this[of 1] show ?thesis by(simp cong:map_spmf_cong)
qed

lemma lossless_loop [simp]: "lossless_spmf (loop 1)"
proof - 
  let ?body = "(\<lambda>(b,k'::nat). map_spmf (\<lambda>b'. (if b' then (True,k'+1) else (False,k'))) (bernoulli_exp_minus_rat 1))"
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
  then show ?thesis using loop_conv_while by simp
qed
end

lemma spmf_loop_zero_fixp_induct_case_adm:
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

lemma spmf_loop_zero:
  shows "\<forall>l.  l>m \<longrightarrow> spmf (loop  l) m = 0"
proof (induction rule: loop_fixp_induct)
  case adm
  then show ?case 
    using spmf_loop_zero_fixp_induct_case_adm by blast
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

lemma spmf_loop [simp]: 
  assumes "1\<le>m"
  shows "spmf (loop 0) m = (exp(-1))^(m) * (1-exp(-1))"
proof -
  have P:"\<forall>k l::nat .  ennreal (spmf (loop k) (k+l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
  proof rule+
    fix l
    show "\<And>k.
           ennreal (spmf (loop k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
    proof (induct l)
      case 0
      then show ?case
      proof -
        have 1:"ennreal (spmf (loop k) (k + 0)) = ennreal (1 - (exp (- 1)))"
          apply(rewrite loop.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          apply(simp add: spmf_loop_zero)
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
                    ennreal (spmf (loop k) (k + l)) = ennreal ((exp(-1))^(l) * (1-exp(-1)))"
           
        have "ennreal (spmf (loop k) (k + Suc l)) = exp (- 1) * ennreal (spmf (loop (Suc k)) (Suc (k + l)))"
          apply(rewrite loop.simps)
          apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf UNIV_bool nn_integral_count_space_finite)
          done
        also have "... =  ennreal ((exp (- 1)) ^ Suc l * (1- (exp (- 1))))"
          using step[of"Suc k"] apply(simp add: ennreal_mult)
          by (rule semiring_normalization_rules(18))
        finally show ?thesis by simp
      qed
    qed
  qed
  have "ennreal (spmf (loop 0) m) = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
  proof -
    have "ennreal (spmf (loop 0) m) = ennreal (spmf (loop 0) (0+m))"
      using assms by auto
    also have "... = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
      using P by blast
    finally show ?thesis by simp
  qed
  then show ?thesis by simp
qed

thm discrete_laplace_rat.simps

context notes [[function_internals]] begin
partial_function (spmf) test :: "bool \<Rightarrow> bool spmf" where
"test b = do {
              a \<leftarrow> bernoulli_exp_minus_rat 1;
              if a = False then return_spmf b
              else  test b
}"
end
thm test.fixp_induct
lemma test_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
and "P (\<lambda>test. return_pmf None)"
and "(\<And>b. P b \<Longrightarrow> P (\<lambda>ba. bernoulli_exp_minus_rat 1 \<bind> (\<lambda>a. if a = False then return_spmf ba else b ba)))"
shows "P test"
  using assms by (rule test.fixp_induct)

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
interpretation loop_spmf fst body 
  rewrites  "body \<equiv> (\<lambda>(b, t, s, z). 
                            fast_uniform (t::nat) \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract (int u) (int t))  \<bind>
                            (\<lambda>d. if \<not> d then return_spmf (True, t, s, 0)
                                 else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>real x / real s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then return_spmf (True, t, s, 0) else if b then return_spmf (False, t, s,- y) else return_spmf (False, t, s,y))))))"
  by(fact body_def)

lemma map_spmf_bind_spmf_lambda:
"map_spmf f \<circ> (\<lambda>y. bind_spmf (p y) (g y) ) = (\<lambda>y. (p y) \<bind> map_spmf f \<circ> (g y))"
  by (simp add: comp_def map_spmf_bind_spmf)

lemma 
  fixes t s ::nat 
  shows 
" 
    (\<lambda>y. bind_spmf (p y)
      (\<lambda>ya. bind_spmf  (g y) (map_spmf f \<circ> local.while)))
=
    (\<lambda>y. bind_spmf (p y)
      (\<lambda>ya. bind_spmf (g y) (map_spmf f \<circ> local.while)))
"
  sorry

  find_theorems "bind_spmf _ (map_spmf _) = _"

lemma discrete_laplace_rat_cov_while:
"discrete_laplace_rat t s = map_spmf (snd \<circ> snd \<circ> snd) (while (True, t, s, 0))" (is "?lhs = ?rhs")
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
      sorry
  qed
  show "ord_spmf (=) ?rhs ?lhs"
    sorry
qed

lemma lossless_discrete_laplace_rat:
"lossless_spmf (discrete_laplace_rat t s)"
  sorry

end


lemma spmf_discrete_laplace_rat[simp]:
  shows "spmf (discrete_laplace_rat t s) z = (exp(t/s)-1)/(exp(t/s)+1) * exp (- abs z * t/s)"
proof (rule spmf_ub_tight)
  show "\<And>x. spmf (discrete_laplace_rat t s) x \<le> (exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
  proof -
    fix x
    show "spmf (discrete_laplace_rat t s) x \<le> (exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s)"
    proof -
      have "ennreal (spmf (discrete_laplace_rat t s) x) \<le>ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))"
        apply(rewrite discrete_laplace_rat.simps)
        apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        apply(simp add: nn_integral_count_space_finite UNIV_bool)
      proof-
        have "ennreal (spmf (discrete_laplace_rat t s) x) = 
              ennreal (spmf (fast_uniform t \<bind>
                              (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                                (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                                     else loop 0 \<bind>
                                      (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                       in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))x)"
          by (simp add: discrete_laplace_rat.simps)
        also have "... =
                  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
                          (\<Sum>\<^sup>+ d. ennreal (spmf (bernoulli_exp_minus_rat (Fract (int u) (int t))) d) *
                                  ennreal (spmf (if \<not> d then discrete_laplace_rat t s
                                                 else loop 0 \<bind>
                                                    (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor> in
                                                     bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                else if b then return_spmf (- y) else return_spmf y)))x)))"
          by (simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        also have "... =  (\<Sum>\<^sup>+ u. ennreal (spmf (fast_uniform t) u) *
       (ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) False) * ennreal (spmf (discrete_laplace_rat t s) x) +
        ennreal (spmf (bernoulli_exp_minus_rat (Fract u t)) True) * ennreal (spmf (loop 0 \<bind>
                                                                                    (\<lambda>v. let y = \<lfloor>(real u + real t * real v) / real s\<rfloor>
                                                                                         in bernoulli_rat (Suc 0) 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s 
                                                                                                                             else if b then return_spmf (- y) 
                                                                                                                                  else return_spmf y)))
                                                                             x)
       )
      )"
          by(simp add: nn_integral_count_space_finite UNIV_bool)
        also have "... = "

      then show ?thesis by simp
    qed
  qed
  show "(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = ennreal (weight_spmf (discrete_laplace_rat t s))"
  proof - 
    have 1:"ennreal (weight_spmf (discrete_laplace_rat t s)) = 1"
      using lossless_discrete_laplace_rat lossless_spmf_def by auto
    have 2:"(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = 1" 
    
end