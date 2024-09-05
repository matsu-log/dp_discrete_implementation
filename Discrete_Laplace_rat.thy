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
      by auto
    also have "... = ennreal ((exp(-1))^(m) * (1-exp(-1)))"
      using P by blast
    finally show ?thesis by simp
  qed
  then show ?thesis by simp
qed

thm discrete_laplace_rat.simps


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

lemma lossless_discrete_laplace_rat:
"lossless_spmf (discrete_laplace_rat t s)"
  sorry
end

(*declare[[s
  qedhow_types,show_sorts]]*)



lemma spmf_discrete_laplace_rat[simp]:
  assumes "1\<le>s" and "1\<le>t"
  shows "spmf (discrete_laplace_rat t s) z = (exp(t/s)-1)/(exp(t/s)+1) * exp (- abs z * t/s)"
proof -
  have "ennreal (spmf (discrete_laplace_rat t s) z) \<le>ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int z\<bar> * t/s))"  
    apply(rewrite discrete_laplace_rat.simps)
    apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
    apply(simp add: nn_integral_count_space_finite UNIV_bool)    
    apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
  proof-
    have "ennreal (spmf (discrete_laplace_rat t s) z) = 
          ennreal (spmf (fast_uniform t \<bind>
                        (\<lambda>u. bernoulli_exp_minus_rat (Fract u t) \<bind>
                         (\<lambda>d. if \<not> d then discrete_laplace_rat t s
                              else loop 0 \<bind>
                                (\<lambda>v. let x = u + t * v; y = \<lfloor>x/s\<rfloor>
                                 in bernoulli_rat 1 2 \<bind> (\<lambda>b. if \<not> b \<and> y = 0 then discrete_laplace_rat t s else if b then return_spmf (- y) else return_spmf y)))))z)"
          by (simp add: discrete_laplace_rat.simps)
        also have "... =
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
      finally have "ennreal (spmf (discrete_laplace_rat t s) z) =
                   (\<Sum>u = 0..t - 1. ennreal (1/t)*
                   (ennreal (1 - exp (- real_of_rat (Fract u t))) * ennreal (spmf (discrete_laplace_rat t s) z) +
                    ennreal (exp (- real_of_rat (Fract u t))) *
                            (\<Sum>\<^sup>+ v. ennreal (exp (- 1) ^ v * (1 - exp (- 1))) *
                                   (let y = \<lfloor>(u+t*real v)/s\<rfloor>
                                    in ennreal (1 / real 2) * ennreal (if y = 0 then spmf (discrete_laplace_rat t s) z else if y = z then 1 else 0) 
                                     + ennreal (1 / real 2) * ennreal (if - y = z then 1 else 0))))) "
        by simp


      then show ?thesis by simp
    qed
  qed
  show "(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = ennreal (weight_spmf (discrete_laplace_rat t s))"
  proof - 
    have 1:"ennreal (weight_spmf (discrete_laplace_rat t s)) = 1"
      using lossless_discrete_laplace_rat lossless_spmf_def by auto
    have 2:"(\<Sum>\<^sup>+ x. ennreal ((exp (t/s) - 1) / (exp (t/s) + 1) * exp (- \<bar>real_of_int x\<bar> * t/s))) = 1" 
    
end