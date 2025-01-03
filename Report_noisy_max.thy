section \<open>Report Noisy Max with discrete laplace distribution\<close>

theory Report_noisy_max
  imports Discrete_laplace_rat
          Differential_Privacy2
          formalization.Differential_Privacy_Example_Report_Noisy_Max
          Discrete_laplace_mechanism
begin

primrec argmax_int_list :: "int list \<Rightarrow> (int \<times> nat)" where
"argmax_int_list [] = (0,0)"|
"argmax_int_list (x#xs) = (if xs = [] then (x,0) else (let (m,i) = argmax_int_list xs in (if x>m then (x,0) else (m,i+1))))"

primrec discrete_laplace_noise_add_list :: "(('a, int) query) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (int list) spmf" where
"discrete_laplace_noise_add_list [] epsilon1 epsilon2  ls = return_spmf []"|
"discrete_laplace_noise_add_list (c#cs) epsilon1 epsilon2 ls = 
do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list cs epsilon1 epsilon2 ls;
  noisy_c \<leftarrow> discrete_laplace_mechanism c 1 epsilon1 epsilon2 ls;
  return_spmf (noisy_c  # noisy_cs)
}"

definition report_noisy_max:: "(('a, int) query) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat spmf" where
"report_noisy_max cs epsilon1 epsilon2 x = do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list cs epsilon1 epsilon2 x;
  return_spmf (snd (argmax_int_list noisy_cs))
}
"

primrec is_count_queries :: "(('a, int) query) list \<Rightarrow> bool" where
"is_count_queries [] = True" |
"is_count_queries (c#cs) = (if is_sensitivity c 1 then is_count_queries cs else False)"

subsection \<open>component function\<close>
lemma argmax_int_list_index_lt_length:
  shows"0<length list \<Longrightarrow> snd (argmax_int_list list) <length list"
proof (induct list)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a list)
  then show ?case 
    unfolding argmax_int_list.simps Let_def snd_def
    by (simp add: prod.case_eq_if)
qed

lemma argmax_int_list_fst: 
shows "length list > 0 \<Longrightarrow>fst (argmax_int_list list)= Max (set list)"
proof(induct list)
  case Nil
  then show ?case
    by simp
next
  case (Cons a list)
  then show ?case
    unfolding argmax_int_list.simps fst_def
    apply (simp add: prod.case_eq_if)
    by (metis List.finite_set Max_ge_iff max.absorb_iff2 not_le_imp_less set_empty2)
qed

lemma argmax_int_list_snd:
  shows "length list > 0 \<Longrightarrow>nth list (snd (argmax_int_list list)) =  fst (argmax_int_list list)"
proof(induct list)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case 
    unfolding argmax_int_list.simps snd_def fst_def
    by(simp add: prod.case_eq_if)
qed

lemma argmax_int_list_snd':
  shows "length list > 0 \<Longrightarrow>nth list (snd (argmax_int_list list)) = Max(set list)"
  using argmax_int_list_fst argmax_int_list_snd by auto

lemma count_queries:
  shows "is_count_queries cs \<Longrightarrow> \<forall> c\<in> (set cs). is_sensitivity c 1"
proof (induct cs)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
  proof(clarify)
    fix c
    assume c:"c \<in> set (a # cs)"
    then show "is_sensitivity c 1"
      apply(cases "c \<in> set cs")
      using Cons is_count_queries.simps(2)[of "a" "cs"]
       apply(presburger)
      apply(cases "a\<in> set cs",simp)
      using Cons is_count_queries.simps(2)[of "a" "cs"]
      by(simp,argo)
  qed
qed


  
lemma lossless_discrete_laplace_noise_add_list:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
  shows "lossless_spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 ls)"
proof (induct cs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)
  then show ?case
    using lossless_discrete_laplace_mechanism[of"epsilon1" "epsilon2" "1"] assms
    by(auto)
qed

lemma lossless_report_noisy_max:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
  shows "lossless_spmf (report_noisy_max cs epsilon1 epsilon2 x)"
  unfolding report_noisy_max_def
  using lossless_discrete_laplace_noise_add_list assms
  by simp

lemma spmf_discrete_laplace_noise_add_list:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
shows "\<And>list. length cs = length list \<Longrightarrow> spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list = ((exp(epsilon1/epsilon2)-1)/(exp(epsilon1/epsilon2)+1))^(length cs) 
                                                                            * prod (\<lambda>((c,z),i). exp(-(epsilon1 * \<bar>z-c(x)\<bar>)/epsilon2)) (set (zip(zip cs list)[0..(length cs -1)]))"
proof(induct cs)
  case Nil
  then show ?case
  proof -
    have 1:"spmf (discrete_laplace_noise_add_list [] epsilon1 epsilon2 x) list = 1"
      unfolding discrete_laplace_noise_add_list.simps
      using Nil by simp
    have 2:" ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length [] * (\<Prod>a\<in>set (zip (map (\<lambda>h x. real_of_int (h x)) []) (map real_of_int list)). case a of (c, z) \<Rightarrow> exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) = 1"
      by simp
    show ?thesis
      using 1 2 by simp
  qed
next
  case (Cons a cs)
  then show ?case
  proof -
    have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) 
        = ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (drop 1 list)) *
          ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (nth list 0))"
      unfolding discrete_laplace_noise_add_list.simps
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
      apply(rewrite ennreal_indicator)
    proof-
      have "(\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa))))
          = (\<Sum>\<^sup>+ xa. (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) *  (ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa)))))"
        by(rewrite nn_integral_cmult,auto)
      also have "... = (\<Sum>\<^sup>+ xa. (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) *  ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {drop 1 list} xa * indicator {nth list 0} xb))"
      proof -
        have 1:"\<And>xa xb. (indicator {Some list} (Some (xb # xa))::ennreal) = indicator {drop 1 list} xa * indicator {nth list 0} xb "
        proof -
          fix xa xb
          have 1:"(list = (xb#xa)) = ((drop 1 list = xa) \<and> (nth list 0 = xb))"
            by (metis Cons_nth_drop_Suc Groups.add_ac(2) cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 drop0 gr0_conv_Suc less_numeral_extra(1) list.sel(3) list.size(4) local.Cons(2) nth_Cons_0 semiring_norm(163))
          show "(indicator {Some (list)} (Some (xb#xa))::ennreal) = indicator {drop 1 list} (xa) * indicator {nth list 0} (xb)"
            unfolding indicator_def
            using 1
            by(auto)
        qed
        have "\<And>xa xb. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa)))
                          = ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {drop 1 list} xa * indicator {list ! 0} xb"
          apply(rewrite 1)
          apply(rewrite HOL.no_atp(124),rewrite HOL.no_atp(124))
          by(auto)
        then show ?thesis by presburger
      qed
      also have "... = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (drop (Suc 0) list)) * ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (list ! 0)) * indicator {drop 1 list} xa) "
        by(rewrite nn_integral_cmult_indicator,auto)
      also have "... = ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (drop (Suc 0) list)) * ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (list ! 0))"
        by(rewrite nn_integral_cmult_indicator,auto)
      finally show "(\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa)))) =
                     ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (drop (Suc 0) list)) * ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (list ! 0)) "
        by simp
    qed
    also have "... = ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (drop 1 list) * (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (list ! 0)))"
      by(rewrite ennreal_mult',auto)
    also have "... = ennreal
     (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs *
      (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) *
      ((exp (real epsilon1 / (real epsilon2 * real (Suc 0))) - 1) * exp (- (real epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar> / (real epsilon2 * real (Suc 0)))) / (exp (real epsilon1 / (real epsilon2 * real (Suc 0))) + 1)))"
      apply(rewrite Cons(1))
      using Cons(2)
      apply(simp)
      apply(rewrite spmf_discrete_laplace_mechanism)
      using assms by(auto)
    also have "... = ennreal (((exp (epsilon1/epsilon2)-1)/(exp(epsilon1/epsilon2)+1))^length (a#cs) * (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * exp (-(epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar>/(epsilon2))))"
    proof -
      have "ennreal (((exp (epsilon1/epsilon2)-1)/(exp (epsilon1/epsilon2)+1))^length cs * (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))*
                    ((exp (epsilon1/epsilon2)-1) * exp (- (epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar>/epsilon2))/(exp (epsilon1 /epsilon2)+1)))
      = ennreal (((exp (epsilon1/epsilon2)-1)/(exp (epsilon1/epsilon2)+1))^length cs * ((exp (epsilon1/epsilon2)-1)/(exp (epsilon1 /epsilon2)+1)) * (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) *
                    exp (- (epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar>/epsilon2)))"
        by argo
      also have "... = ennreal (((exp (epsilon1/epsilon2)-1)/(exp(epsilon1/epsilon2)+1))^(length (a#cs)) * (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * exp (-(epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar>/(epsilon2))))"
      proof -
        have "((exp (epsilon1/epsilon2)-1)/(exp (epsilon1/epsilon2)+1))^length cs * ((exp (epsilon1/epsilon2)-1)/(exp (epsilon1 /epsilon2)+1)) = ((exp (epsilon1/epsilon2)-1)/(exp (epsilon1/epsilon2)+1))^(length (a#cs))"
          by auto
        then show ?thesis by presburger
      qed
      finally show ?thesis by simp
    qed
    also have "... = ennreal(((exp(epsilon1/epsilon2)-1)/(exp(epsilon1/epsilon2)+1))^length (a # cs) * (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int (list))) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)))" 
    proof -
      have " (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * exp (- (real epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar> / real epsilon2))
          = (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int (list))) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))"
      proof -
        have 1:"inj_on (\<lambda>((c, z), i). ((c, z), i + 1)) (set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]))"
          unfolding inj_on_def
          by auto
        have 2:"set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]) = (\<lambda>((c, z), i). ((c, z), i + 1)) ` set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)])"
          apply(rewrite set_zip,rewrite set_zip)
          apply(auto)
          apply(rewrite zip_map_map)
          by(rule,auto)
        have 3:"(\<And>xa. xa \<in> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]) \<Longrightarrow>
         (case case xa of (x, xa) \<Rightarrow> (case x of (c, z) \<Rightarrow> \<lambda>i. ((c, z), i + 1)) xa of (xa, xb) \<Rightarrow> (case xa of (c, z) \<Rightarrow> \<lambda>i. 
          exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) xb) = (case xa of (xa, xb) \<Rightarrow> (case xa of (c, z) \<Rightarrow> \<lambda>i. exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) xb))"
          by(auto)
        have "(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * exp (- (real epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar> / real epsilon2))
            =  (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * exp (- (real epsilon1 * \<bar>real_of_int (list ! 0) - real_of_int (a x)\<bar> / real epsilon2))"
          using comm_monoid_mult_class.prod.reindex_cong[of "(\<lambda>((c,z),i). ((c,z),i+1))" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [0..int (length cs - 1)])" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)])"
                                                            "(\<lambda>((c,z),i). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))" "(\<lambda>((c,z),i). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))"]
                1 2 3
          by presburger
        also have "... = (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) * prod (\<lambda> ((c,z),i). exp (- (real epsilon1 * \<bar>z - c x\<bar>)/epsilon2)) {((a,list ! 0),0)}"
          by(auto)         
        also have "(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>{((a, list ! 0), 0)}. exp (- (real epsilon1 * real_of_int \<bar>z - c x\<bar>) / real epsilon2)) = (\<Prod>((c,z),i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int (list))) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))"
        proof -
          have 1:"finite (set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]))"
            by auto
          have 2:"finite {((a, list ! 0), 0)}"
            by auto
          have 3:"(set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]))  \<inter>  {((a, list ! 0), 0)} = {}"
            by(rewrite set_zip,rewrite zip_map_map,rewrite zip_map_map,auto)
          have 4:" set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int list)) [0..int (length cs)]) 
                = (set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]))  \<union>  {((a, list ! 0), 0)}"
          proof - 
            have "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int list)) [0..int (length cs)])
                = set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a#cs)) (map real_of_int (nth list 0 # drop 1 list))) (0#[1..int (length cs)]))"
            proof -
              have 1:"list =  (nth list 0 # drop 1 list)"
                by (metis Cons_nth_drop_Suc One_nat_def drop0 length_greater_0_conv list.simps(3) local.Cons(2))
              have 2:"[0..int (length cs)] = (0#[1..int (length cs)])"
                by (simp add: upto_rec1)
              show ?thesis using 1 2 by auto
            qed
            also have "... = set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (cs)) (map real_of_int (drop 1 list))) ([1..int (length cs)])) \<union> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) ([a])) (map real_of_int ([list ! 0]))) ([0]))"
              by auto
            also have "... = (set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)]))  \<union>  {((a, list ! 0), 0)}"
              by(auto)
            finally show ?thesis by simp
          qed
          show ?thesis
            apply(rewrite 4)
            apply(rewrite comm_monoid_mult_class.prod.union_disjoint[of "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (drop 1 list))) [1..int (length cs)])" "{((a, list ! 0), 0)}"])
            using 1 2 3 by(auto)
        qed
        finally show ?thesis by simp
      qed
      then show ?thesis
        by (simp add: Groups.mult_ac(1))
    qed
    finally have p:" ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) 
                   = ennreal(((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length (a # cs) * (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a # cs)) (map real_of_int list)) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2)))"     
      by simp
    show ?thesis
    proof -
      have 1:"0 \<le> spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list"
        by simp
      have 2:"0 \<le> ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length (a # cs) *
      (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a # cs)) (map real_of_int list)) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))"
      proof-
        have 1:"0 \<le> ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length (a # cs)"
          by(auto)
        have 2:"0 \<le> (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (a # cs)) (map real_of_int list)) [0..int (length cs)]). exp (- (real epsilon1 * \<bar>z - c x\<bar>) / real epsilon2))"
          by(rewrite linordered_semidom_class.prod_nonneg,auto)
        show ?thesis using 1 2 by simp
      qed
      show ?thesis
        using p ennreal_inj 1 2
        by simp
    qed
  qed
qed

lemma spmf_discrete_laplace_noise_add_list_zero:
shows "\<And>list. length cs \<noteq> length list \<Longrightarrow> spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list = 0"
proof (induct cs)
  case Nil
  then show ?case 
    unfolding discrete_laplace_noise_add_list.simps by simp
next
  case (Cons a cs)
  then show ?case 
  proof(cases "list = []")
    case True
    then show ?thesis 
    proof -
      have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) = 0"
        unfolding discrete_laplace_noise_add_list.simps
        apply(rewrite ennreal_spmf_bind,rewrite nn_integral_measure_spmf,rewrite ennreal_spmf_bind,rewrite nn_integral_measure_spmf)
        using True by simp
      then show ?thesis by simp
    qed
  next
    case False
    then show ?thesis 
    proof -
      have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) 
          = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * (indicator {Some list} (Some (xb # xa))::ennreal)))"
        unfolding discrete_laplace_noise_add_list.simps
        apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
        by(simp add: ennreal_indicator)
      also have "... = (\<Sum>\<^sup>+ xa.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) *
        (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {tl list} xa * indicator {hd list} xb))"
      proof -
        have "\<And>xa xb. (indicator {Some list} (Some (xb # xa))::ennreal) = indicator {tl list} xa *indicator {hd list} xb"
        proof -
          fix xa::"int list" and xb::"int"
        have "(indicator {Some list} (Some (xb # xa))::ennreal) = (if list = xb#xa then 1::int else 0)"
          by simp
        also have "... = (if (hd list = xb \<and> tl list = xa) then 1 else 0)"
          using False by force
        also have "... = (if tl list = xa then 1 else 0) * (if hd list = xb then 1 else 0)"
          by simp
        also have "... = indicator {tl list} xa * indicator {hd list} xb"
          by simp
        finally show "(indicator {Some list} (Some (xb # xa))::ennreal) = indicator {tl list} xa * indicator {hd list} xb"
          by simp
      qed
      then have "\<And>xa xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * (indicator {Some list} (Some (xb # xa))::ennreal) 
                        = ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {tl list} xa * indicator {hd list} xb"
        by (simp add: ab_semigroup_mult_class.mult_ac(1))
      then show ?thesis by simp
    qed
    also have "... = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (hd list)) * indicator {tl list} xa))"
      by simp
    also have "... = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) *
                             ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (hd list)) * indicator {tl list} xa)"
      using no_atp(124) by meson
    also have "... = 0"
    proof -
      have "\<And>xa. xa\<in>{tl list} \<Longrightarrow> ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) = 0"
      proof -
        have "length cs \<noteq> length (tl list)"
          using Cons(2) False by auto
        then show "\<And>xa. xa\<in>{tl list} \<Longrightarrow> ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) = 0"
          using Cons(1)[of "tl list"] by simp
      qed
      then show ?thesis by simp
    qed
    finally have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) = 0"
      by simp
    then show ?thesis by simp  
  qed
qed
qed

lemma pure_dp_discrete_laplace_noise_add_list:
  fixes cs::"('a,int) query list"
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "countable (UNIV::'a list set)"
  shows "is_count_queries cs \<Longrightarrow> pure_dp (discrete_laplace_noise_add_list cs epsilon1 epsilon2) (length cs *(epsilon1/epsilon2))"
proof(induct cs)
  case Nil
  then show ?case
    unfolding discrete_laplace_noise_add_list.simps pure_dp_def differential_privacy_def DP_inequality_def 
    by(auto)
next
  case (Cons a cs)
  then show ?case
    unfolding discrete_laplace_noise_add_list.simps
  proof -
    assume a_cs:"is_count_queries (a # cs)"
    have cs:"is_count_queries cs"
      using a_cs unfolding is_count_queries.simps by argo
    have a:"is_sensitivity a 1"
      using a_cs unfolding is_count_queries.simps by argo
    have t1:"(\<lambda>x. discrete_laplace_noise_add_list cs epsilon1 epsilon2 x \<bind> (\<lambda>y. case (x, y) of (x, noisy_cs) \<Rightarrow> discrete_laplace_mechanism a 1 epsilon1 epsilon2 x \<bind> (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs))))
        = (\<lambda>b. discrete_laplace_noise_add_list cs epsilon1 epsilon2 b \<bind> (\<lambda>noisy_cs. discrete_laplace_mechanism a 1 epsilon1 epsilon2 b \<bind> (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs))))"
      by simp
    have t2:"real (length cs) * (real epsilon1 / real epsilon2) + real epsilon1 / real epsilon2
          = (length (a # cs)) * (real epsilon1 / real epsilon2)"
      by(auto,argo)
    have "pure_dp (\<lambda>x. discrete_laplace_noise_add_list cs epsilon1 epsilon2 x \<bind> (\<lambda>y. case (x, y) of (x, noisy_cs) \<Rightarrow> discrete_laplace_mechanism a 1 epsilon1 epsilon2 x \<bind> (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs)))) (real (length cs) * (real epsilon1 / real epsilon2) + real epsilon1 / real epsilon2)"
    proof(rule pure_dp_comp[of "discrete_laplace_noise_add_list cs epsilon1 epsilon2" "(real (length cs) * (real epsilon1 / real epsilon2))"
                        "(\<lambda>(x,noisy_cs). bind_spmf (discrete_laplace_mechanism a 1 epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs)))"
                        "epsilon1/epsilon2"])
      show "pure_dp (discrete_laplace_noise_add_list cs epsilon1 epsilon2) (real (length cs) * (real epsilon1 / real epsilon2))"
        using Cons cs by simp
      show "\<And>y. pure_dp (\<lambda>x. case (x, y) of (x, noisy_cs) \<Rightarrow> bind_spmf (discrete_laplace_mechanism a 1 epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs))) (real epsilon1 / real epsilon2)"
        apply(simp)
      proof-
        fix y
        show "pure_dp (\<lambda>x. bind_spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # y))) (real epsilon1 / real epsilon2)"
        using pure_dp_discrete_laplace_mechanism[of"a" "1" "epsilon1" "epsilon2"] assms 
              dp_postprocess_theorem[of "\<lambda>x. discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x" "epsilon1/epsilon2" "\<lambda>noisy_c. (noisy_c # y)"]
              a
        unfolding postprocess_def
        by simp
      qed
      show "\<And>x. lossless_spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x)"
        using lossless_discrete_laplace_noise_add_list assms by simp
      show "\<And>x y. lossless_spmf (case (x, y) of (x, noisy_cs) \<Rightarrow> bind_spmf (discrete_laplace_mechanism a 1 epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs)))"
        apply(simp)
        using lossless_discrete_laplace_mechanism assms by fastforce
      show "0 \<le> real (length cs) * (real epsilon1 / real epsilon2)"
        using assms by simp
      show "0 \<le> real epsilon1 / real epsilon2"
        using assms by simp
      show "countable (UNIV::int list set)"
        by simp
      show "countable (UNIV::'a list set)" 
        using assms(3) by simp
    qed
    then show "pure_dp (\<lambda>b. discrete_laplace_noise_add_list cs epsilon1 epsilon2 b \<bind> (\<lambda>noisy_cs. discrete_laplace_mechanism a 1 epsilon1 epsilon2 b \<bind> (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs)))) (real (length (a # cs)) * (real epsilon1 / real epsilon2))"
      using t1 t2 by auto
  qed
qed

lemma spmf_report_noisy_max_bottom:
  shows "spmf (report_noisy_max [] epsilon1 epsilon2 x) 0 = 1"
    and "0<z \<Longrightarrow> spmf (report_noisy_max [] epsilon1 epsilon2 x) z = 0"
  unfolding report_noisy_max_def
  by auto

lemma spmf_report_noisy_max_zero:
  assumes "0<z"
and "length cs \<le>z"
  shows "spmf (report_noisy_max cs epsilon1 epsilon2 x) z = 0"
proof (cases "cs = []")
  case True
  then show ?thesis
    using spmf_report_noisy_max_bottom assms by simp
next
  case False
  then show ?thesis
  proof -
    have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = 0"
      unfolding report_noisy_max_def
    proof(simp add:ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
      have "\<And>list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))) = 0"
      proof -
        fix list::"int list"
        show "ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))) = 0 "
        proof(cases "length list = length cs")
          case True
          then show ?thesis
          proof-
            have "indicator {Some z} (Some (snd (argmax_int_list list))) = 0"
              unfolding indicator_def
              using argmax_int_list_index_lt_length[of "list"] True False list.size(3) assms
              by simp
            then show ?thesis by auto
          qed
        next
          case False
          then show ?thesis 
            using spmf_discrete_laplace_noise_add_list_zero by force
        qed
      qed
      then show "(\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * indicator {Some z} (Some (snd (argmax_int_list xa)))) = 0"
        by(rewrite nn_integral_0_iff,auto)
    qed
    then show ?thesis by simp
  qed
qed

lemma ennreal_spmf_report_noisy_max_simps:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "z<length cs"
  shows "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) =
         (\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
proof -
  have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))))"  
    unfolding report_noisy_max_def
    by(simp add: ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
  also have "... =  (\<Sum>\<^sup>+ list\<in>{list. length list = length cs}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))))"
    apply(rule nn_integral_count_space_eq,auto)
    using assms spmf_discrete_laplace_noise_add_list_zero 
    by metis
  also have "... =  (\<Sum>\<^sup>+ ((a, c), b)\<in>{((a,c),b). a = take z (a@b#c) \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> length (a@b#c) = length cs}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) *  indicator {Some z} (Some (snd (argmax_int_list (a @ b # c)))))"
    using nn_integral_bij_count_space[of "\<lambda>((a,c),b). a@b#c" "{((a,c),b). a = take z (a@b#c) \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> length (a@b#c) = length cs}" "{list. length list = length cs}"]
    unfolding case_prod_beta' 
    apply(rule)
    unfolding bij_betw_def image_def inj_on_def
  proof(rule+,force,force,force,rule,clarify,rule+)
    fix x::"int list"
    assume x:"x \<in> {list. length list = length cs}" 
    show "x = fst (fst (((take z x, drop (Suc z) x),nth x z))) @ snd (((take z x, drop (Suc z) x),nth x z)) # snd (fst (((take z x, drop (Suc z) x),nth x z)))"
      using x assms id_take_nth_drop[of "z" "x"]
      by simp
    show "((take z x, drop (Suc z) x),nth x z)\<in> {list.
             fst (fst list) = take z (fst (fst list) @ snd list # snd (fst list)) \<and>
             snd list = (fst (fst list) @ snd list # snd (fst list)) ! z \<and>
             snd (fst list) = drop (Suc z) (fst (fst list) @ snd list # snd (fst list)) \<and> length (fst (fst list) @ snd list # snd (fst list)) = length cs}"
      using x assms id_take_nth_drop[of "z" "x"]
      by(auto)
  qed
  also have "... = (\<Sum>\<^sup>+ ((a, c), b).
        ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {Some z} (Some (snd (argmax_int_list (a @ b # c)))) * indicator {((a,c),b). a = take z (a@b#c) \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> length (a@b#c) = length cs} ((a,c),b))"
    using nn_integral_count_space_indicator[of "{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a@b#c) = length cs}"
                                             "\<lambda>((a,c),b). ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {Some z} (Some (snd (argmax_int_list (a @ b # c))))"]
    unfolding case_prod_beta
    by simp
  also have "...
        = (\<Sum>\<^sup>+ (a,c). (\<Sum>\<^sup>+ b.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {Some z} (Some (snd (argmax_int_list (a @ b # c))))
                               *  (indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a@b#c) = length cs} ((a, c), b)::ennreal)))"
    using nn_integral_fst_count_space[of "\<lambda>((a,c),b).  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {Some z} (Some (snd (argmax_int_list (a @ b # c))))
                               *  indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a@b#c) = length cs} ((a, c), b)"]
    unfolding case_prod_beta
    by(auto)
  also have "... = (\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
  proof -   
    have "(\<Sum>\<^sup>+ (a,c). (\<Sum>\<^sup>+ b.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {Some z} (Some (snd (argmax_int_list (a @ b # c))))
                               *  indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a@b#c) = length cs} ((a, c), b)))
        = (\<Sum>\<^sup>+ (a,c). (\<Sum>\<^sup>+ b.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) *indicator {(a,c). length a = z \<and> length c = length cs - (z+1)} (a,c) * indicator {b. z = snd (argmax_int_list (a@b#c))} b))"
    proof(rule nn_integral_cong,clarify,rule nn_integral_cong)
      fix a c ::"int list" and b::int
      have p:"indicator {Some z} (Some (snd (argmax_int_list (a @ b # c)))) * (indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)::ennreal) 
          = (indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)::ennreal) * (indicator {b. z = snd (argmax_int_list (a @ b # c))} b::ennreal)"
      proof -
        have "(indicator {Some z} (Some (snd (argmax_int_list (a @ b # c)))) * indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)::ennreal)
            = indicator {z} (snd (argmax_int_list (a @ b # c))) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)"
        proof -
          have 1:"indicator {Some z} (Some (snd (argmax_int_list (a @ b # c)))) = indicator {z} (snd (argmax_int_list (a @ b # c)))"
            unfolding indicator_def by simp
          have 2:"{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} = {((a, c), b). length a = z \<and> length c = length cs -(z+1)}"
            apply(rule+,clarify)   
            using assms length_take[of "z"]
              apply (metis min.absorb4)
             apply(clarify)
            using assms length_drop[of "Suc z"]
             apply (metis Suc_eq_plus1)
            apply(rule+,clarify,simp,clarify,simp)
            using assms(4) by linarith
          have 3:"indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)
                   = indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)"
            apply(rewrite 2)
            unfolding indicator_def by(auto)
          show ?thesis 
            by(rewrite 1, rewrite 3,simp)
        qed
        also have "... =indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c) * indicator {b. z = snd (argmax_int_list (a @ b # c))} b"
          unfolding indicator_def
          by auto
        finally show ?thesis by simp
      qed
      show "ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * (indicator {Some z} (Some (snd (argmax_int_list (a @ b # c))))::ennreal) *
       (indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)::ennreal) =
       ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * (indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)::ennreal) * (indicator {b. z = snd (argmax_int_list (a @ b # c))} b::ennreal)"
        apply(rewrite semigroup_mult_class.mult.assoc)
        by(rewrite p, rewrite semigroup_mult_class.mult.assoc,auto)
    qed
    also have "... =  (\<Sum>\<^sup>+ (a, c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c))  * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)))"
    proof(rule nn_integral_cong,clarify)
      fix a c::"int list"
      show "\<integral>\<^sup>+ba\<in>{ba. z = snd (argmax_int_list (a @ ba # c))}. (ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ ba # c)) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c))\<partial>count_space UNIV =
           (\<Sum>\<^sup>+ ba\<in>{ba. z = snd (argmax_int_list (a @ ba # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ ba # c)) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)) "
        by(rewrite nn_integral_count_space_indicator[of "{ba. z = snd (argmax_int_list (a @ ba # c))}"],auto)
    qed
    also have "... = (\<Sum>\<^sup>+ (a, c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c))) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c))"
      by(rewrite ab_semigroup_mult_class.mult.commute, rewrite nn_integral_cmult,simp,rewrite ab_semigroup_mult_class.mult.commute,simp)
    also have "... = (\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
      using nn_integral_count_space_indicator[of "{(a,c). length a = z \<and> length c = length cs - (z+1)}" "\<lambda>(a,c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"]
      unfolding case_prod_beta
      by simp
    finally show ?thesis
      by simp
  qed
  finally show ?thesis by simp
qed

lemma test:
  shows "\<And>rs1 rs2. length rs1 = length cs \<Longrightarrow> length rs2 = length cs \<Longrightarrow> ((map2 (\<lambda>r::int. (\<lambda>c. r+c))) rs1 cs = (map2 (\<lambda>r::int. (\<lambda>c. r+c)))  rs2 cs) = (rs1 = rs2)"
proof (induct cs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)
  then show ?case
    unfolding zip_Cons
  proof(auto)
    assume H:"map (\<lambda>(x, y). x + y) (case rs1 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) = map (\<lambda>(x, y). x + y) (case rs2 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) "
    have 1:"rs1 \<noteq> []"
      using Cons by auto
    have 2:"rs2 \<noteq> []"
      using Cons by auto
    have 3:"map (\<lambda>(x, y). x + y) (case rs1 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) = (hd rs1 + a)#(map (\<lambda>(x, y). x + y) (zip (tl rs1) cs))"
      using 1 list.case_eq_if list.map
      by (simp add: list.case_eq_if)
    have 4:"map (\<lambda>(x, y). x + y) (case rs2 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) = (hd rs2 + a)#(map (\<lambda>(x, y). x + y) (zip (tl rs2) cs))"
      using 2 list.case_eq_if list.map
      by (simp add: list.case_eq_if)
    have "(hd rs1 + a)#(map (\<lambda>(x, y). x + y) (zip (tl rs1) cs)) =  (hd rs2 + a)#(map (\<lambda>(x, y). x + y) (zip (tl rs2) cs))"
      using H 3 4 by simp
    then have "hd rs1 = hd rs2 \<and> tl rs1 = tl rs2"
      using Cons by auto
    then show "rs1 = rs2" 
      using "1" "2" list.expand by blast
  qed
qed

lemma test2:
  fixes list2::"int list"
  shows"\<And>list. length list = length list2 \<Longrightarrow> list = map (\<lambda>p. fst p + snd p) (zip (map2 (\<lambda>a c. a-c) list list2) list2)"
proof(induct list2)
  case Nil
  then show ?case by simp
next
  case (Cons a list2)
  then show ?case 
  proof -
    have 1:"list = hd list # tl list"
    proof-
      have "list \<noteq> []" using Cons by auto
      then show ?thesis by simp
    qed
    show ?thesis
      apply(rewrite 1)
      unfolding zip.simps 
    proof -
      have 1:"(case list of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2)
          = (hd list, a) # zip (tl list) list2"
        using list.cases(2)[of _ _ "hd list" "tl list"] 1 by auto
      have 2:"map (\<lambda>(x, y). x - y) (case list of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2)
            = (hd list - a)# (map (\<lambda>(x, y). x - y) (zip (tl list) list2))"
        apply(rewrite 1)
        using list.map(2) by simp
      have 3:"(case map (\<lambda>(x, y). x - y) (case list of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2) of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2)
          = (hd list-a, a) # zip ((map (\<lambda>(x, y). x - y) (zip (tl list) list2))) list2"
        apply(rewrite 2)
        using list.case(2)[of _ _ "hd list- a"] by simp
      have 4:"map (\<lambda>p. fst p + snd p) (case map (\<lambda>(x, y). x - y) (case list of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2) of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2)
          = (hd list) #  map (\<lambda>p. fst p + snd p) (zip ((map (\<lambda>(x, y). x - y) (zip (tl list) list2))) list2)"
        apply(rewrite 3)
        using list.map(2)[of "(\<lambda>p. fst p + snd p)" "(hd list-a,a)" "zip (map2 (-) (tl list) list2) list2"] unfolding case_prod_beta
        by(auto)
      show "hd list # tl list = map (\<lambda>p. fst p + snd p) (case map (\<lambda>(x, y). x - y) (case list of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2) of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs list2)"
        apply(rewrite 4)
        using Cons(1)[of "tl list"] Cons(2) by simp
    qed
  qed
qed

lemma ennreal_spmf_report_noisy_max_simps2:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "z<length cs"
  shows "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) =
         (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
       \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
proof -
  have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) 
    = (\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
    using ennreal_spmf_report_noisy_max_simps assms by simp
  also have "... = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra,rc). length ra = z \<and> length rc = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs)))@b#(map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs)))))}.
                                                                                             ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs))) @ b # (map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs))))))"
    using nn_integral_bij_count_space[of "\<lambda>(ra,rc). ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs))), (map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs))))"
                                         "{(ra,rc). length ra = z \<and> length rc = length cs - (z+1)}" "{(a,c). length a = z \<and> length c = length cs - (z+1)}"
                                         "\<lambda>(a,c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"]  
    unfolding case_prod_beta fst_conv snd_conv
    apply(rule)
    unfolding bij_betw_def inj_on_def image_def
  proof(rule+,auto)
    fix a b aa ba::"int list"
    assume H1:"map (\<lambda>p. fst p + snd p) (zip a (take (length a) (map (\<lambda>q. q x) cs))) = map (\<lambda>p. fst p + snd p) (zip aa (take (length a) (map (\<lambda>q. q x) cs))) "    
      and H2:"length aa = length a"
      and H3:"z = length a"
      and H4:"map (\<lambda>p. fst p + snd p) (zip b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))) = map (\<lambda>p. fst p + snd p) (zip ba (drop (Suc (length a)) (map (\<lambda>q. q x) cs)))"
      and H5:"length b = length cs - Suc (length a)" and H6:" length ba = length cs - Suc (length a)"
    have 1:"length a = length (take (length a) (map (\<lambda>q. q x) cs))"
      using H3 assms by simp
    have 2:"length aa = length (take (length a) (map (\<lambda>q. q x) cs))"
      using H2 H3 assms by simp
    have 3:"map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) = map2 (+) aa (take (length a) (map (\<lambda>q. q x) cs))"
      using H1 unfolding case_prod_beta by simp
    show "a = aa"
      using test[of "a" "(take (length a) (map (\<lambda>q. q x) cs))" "aa"] 1 2 3
      by simp
    have 4:"length b = length (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
      using H5 H3 assms by simp
    have 5:"length ba = length (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
      using H6 H3 assms by simp
    have 6:"map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs)) = map2 (+) ba (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
      using H4 unfolding case_prod_beta by simp
    show "b=ba"
      using test[of "b" "(drop (Suc (length a)) (map (\<lambda>q. q x) cs))" "ba"] 4 5 6
      by simp
  next
    fix aa ba::"int list"
    assume "z = length aa" and "length ba = length cs - Suc (length aa)"
    then show "min (length cs) (length aa) = length aa"
      using assms by simp
  next
    fix a b::"int list"
    assume H1:"length b = length cs - Suc (length a)" and H2:"z = length a"
    have 1:"length (map2 (\<lambda>a c. a-c) a (take (length a) (map (\<lambda>q. q x) cs))) = length a"
      using assms H2 by(auto)
    have 2:"length (map2 (\<lambda>a c. a-c) b (drop (Suc(length a)) (map (\<lambda>q. q x) cs))) = length cs - Suc (length a)"
      using assms H1 by auto
    have 3:"a = map (\<lambda>p. fst p + snd p) (zip (map2 (\<lambda>a c. a-c) a (take (length a) (map (\<lambda>q. q x) cs))) (take (length a) (map (\<lambda>q. q x) cs)))"
      using test2 H2 1 by simp
    have 4:"b = map (\<lambda>p. fst p + snd p) (zip (map2 (\<lambda>a c. a-c) b (drop (Suc(length a)) (map (\<lambda>q. q x) cs))) (drop (Suc (length a)) (map (\<lambda>q. q x) cs)))"
      using test2 H1 2 by simp
    show "\<exists>aa. length aa = length a \<and> (\<exists>ba. length ba = length cs - Suc (length a) \<and> a = map (\<lambda>p. fst p + snd p) (zip aa (take (length a) (map (\<lambda>q. q x) cs))) \<and> b = map (\<lambda>p. fst p + snd p) (zip ba (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))"  
      using 1 2 3 4 by blast
  qed
  also have "... = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
         \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
  proof(rule nn_integral_cong,auto)
    fix a b::"int list"
    assume "z = length a" and "length b = length cs - Suc(length a)"
    show "(\<Sum>\<^sup>+ ba\<in>{ba. length a = snd (argmax_int_list (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ ba # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ ba # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))) =
           (\<Sum>\<^sup>+ rb\<in>{rb. length a = snd (argmax_int_list (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length a) x) # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length a) x) # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs)))))"
      using nn_integral_bij_count_space[of "\<lambda>rb. rb+(cs!length a) x" "{rb. length a = snd (argmax_int_list (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length a) x) # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))}"
                                             "{ba. length a = snd (argmax_int_list (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ ba # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))}"
                                             "\<lambda>ba. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) @ ba # map2 (+) b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))"]
      unfolding case_prod_beta fst_conv snd_conv
      apply(rule)
      unfolding bij_betw_def inj_on_def image_def
    proof(auto,rule)
      fix xa::int
      assume "length a = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip a (take (length a) (map (\<lambda>q. q x) cs))) @ xa # map (\<lambda>p. fst p + snd p) (zip b (drop (Suc (length a)) (map (\<lambda>q. q x) cs)))))"
      then show "length a = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip a (take (length a) (map (\<lambda>q. q x) cs))) @ ((xa-(cs ! length a) x) + (cs ! length a) x) # map (\<lambda>p. fst p + snd p) (zip b (drop (Suc (length a)) (map (\<lambda>q. q x) cs))))) \<and> xa = (xa-(cs ! length a) x) + (cs ! length a) x "
        by auto
    qed
  qed
  finally show ?thesis
    by simp
qed

lemma fix_noise:
  assumes "1\<le>epsilon1"
    and "1\<le>epsilon2"
    and "length cs = length ra + length rc +1"
  shows "spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))
        = (\<Prod>(r,i)\<in>set (zip (map real_of_int ra) [0.. int(length ra)-1]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))
          * exp (- (real epsilon1 * \<bar>rb\<bar>) / real epsilon2) 
          * (\<Prod>(r,i)\<in>set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
proof-
  have "spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))
      = ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs *
    (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)]).
       exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))"
  apply(rewrite spmf_discrete_laplace_noise_add_list)
    using assms by simp_all  
  have "(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
      = (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
        (\<Prod>((c, z), i)\<in>{((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}. exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
        (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))"
  proof -
    have 1:"set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)])
           = set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y)  cs))))) [0..int(length ra -1)])
           \<union> {(((\<lambda>x::'a list. real_of_int ((cs ! length ra)x)), real_of_int(rb + (cs ! length ra) y)), int (length ra))}
           \<union> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra))cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y)  cs))))) [(length ra +1)..int(length cs -1)])"
    proof -
      have 1:"zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)]
      = zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y)  cs))))) [0..int(length ra -1)] @
        (((\<lambda>x::'a list. real_of_int ((cs ! length ra)x)), real_of_int(rb + (cs ! length ra) y)), int (length ra)) #
       zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra))cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y)  cs))))) [(length ra +1)..int(length cs -1)]"
        sorry
      then show ?thesis by simp
    qed
    have 2:"(set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<union>
             {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}) \<inter>
            set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]) = {}"
    proof(rule,clarify)
      fix a b ba
      assume H:"((a, b), ba)
       \<in> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<union>
          {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}"
      have 1:"ba \<in> set  [0..int (length ra - 1)]\<union> {int (length ra)}"
        using H set_zip_rightD by fast
      have "((a, b), ba) \<notin> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)])"
        using 1 set_zip_rightD[of "(a,b)" "ba" _ "[int (length ra + 1)..int (length cs - 1)]"]
        by fastforce
      then show "((a, b), ba) \<in> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]) \<Longrightarrow> ((a, b), ba) \<in> {}"
        by simp
    next
      show "{} \<subseteq> (set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<union>
           {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}) \<inter>
          set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)])"
        by simp
    qed
    have 3:"set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<inter>
    {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))} = {}"
    proof(rule,clarify)
      fix a b ba
      have " ((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))
         \<notin> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)])"
        sorry
      then show "((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))
         \<in> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<Longrightarrow>
        ((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra)) \<in> {}" by simp
    next
      show "{} \<subseteq> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<inter>
            {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}" by simp
     qed
     show ?thesis
       apply(rewrite 1)
       apply(rewrite comm_monoid_mult_class.prod.union_disjoint,simp,simp)
       using 2 apply(simp)
       apply(rewrite comm_monoid_mult_class.prod.union_disjoint,simp,simp)
       using 3 by auto
   qed
   have " (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (epsilon1 * \<bar>z - c y\<bar>) / epsilon2))
       = (\<Prod>(r,i)\<in>set (zip (map real_of_int ra) [0.. int(length ra)-1]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
    using comm_monoid_mult_class.prod.reindex_bij_betw[of "\<lambda>((c,z),i). (z - c y,i)" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)])"
                                                         "set (zip ra [0.. int(length ra)-1])" "\<lambda>(r,i). exp (- (epsilon1 * \<bar>r\<bar>) / epsilon2)"]
    unfolding case_prod_beta fst_conv snd_conv
  proof(rule)
    show "bij_betw (\<lambda>p. (snd (fst p) - fst (fst p) y, snd p)) (set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]))
     (set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1])))"
      sorry
    show "(\<Prod>p\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2)) = (\<Prod>p\<in>set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1])). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2))"
    proof-
      have "set (zip (map real_of_int ra) [0..int (length ra) - 1]) = set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
        sorry
      then show ?thesis by auto
    qed
  qed
  have "(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
      = (\<Prod>(r,i)\<in>set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
    using comm_monoid_mult_class.prod.reindex_bij_betw[of "\<lambda>((c,z),i). (z - c y,i)" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)])"
                                                          "set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)])" "\<lambda>(r,i). exp (- (epsilon1 * \<bar>r\<bar>) / epsilon2)"]
    unfolding case_prod_beta fst_conv snd_conv
  proof(rule)
    show "bij_betw (\<lambda>p. (snd (fst p) - fst (fst p) y, snd p))
     (set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]))
     (set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]))"
      sorry
    show "(\<Prod>p\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2)) =
    (\<Prod>p\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2))"
      by simp
  qed
  have "(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>{((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}. exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]).
       exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
        = (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>{((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}. exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]).
       exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))"
    sorry
  show ?thesis sorry
qed


lemma pointwise_pure_dp_inequality_report_noisy_max:
  assumes "is_count_queries cs"
and "(x,y)\<in>adj"
and "n = length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
shows "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z\<le> exp(epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
proof (cases "length cs =0")
  case True
  show "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
  proof -
    fix z::nat
    have 1:"cs = []"
      using True by simp
    have 2:"spmf (report_noisy_max [] epsilon1 epsilon2 x) 0 \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max [] epsilon1 epsilon2 y) 0"
      unfolding report_noisy_max_def
      by(simp)
    have 3:"0<z \<Longrightarrow> spmf (report_noisy_max [] epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max [] epsilon1 epsilon2 y) z"
      unfolding report_noisy_max_def
      by(simp)
    show "spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
      using 1 2 3 by auto
  qed
next
  case False
  assume cs:"length cs \<noteq> 0"
  show "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
  proof-
    fix z
    show "spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
    proof(cases "z<length cs")
      case True
      then show ?thesis 
      proof -
        thm ennreal_spmf_report_noisy_max_simps2[of "cs" "epsilon1" "epsilon2" "z" "y"]
        have x:"ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) 
              = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
                  \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
                    ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
          using assms ennreal_spmf_report_noisy_max_simps2[of "cs" "epsilon1" "epsilon2"  "z" "x"] True
          by linarith
        have y:"ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 y) z)
            =  (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
   \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
     ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
          using assms ennreal_spmf_report_noisy_max_simps2[of "cs" "epsilon1" "epsilon2"  "z" "y"] True
          by linarith
        have exp_y:"ennreal (exp (epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z) 
                = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
                    \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
                 exp (epsilon1/epsilon2) *  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
        proof-
          have "ennreal (exp (epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z) = ennreal (exp (epsilon1/epsilon2)) *  (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
   \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
     ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
            by(rewrite ennreal_mult',simp, rewrite y, simp)
          also have "... =(\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}. ennreal (exp(epsilon1/epsilon2)) *
       (\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))))"
            using nn_integral_cmult[of "\<lambda>(ra, rc).  (\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
                                    "count_space {(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}"
                                       "ennreal (exp(epsilon1/epsilon2))"] 
            unfolding case_prod_beta
            by(auto)
          also have "... =(\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
                    \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
                 exp (epsilon1/epsilon2) *  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"            
            by(rewrite nn_integral_cmult,auto)
          finally show ?thesis by simp
        qed
        have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) \<le> ennreal (exp (epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z)"
          apply(rewrite x, rewrite exp_y)
        proof(rule nn_integral_mono,auto)
          fix ra rc::"int list"
          assume H1:"z = length ra"
            and H2:"length rc = length cs - Suc(length ra)"
          show "(\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))))
           \<le> (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}.
                 ennreal (exp (real epsilon1 / real epsilon2)) *
                 ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))"
          proof -
            have 1:"(\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))))
              = ennreal ((\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              apply(rewrite fix_noise)
              using assms apply(simp,simp)
              using H2 
              using H1 True apply linarith
              apply(rewrite ab_semigroup_mult_class.mult.commute[of _ "(\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))"])
              apply(rewrite comm_semiring_1_class.semiring_normalization_rules(18))
              apply(rewrite ennreal_mult'',simp)
              apply(rewrite nn_integral_cmult,simp)
              apply(rewrite ab_semigroup_mult_class.mult.commute[of "(\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))"])
              by simp
            have 2:"(\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}.
                 ennreal (exp (real epsilon1 / real epsilon2)) *
                 ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))
                = ennreal ((\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. 
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              apply(rewrite fix_noise)
              using assms apply(simp,simp)
              using H1 H2 True apply linarith
              apply(rewrite ab_semigroup_mult_class.mult.commute[of _ "(\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))"])
              apply(rewrite ab_semigroup_mult_class.mult.commute[of "ennreal (exp (real epsilon1 / real epsilon2))" ])
              apply(rewrite comm_semiring_1_class.semiring_normalization_rules(18))
              apply(rewrite ennreal_mult'',simp)
              apply(rewrite ennreal_mult'[of "exp (real epsilon1 / real epsilon2)"],simp)
              apply(rewrite semigroup_mult_class.mult.assoc)
              apply(rewrite nn_integral_cmult,simp)
              apply(rewrite ab_semigroup_mult_class.mult.commute[of _ "(\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))"])
              apply(rewrite ab_semigroup_mult_class.mult.commute[of _ "ennreal (exp (real epsilon1 / real epsilon2))"])  
              by simp
            have 3:"(\<Sum>\<^sup>+ x\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))
                \<le> (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. 
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              sorry
            have 4:"ennreal ((\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))
              \<le> ennreal ((\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. 
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              using 3 ordered_semiring_class.mult_left_mono[of _ _ "ennreal ((\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))"]
              by simp
            show ?thesis using 1 2 4 by simp
          qed
        qed
        then show ?thesis by simp
      qed
    next
      case False
      then show ?thesis
        using spmf_report_noisy_max_zero[of "z" "cs"] cs by simp
    qed
  qed
qed      
        


lemma pure_dp_report_noisy_max:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "is_count_queries cs"
  shows "pure_dp (report_noisy_max cs epsilon1 epsilon2) (epsilon1/epsilon2)"
  using pointwise_pure_dp_inequality_report_noisy_max[of "cs" _ _ _ "epsilon1" "epsilon2"]
        pointwise_spmf_bound_imp_pure_dp_nat[of "(\<lambda>l. report_noisy_max cs epsilon1 epsilon2 l)" "epsilon1/epsilon2"] 
        assms
  by simp
  
  
  





end
