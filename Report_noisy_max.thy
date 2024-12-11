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
lemma argmax_int_list_index_le_length:
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
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
shows "\<And>list. length cs \<noteq> length list \<Longrightarrow> spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list = 0"
proof (induct cs)
  case Nil
  then show ?case 
    unfolding discrete_laplace_noise_add_list.simps by simp
next
  case (Cons a cs)
  then show ?case 
  proof -
    have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa))))"
      unfolding discrete_laplace_noise_add_list.simps
      apply(simp add: ennreal_spmf_bind nn_integral_measure_spmf)
      by(simp add: ennreal_indicator)
    show ?thesis 
      sorry
  qed
qed


lemma pure_dp_discrete_laplace_noise_add_list:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
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
      show "measure_spmf \<circ> (\<lambda>(x, noisy_cs). bind_spmf (discrete_laplace_mechanism a 1 epsilon1 epsilon2 x)  (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs))) \<in> count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
        unfolding o_def
        apply(rewrite case_prod_beta,rewrite measure_spmf_bind)
        unfolding o_def
        apply(auto)
        sorry
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

lemma ennreal_spmf_report_noisy_max_simps:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
  shows "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa))"
proof -
  have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * indicator {Some z} (Some (snd (argmax_int_list xa))))"  
    unfolding report_noisy_max_def
    by(simp add: ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
  also have "... = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (if z = snd (argmax_int_list xa) then 1 else 0))"
  proof -  
    have "\<And>xa. indicator {Some z} (Some (snd (argmax_int_list xa))) = (if z = snd (argmax_int_list xa) then 1 else 0)"  
      by auto
    then have "\<And>xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * indicator {Some z} (Some (snd (argmax_int_list xa))) =  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (if z = snd (argmax_int_list xa) then 1 else 0)"
      by simp
    then show ?thesis by simp  
  qed
  also have "... = nn_integral (count_space {list. length list = length cs}) (\<lambda>xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (if z = snd (argmax_int_list xa) then 1 else 0))"  
    apply(rewrite nn_integral_count_space_eq[of "UNIV" " {list. length list = length cs}"],auto)
    using spmf_discrete_laplace_noise_add_list_zero assms
    by metis
  also have "... = nn_integral (count_space {list. length list = length cs \<and> z = snd (argmax_int_list list)}) (\<lambda>xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (if z = snd (argmax_int_list xa) then 1 else 0))"
    by(rewrite nn_integral_count_space_eq[of "{list. length list = length cs}" "{list. length list = length cs \<and> z = snd (argmax_int_list list)}"],auto)
  also have "... = nn_integral (count_space {list. length list = length cs \<and> z = snd (argmax_int_list list)}) (\<lambda>xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa))"
    by(rewrite nn_integral_cong,auto)
  finally show ?thesis by simp  
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
  show "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z \<le> exp (real epsilon1 / real epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z "
  proof-
    fix z
    have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa))"
      using ennreal_spmf_report_noisy_max_simps assms False by auto
    have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 y) z) = (\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) xa))"
      using ennreal_spmf_report_noisy_max_simps assms False by auto
    have "exp(epsilon1/epsilon2) * (\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) xa))
        = (\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. exp(epsilon1/epsilon2) * ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) xa))"
      by(rewrite nn_integral_cmult,auto)
    have "(\<Sum>\<^sup>+ xa\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa))
        = (\<Sum>\<^sup>+ xa\<in>{(a, b, c). a = take z (a @ b # c) \<and> length (a @ b # c) = length cs \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c)\<and> z= snd (argmax_int_list (a@b#c))}.
            ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (case xa of (a, b, c) \<Rightarrow> a @ b # c)))"
      apply(rewrite nn_integral_bij_count_space[of "\<lambda>(a,b,c). (a@b#c)"                                       
                                         "{(a, b, c). a = take z (a@b#c) \<and> length(a@b#c)  = length cs \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> z= snd (argmax_int_list (a@b#c))}"
                                         "{list. length list = length cs \<and> z = snd (argmax_int_list list)}" 
                                         "\<lambda>list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list)"])
        unfolding bij_betw_def image_def inj_on_def
      proof(rule,clarify)
        fix a1 c1 a2 c2::"int list" and b1 b2:: "int" 
        assume "a1 = take (snd (argmax_int_list (a1 @ b1 # c1))) (a1@b1#c1)"
          and  "a2 = take (snd (argmax_int_list (a1 @ b1 # c1))) (a2@b2#c2)"
          and  "b1 = nth (a1@b1#c1) (snd (argmax_int_list (a1 @ b1 # c1)))"
          and  "b2 = nth (a2@b2#c2) (snd (argmax_int_list (a1 @ b1 # c1)))"
          and  "c1 = drop (Suc (snd (argmax_int_list (a1 @ b1 # c1)))) (a1@b1#c1)"
          and  "c2 = drop (Suc (snd (argmax_int_list (a1 @ b1 # c1)))) (a2@b2#c2)"
        then show "a1 @ b1 # c1 = a2 @ b2 # c2 \<Longrightarrow> a1 = a2 \<and> (b1, c1) = (b2, c2)"
          by metis
      next
        show "{y. \<exists>x\<in>{(a, b, c). a = take z (a @ b # c) \<and> length (a @ b # c) = length cs \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> z = snd (argmax_int_list (a @ b # c))}.
           y = (case x of (a, b, c) \<Rightarrow> a @ b # c)} = {list. length list = length cs \<and> z = snd (argmax_int_list list)}"
        proof(rule,clarify,rule)
          fix list
          assume list:"list \<in> {list. length list = length cs \<and> z = snd (argmax_int_list list)}"
          show "list \<in> {y. \<exists>x\<in>{(a, b, c). a = take z (a @ b # c) \<and> length (a @ b # c) = length cs \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> z = snd (argmax_int_list (a @ b # c))}. y = (case x of (a, b, c) \<Rightarrow> a @ b # c)}"
          proof(rule,rule)
            have "snd (argmax_int_list list) < length list"
              using False argmax_int_list_index_le_length[of "list"] list by fastforce 
            then show "list = (case ((take (snd(argmax_int_list list)) list), (nth list (snd(argmax_int_list list))),(drop (Suc (snd(argmax_int_list list))) list)) of (a, b, c) \<Rightarrow> a @ b # c)"
              using id_take_nth_drop[of "(snd(argmax_int_list list))" "list"] by auto
            then have p:"take (snd (argmax_int_list list)) list@ list ! snd (argmax_int_list list)# drop (Suc (snd (argmax_int_list list))) list = list"
              by simp
            show "((take (snd(argmax_int_list list)) list), (nth list (snd(argmax_int_list list))),(drop (Suc (snd(argmax_int_list list))) list)) \<in> {(a, b, c). a = take z (a @ b # c) \<and> length (a @ b # c) = length cs \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> z = snd (argmax_int_list (a @ b # c))}"
              apply(clarify,rewrite p,rewrite p,rewrite p,rewrite p,rewrite p)
              using list by auto
          qed
        qed
        find_theorems "(\<Sum>\<^sup>+ xa. (\<Sum>\<^sup>+ xa. _ ))"
qed

lemma pure_dp_report_noisy_max:
  assumes "1\<le>epsilon1" and "1\<le>epsilon2"
and "is_count_queries cs"
  shows "pure_dp (report_noisy_max cs epsilon1 epsilon2) (epsilon1/epsilon2)"
  using pointwise_pure_dp_inequality_report_noisy_max[of "cs" _ _ "epsilon1" "epsilon2"]
        pointwise_spmf_bound_imp_pure_dp_nat[of "(\<lambda>l. report_noisy_max cs epsilon1 epsilon2 l)" "epsilon1/epsilon2"] 
        assms
  by simp
  
  
  





end
