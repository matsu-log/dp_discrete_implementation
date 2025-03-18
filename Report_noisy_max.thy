section \<open>Report Noisy Max with discrete laplace distribution\<close>

theory Report_noisy_max
  imports "sampler/Discrete_Laplace_rat"
          Differential_Privacy_spmf
          Discrete_laplace_mechanism
begin

subsection \<open>auxiliary lemmas\<close>

lemma map2_add_eq_iff_int:
  shows "\<And>rs1 rs2. length rs1 = length cs \<Longrightarrow> length rs2 = length cs \<Longrightarrow> ((map2 (\<lambda>r::int. (\<lambda>c. r+c))) rs1 cs = (map2 (\<lambda>r::int. (\<lambda>c. r+c)))  rs2 cs) = (rs1 = rs2)"
proof (induct cs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)
  show ?case unfolding zip_Cons
  proof
    show "map (\<lambda>a. case a of (a, b) \<Rightarrow> a + b) (case rs1 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) = map (\<lambda>a. case a of (a, b) \<Rightarrow> a + b) (case rs2 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) \<Longrightarrow> rs1 = rs2"
    proof -
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
    show "rs1 = rs2 \<Longrightarrow> map (\<lambda>a. case a of (a, b) \<Rightarrow> a + b) (case rs1 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs) = map (\<lambda>a. case a of (a, b) \<Rightarrow> a + b) (case rs2 of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, a) # zip zs cs)"
      by simp
  qed
qed

lemma list_restore_by_map2_sub_add:
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

subsection \<open>Define report_noisy_max\<close>

fun argmax_int_list :: "int list \<Rightarrow> (int \<times> nat)" where
"argmax_int_list [] = (0,0)"|
"argmax_int_list [x] = (x,0)"|
"argmax_int_list (x#xs) =(let (m,i) = argmax_int_list xs in (if x\<ge>m then (x,0) else (m,i+1)))"

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

definition is_count_query :: "('a, int) query \<Rightarrow> bool" where
"is_count_query c = (\<forall>(l1, l2)\<in>adj. \<bar>c l1 - c l2\<bar>\<le>1 \<and> 
                                           (if length l1 < length l2 then c l1 \<le> c l2 
                                            else c l2 \<le> c l1))"

definition is_count_queries :: "(('a, int) query) list \<Rightarrow> bool" where
"is_count_queries cs = (\<forall>c\<in>set cs. is_count_query c)"

subsection \<open>component function\<close>
lemma argmax_int_list_index_lt_length:
  shows"0<length list \<Longrightarrow> snd (argmax_int_list list) <length list"
proof (induct list rule: argmax_int_list.induct) 
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x v va)
  then show ?case 
    unfolding argmax_int_list.simps snd_def Let_def 
    thm prod.case_eq_if
    by(simp add: prod.case_eq_if) 
qed

lemma argmax_int_list_fst: 
  shows "length list > 0 \<Longrightarrow>fst (argmax_int_list list)= Max (set list)"
proof(induct list rule:argmax_int_list.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x v va)
  then show ?case
    unfolding argmax_int_list.simps fst_def
    apply(simp add: prod.case_eq_if)
    by(rewrite max_def, rewrite linorder_class.Max_ge_iff,auto)
qed

lemma argmax_int_list_snd:
  shows "length list > 0 \<Longrightarrow> (list ! i = Max (set list) \<and> (\<forall>k<i. list ! i > list ! k)) = (i = snd (argmax_int_list list))"
proof(induct list arbitrary: i rule: argmax_int_list.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by fastforce
next
  case (3 x v va)
  then show ?case 
  proof(cases "x < Max(set (v#va))")
    case True  
    show ?thesis  
    proof
      assume H:"(x#v#va) ! i = Max (set (x#v#va)) \<and> (\<forall>k<i. (x#v#va) ! k < (x#v#va) ! i)"
      have "(x#v#va) ! 0 < Max(set (x#v#va))"
        apply(rewrite nth_Cons_0)        
        unfolding set_simps        
        apply(rewrite Max_insert)        
        using True by auto
      then have i:"1\<le>i"
        using H less_imp_neq linorder_le_less_linear by blast  
      have 1:"(v#va) ! (i - 1) = Max (set (v#va))"
        using H Max_insert[of "set (v#va)" "x"] unfolding set_simps(2)[of "x"] 
        using i by auto  
      have 2:"(\<forall>k<i-1. (v#va) ! k < (v#va) ! (i-1))"
        using H True i
        by (metis Suc_mono diff_Suc_1 diff_is_0_eq not0_implies_Suc not_less_eq_eq nth_Cons_pos zero_less_Suc)  
      have p:"i-1 = snd (argmax_int_list(v#va))"   
        using 1 2 3 i by blast        
      show "i = snd (argmax_int_list (x#v#va))"
        unfolding argmax_int_list.simps
        apply(simp)
        unfolding case_prod_beta
        apply(rewrite p[symmetric], rewrite argmax_int_list_fst,simp)
        apply(rewrite argmax_int_list_fst,simp)
        apply(rewrite if_not_P)
        using True apply linarith
        using i by simp 
    next  
      assume H:"i = snd (argmax_int_list (x#v#va))"
      have 0:"0 \<noteq> snd (argmax_int_list (x#v#va))"
        unfolding argmax_int_list.simps
        apply(simp)
        unfolding case_prod_beta
        apply(rewrite argmax_int_list_fst,simp,rewrite argmax_int_list_fst, simp)
        apply(rewrite if_not_P)
        using True apply linarith
        by simp
      then have i:"1\<le> i"  
        using H by simp
      have p:"i-1 = snd (argmax_int_list (v#va))"          
        apply(rewrite H)
        unfolding argmax_int_list.simps
        apply(simp) unfolding case_prod_beta
        apply(rewrite argmax_int_list_fst,simp)
        apply(rewrite if_not_P)
        using True apply linarith
        by simp
      have 1:"(v#va) ! (i-1) = Max (set (v#va))"  
        using p 3 by auto
      have 2:"(\<forall>k<i-1. (v#va) ! k < (v#va) ! (i-1))"
        using p 3 by auto
      show "(x # v # va) ! i = Max (set (x # v # va)) \<and> (\<forall>k<i. (x # v # va) ! k < (x # v # va) ! i)"  
        using 1 2 i 0 True apply(rewrite set_simps, rewrite Max_insert,auto)         
        by (metis One_nat_def Suc_le_D Suc_le_eq diff_Suc_1 less_Suc_eq_le nth_non_equal_first_eq)
    qed
  next
    case False
    show ?thesis
    proof
      assume H:"(x # v # va) ! i = Max (set (x # v # va)) \<and> (\<forall>k<i. (x # v # va) ! k < (x # v # va) ! i)"
      have "(x # v # va) ! 0 = Max (set (x # v # va)) \<and> (\<forall>k<0. (x # v # va) ! k < (x # v # va) ! 0)"
        using False by(simp)
      then have i:"i=0"
        using  False H by fastforce
      show "i = snd (argmax_int_list (x # v # va))"
        apply(rewrite i)
        unfolding argmax_int_list.simps Let_def case_prod_beta
        apply(rewrite argmax_int_list_fst,simp)
        apply(rewrite if_P)
        using False by(linarith)(simp)
    next
      assume H:"i = snd (argmax_int_list (x # v # va))"
      have i:"i=0"
        apply(rewrite H) unfolding argmax_int_list.simps Let_def case_prod_beta
        apply(rewrite argmax_int_list_fst,simp)
        apply(rewrite if_P)
        using False by(linarith)(simp)
      show "(x # v # va) ! i = Max (set (x # v # va)) \<and> (\<forall>k<i. (x # v # va) ! k < (x # v # va) ! i)"
        apply(rewrite i)+
        apply(rewrite set_simps(2),rewrite Max_insert)
          apply(simp,simp,rewrite max_def)
        using False by simp
    qed
  qed
qed

lemma count_query_imp_sensitivity_1:
  shows "is_count_query c \<Longrightarrow> is_sensitivity c 1"
  unfolding is_count_query_def is_sensitivity_def by auto

lemma count_queries_imp_sensitivity_1:
  shows "is_count_queries cs \<Longrightarrow> \<forall> c\<in> (set cs). is_sensitivity c 1"
  unfolding is_count_queries_def
  using count_query_imp_sensitivity_1 by auto

lemma count_queries_imp_sensitivity_1':
  shows "is_count_queries cs \<Longrightarrow> \<forall>k < length cs. is_sensitivity (cs!k) 1"
  using count_queries_imp_sensitivity_1 by fastforce

lemma count_queries_1:
  assumes "neighbour x y"
  and "length x < length y"
  and "is_count_queries cs"
shows "\<forall>c \<in> set cs. (c x \<le> c y  \<and> c y - 1 \<le> c x)" 
  using assms unfolding is_count_queries_def is_count_query_def adj_def
  by fastforce

lemma count_queries_1':
  assumes "neighbour x y"
  and "length x < length y"
  and "is_count_queries cs"
shows " \<forall>i < length cs. ((cs ! i) x \<le> (cs ! i) y  \<and> (cs ! i)y - 1 \<le> (cs!i) x)" 
  using assms count_queries_1 by fastforce

lemma count_queries_2:
  assumes "neighbour x y"
  and "length x \<ge> length y"
  and "is_count_queries cs"
shows "\<forall>c \<in> set cs. (c y \<le> c x  \<and> c x - 1 \<le> c y)" 
  using assms unfolding is_count_queries_def is_count_query_def adj_def 
  by fastforce

lemma count_queries_2':
  assumes "neighbour x y"
  and "length x \<ge> length y"
shows "is_count_queries cs \<Longrightarrow> \<forall>i < length cs. ((cs ! i) y \<le> (cs ! i) x  \<and> (cs ! i)x - 1 \<le> (cs!i) y)" 
  using assms count_queries_2 by fastforce

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
    proof -
      have "ennreal (spmf (discrete_laplace_noise_add_list (a # cs) epsilon1 epsilon2 x) list) 
          = (\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa))))"
        unfolding discrete_laplace_noise_add_list.simps by(simp add: ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
      also have "... = (\<Sum>\<^sup>+ xa. (\<Sum>\<^sup>+ xb. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) *  (ennreal (spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) xb) * indicator {Some list} (Some (xb # xa)))))"
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
      finally show ?thesis
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
          apply(rewrite zip_map_map)
          by force
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
      using a_cs unfolding is_count_queries_def by auto
    have a:"is_sensitivity a 1"
      using a_cs count_queries_imp_sensitivity_1 by fastforce
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
      proof-
        fix y
        have "pure_dp (\<lambda>x. bind_spmf (discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # y))) (real epsilon1 / real epsilon2)"
          using pure_dp_discrete_laplace_mechanism[of"a" "1" "epsilon1" "epsilon2"] assms
              dp_postprocess_theorem[of "\<lambda>x. discrete_laplace_mechanism a (Suc 0) epsilon1 epsilon2 x" "epsilon1/epsilon2" "\<lambda>noisy_c. (noisy_c # y)"]
              a
          unfolding postprocess_def
          by simp
        then show "pure_dp (\<lambda>x. case (x, y) of (x, noisy_cs) \<Rightarrow> discrete_laplace_mechanism a 1 epsilon1 epsilon2 x \<bind> (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs))) (real epsilon1 / real epsilon2)" 
          by simp
      qed
      show "\<And>x. lossless_spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x)"
        using lossless_discrete_laplace_noise_add_list assms by simp
      show "\<And>x y. lossless_spmf (case (x, y) of (x, noisy_cs) \<Rightarrow> bind_spmf (discrete_laplace_mechanism a 1 epsilon1 epsilon2 x) (\<lambda>noisy_c. return_spmf (noisy_c # noisy_cs)))"
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

subsection \<open>report_noisy_max\<close>

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
    proof -
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
      then have "(\<Sum>\<^sup>+ xa. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) xa) * indicator {Some z} (Some (snd (argmax_int_list xa)))) = 0"
        by(rewrite nn_integral_0_iff,auto)
      then show ?thesis 
        unfolding report_noisy_max_def by(simp add:ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
    qed
    then show ?thesis by simp
  qed
qed

lemma ennreal_spmf_report_noisy_max_simps_step1:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2" and "z<length cs"
shows "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = 
      (\<Sum>\<^sup>+ list\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list))"
proof -
  have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))))"
    unfolding report_noisy_max_def
    by(simp add: ennreal_spmf_bind nn_integral_measure_spmf ennreal_indicator)
  also have "... = (\<Sum>\<^sup>+ list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {list. length list = length cs \<and> z = snd (argmax_int_list list)} list)"
  proof(rule nn_integral_cong)
    fix list::"int list"
    show "ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {Some z} (Some (snd (argmax_int_list list))) =
          ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list) * indicator {list. length list = length cs \<and> z = snd (argmax_int_list list)} list"
    proof(cases "length list = length cs")
      case True
      then show ?thesis
      proof -
        have "indicator {Some z} (Some (snd (argmax_int_list list))) = indicator {list. length list = length cs \<and> z = snd (argmax_int_list list)} list"
          unfolding indicator_def using True by simp
        then show ?thesis by (rule arg_cong)
      qed
    next
      case False
      then show ?thesis 
        using spmf_discrete_laplace_noise_add_list_zero by force
    qed
  qed   
  also have "... = (\<Sum>\<^sup>+ list\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list))"
    using nn_integral_count_space_indicator[of "{list. length list = length cs \<and> z = snd (argmax_int_list list)}" "\<lambda>list. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list)",symmetric]
    by simp
  finally show ?thesis by simp
qed

lemma ennreal_spmf_report_noisy_max_simps_step2:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2" and "z<length cs"
shows "(\<Sum>\<^sup>+ list\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list))
     = (\<Sum>\<^sup>+ (a, c)\<in>{(a, c). length a = z \<and> length c = length cs - (z + 1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
proof -
  have "(\<Sum>\<^sup>+ list\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list)) 
      = (\<Sum>\<^sup>+ ((a, c), b)\<in>{((a,c),b). a = take z (a@b#c) \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> length (a@b#c) = length cs \<and> z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a@b#c)))"
    using nn_integral_bij_count_space[of "\<lambda>((a,c),b). a@b#c" "{((a,c),b). a = take z (a@b#c) \<and> b = nth (a@b#c) z \<and> c = drop (Suc z) (a@b#c) \<and> length (a@b#c) = length cs \<and> z = snd (argmax_int_list (a@b#c))}" "{list. length list = length cs \<and> z = snd (argmax_int_list list)}",symmetric]
  proof
    show "bij_betw (\<lambda>((a, c), b). a @ b # c) {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))} {list. length list = length cs \<and> z = snd (argmax_int_list list)}"
      unfolding bij_betw_def
    proof
      show "inj_on (\<lambda>((a, c), b). a @ b # c) {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}"
        unfolding inj_on_def
        by(clarify)(metis)
      show "(\<lambda>((a, c), b). a @ b # c) ` {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))} = {list. length list = length cs \<and> z = snd (argmax_int_list list)}"
        unfolding image_def
      proof
        show "{y. \<exists>x\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. y = (case x of (x, xa) \<Rightarrow> (case x of (a, c) \<Rightarrow> \<lambda>b. a @ b # c) xa)} \<subseteq> {list. length list = length cs \<and> z = snd (argmax_int_list list)}"
          by force
        show "{list. length list = length cs \<and> z = snd (argmax_int_list list)} \<subseteq> {y. \<exists>x\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. y = (case x of (x, xa) \<Rightarrow> (case x of (a, c) \<Rightarrow> \<lambda>b. a @ b # c) xa)}"
        proof(clarify)
          fix list::"int list"
          assume H1:"length list = length cs" and H2:"z = snd (argmax_int_list list)"
          let ?a = "take z list"
          let ?b = "nth list z" 
          let ?c = "drop (Suc z) list"
          have p:"?a = take (snd (argmax_int_list list)) (?a) @ take (snd (argmax_int_list list) - length ?a) (?b # ?c) \<and>
                ?b = (?a @ ?b # ?c) ! snd (argmax_int_list list) \<and>
                ?c = drop (Suc (snd (argmax_int_list list))) (?a) @ drop (Suc (snd (argmax_int_list list)) - length (?a)) (?b # ?c) \<and>
                 Suc (length (?a) + length (?c)) = length cs \<and> snd (argmax_int_list list) = snd (argmax_int_list (?a @ ?b # ?c)) \<and> list = ?a @ ?b # ?c"
          proof -
            have list:"list = ?a @ ?b # ?c"
              using H1 H2 assms id_take_nth_drop[of"z" "list"] by simp
            show ?thesis
              using list assms H1 H2 by simp
          qed
          show "\<exists>xa\<in>{((a, c), b).
               a = take (snd (argmax_int_list list)) (a @ b # c) \<and>
               b = (a @ b # c) ! snd (argmax_int_list list) \<and> c = drop (Suc (snd (argmax_int_list list))) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> snd (argmax_int_list list) = snd (argmax_int_list (a @ b # c))}.
            list = (case xa of (x, xa) \<Rightarrow> (case x of (a, c) \<Rightarrow> \<lambda>b. a @ b # c) xa)"
            using H1 H2 apply simp 
            using p by blast
        qed
      qed
    qed
    show "(\<Sum>\<^sup>+ ((a, c), b)\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))
        = (\<Sum>\<^sup>+ list\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (case list of (x, xa) \<Rightarrow> (case x of (a, c) \<Rightarrow> \<lambda>b. a @ b # c) xa)))"
      unfolding case_prod_beta by simp
  qed
  also have "... = (\<Sum>\<^sup>+ (a, c)\<in>{(a, c). length a = z \<and> length c = length cs - (z + 1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
  proof -
    have "(\<Sum>\<^sup>+ ((a, c), b)\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))
        = (\<Sum>\<^sup>+ ((a, c), b)\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs \<and> z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c))))" 
      apply(rule nn_integral_cong)
      unfolding case_prod_beta by simp
    also have "... = (\<Sum>\<^sup>+ ((a, c), b)\<in>{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c))))"
      unfolding indicator_def
      apply(rule nn_integral_count_space_eq)
       apply(clarify,simp)
      by(clarify,simp)
    also have "... = (\<Sum>\<^sup>+ ((a, c), b). ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c))) * indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a,c),b))"
      using nn_integral_count_space_indicator[of "{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs}" "\<lambda>((a,c),b). ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c)))"]
      unfolding case_prod_beta by simp
    also have "... = (\<Sum>\<^sup>+ (a, c). \<Sum>\<^sup>+ b. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c))) * indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b))"   
      using nn_integral_fst_count_space[of "\<lambda>((a,c),b).  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c)))
                               *  indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a@b#c) = length cs} ((a, c), b)"]
      unfolding case_prod_beta by simp
    also have "... = (\<Sum>\<^sup>+ (a,c). (\<Sum>\<^sup>+ b.  ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) *indicator {(a,c). length a = z \<and> length c = length cs - (z+1)} (a,c) * indicator {b. z = snd (argmax_int_list (a@b#c))} b)::ennreal)"
    proof(rule nn_integral_cong,clarify,rule nn_integral_cong)
      fix a b c
      have p:"(indicator {z} (snd (argmax_int_list (a @ b # c))) * indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b) ::ennreal)
          = indicator {(a,c). length a = z \<and> length c = length cs - (z+1)} (a,c) * indicator {b. z = snd (argmax_int_list (a@b#c))} b"
      proof -
        have "indicator {z} (snd (argmax_int_list (a @ b # c))) * ((indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)::ennreal))
            = indicator {z} (snd (argmax_int_list (a @ b # c))) * (indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)::ennreal)"
        proof -
          have set_eq:"{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} = {((a, c),b). length a = z \<and> length c = length cs - (z + 1)}"
          proof
            show "{((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} \<subseteq> {((a, c), b). length a = z \<and> length c = length cs - (z + 1)}"
              apply clarify
              using assms length_take[of "z"] length_drop[of "Suc z"] 
              by (metis Suc_eq_plus1 min.absorb4)
            show "{((a, c), b). length a = z \<and> length c = length cs - (z + 1)} \<subseteq> {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs}"
              apply(clarify) 
              using assms by simp
          qed
          show ?thesis 
            apply(rewrite set_eq)
            unfolding indicator_def by simp
        qed
        also have "... = indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c) * indicator {b. z = snd (argmax_int_list (a @ b # c))} b"
          unfolding indicator_def by simp
        finally show ?thesis by simp
      qed
      then show "ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {z} (snd (argmax_int_list (a @ b # c))) * indicator {((a, c), b). a = take z (a @ b # c) \<and> b = (a @ b # c) ! z \<and> c = drop (Suc z) (a @ b # c) \<and> length (a @ b # c) = length cs} ((a, c), b)
               = ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c) * indicator {b. z = snd (argmax_int_list (a @ b # c))} b"
        apply(rewrite mult.assoc)
        apply(rewrite p, rewrite mult.assoc)
        by simp
    qed
    also have "... =  (\<Sum>\<^sup>+ (a, c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c))  * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)))"
    proof(rule nn_integral_cong,clarify)
      fix a c::"int list"
      show "(\<integral>\<^sup>+ba\<in>{ba. z = snd (argmax_int_list (a @ ba # c))}. (ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ ba # c)) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c))\<partial>count_space UNIV) =
           (\<Sum>\<^sup>+ ba\<in>{ba. z = snd (argmax_int_list (a @ ba # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ ba # c)) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c)) "
        by(rewrite nn_integral_count_space_indicator[of "{ba. z = snd (argmax_int_list (a @ ba # c))}"],auto)
    qed
    also have "... = (\<Sum>\<^sup>+ (a, c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c))) * indicator {(a, c). length a = z \<and> length c = length cs - (z + 1)} (a, c))"
      apply(rewrite ab_semigroup_mult_class.mult.commute, rewrite nn_integral_cmult,simp)
      by(rewrite ab_semigroup_mult_class.mult.commute,simp)
    also have "... = (\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
      using nn_integral_count_space_indicator[of "{(a,c). length a = z \<and> length c = length cs - (z+1)}" "\<lambda>(a,c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"]
      unfolding case_prod_beta
      by simp
    finally show ?thesis
      by simp
  qed
  finally show ?thesis by simp
qed

lemma ennreal_spmf_report_noisy_max_simps_step3:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "z<length cs"
  shows "(\<Sum>\<^sup>+ (a, c)\<in>{(a, c). length a = z \<and> length c = length cs - (z + 1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c))) =
         (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
       \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
proof -
  have "(\<Sum>\<^sup>+ (a, c)\<in>{(a,c). length a = z \<and> length c = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a@b#c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))
    = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra,rc). length ra = z \<and> length rc = length cs - (z+1)}. \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs)))@b#(map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs)))))}.
                                                                                             ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs))) @ b # (map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs))))))"
    using nn_integral_bij_count_space[of "\<lambda>(ra,rc). ((map2 (\<lambda>r::int. (\<lambda>c. r+c)) ra (take z (map (\<lambda>q. q(x)) cs))), (map2 (\<lambda>r::int. (\<lambda>c. r+c)) rc (drop (Suc z) (map (\<lambda>q. q(x)) cs))))"
                                         "{(ra,rc). length ra = z \<and> length rc = length cs - (z+1)}" "{(a,c). length a = z \<and> length c = length cs - (z+1)}"
                                         "\<lambda>(a,c). (\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"]  
    unfolding case_prod_beta fst_conv snd_conv
  proof
    show "bij_betw (\<lambda>p. (map (\<lambda>p. fst p + snd p) (zip (fst p) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd p) (drop (Suc z) (map (\<lambda>q. q x) cs)))))
                     {p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}
                     {p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}"
      unfolding bij_betw_def inj_on_def image_def
    proof
      show "\<forall>l1\<in>{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}.
            \<forall>l2\<in>{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}.
            (map (\<lambda>p. fst p + snd p) (zip (fst l1) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd l1) (drop (Suc z) (map (\<lambda>q. q x) cs)))) =
            (map (\<lambda>p. fst p + snd p) (zip (fst l2) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd l2) (drop (Suc z) (map (\<lambda>q. q x) cs)))) \<longrightarrow> l1 = l2"
      proof clarify
        fix a c ra rc::"int list"
        assume H1:"length (snd (a, c)) = length cs - (length (fst (a, c)) + 1)" and
               H2:"z = length (fst (a, c))" and
               H3:"length (fst (ra, rc)) = length (fst (a, c))" and
               H4:"length (snd (ra, rc)) = length cs - (length (fst (a, c)) + 1)" and
               H5:"map (\<lambda>p. fst p + snd p) (zip (fst (a, c)) (take (length (fst (a, c))) (map (\<lambda>q. q x) cs))) = map (\<lambda>p. fst p + snd p) (zip (fst (ra, rc)) (take (length (fst (a, c))) (map (\<lambda>q. q x) cs)))" and
               H6:"map (\<lambda>p. fst p + snd p) (zip (snd (a, c)) (drop (Suc (length (fst (a, c)))) (map (\<lambda>q. q x) cs))) = map (\<lambda>p. fst p + snd p) (zip (snd (ra, rc)) (drop (Suc (length (fst (a, c)))) (map (\<lambda>q. q x) cs)))"
        have 1:"length a = length (take (length a) (map (\<lambda>q. q x) cs))"
          using H2 assms by simp
        have 2:"length ra = length (take (length a) (map (\<lambda>q. q x) cs))"
          using H2 H3 assms by simp
        have 3:"map2 (+) a (take (length a) (map (\<lambda>q. q x) cs)) = map2 (+) ra (take (length a) (map (\<lambda>q. q x) cs))"
         using H5 unfolding case_prod_beta by simp
       have p1:"a = ra"
         using map2_add_eq_iff_int[of "a" "(take (length a) (map (\<lambda>q. q x) cs))" "ra"] 1 2 3
         by simp
       have 4:"length c = length (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
         using H1 H2 assms by simp
       have 5:"length rc = length (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
         using H4 H2 assms by simp
       have 6:"map2 (+) c (drop (Suc (length a)) (map (\<lambda>q. q x) cs)) = map2 (+) rc (drop (Suc (length a)) (map (\<lambda>q. q x) cs))"
         using H6 unfolding case_prod_beta by simp
       have p2:"c = rc"
         using map2_add_eq_iff_int[of "c" "(drop (Suc (length a)) (map (\<lambda>q. q x) cs))" "rc"] 4 5 6
         by simp
       show "a = ra \<and> c = rc" using p1 p2 by simp
     qed
     show "{y. \<exists>xa\<in>{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}. y = (map (\<lambda>p. fst p + snd p) (zip (fst xa) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd xa) (drop (Suc z) (map (\<lambda>q. q x) cs))))}
        = {p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}"
     proof
       show "{y. \<exists>xa\<in>{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}. y = (map (\<lambda>p. fst p + snd p) (zip (fst xa) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd xa) (drop (Suc z) (map (\<lambda>q. q x) cs))))} \<subseteq> {p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}"
       proof clarify
         fix a c ra rc::"int list"
         assume H1:"length (snd (ra, rc)) = length cs - (length (fst (ra, rc)) + 1)" and
                H2:"z = length (fst (ra, rc))"
         show "length (fst (map (\<lambda>p. fst p + snd p) (zip (fst (ra, rc)) (take (length (fst (ra, rc))) (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd (ra, rc)) (drop (Suc (length (fst (ra, rc)))) (map (\<lambda>q. q x) cs))))) = length (fst (ra, rc)) \<and>
              length (snd (map (\<lambda>p. fst p + snd p) (zip (fst (ra, rc)) (take (length (fst (ra, rc))) (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd (ra, rc)) (drop (Suc (length (fst (ra, rc)))) (map (\<lambda>q. q x) cs))))) = length cs - (length (fst (ra, rc)) + 1)"
           using H1 H2 assms by simp
        qed
        show "{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)} \<subseteq> {y. \<exists>xa\<in>{p. length (fst p) = z \<and> length (snd p) = length cs - (z + 1)}. y = (map (\<lambda>p. fst p + snd p) (zip (fst xa) (take z (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd xa) (drop (Suc z) (map (\<lambda>q. q x) cs))))}"
        proof clarify
          fix a c::"int list"
          assume H1:"length (snd (a, c)) = length cs - (length (fst (a, c)) + 1)" and
                 H2:"z = length (fst (a, c))"
          let ?ra = "(map2 (\<lambda>a q. a-q) a (take (length a) (map (\<lambda>q. q x) cs)))"
          let ?rc = "(map2 (\<lambda>a q. a-q) a (drop (Suc (length (fst (a, c)))) (map (\<lambda>q. q x) cs)))"
          show "\<exists>xa\<in>{p. length (fst p) = length (fst (a, c)) \<and> length (snd p) = length cs - (length (fst (a, c)) + 1)}.
              (a, c) = (map (\<lambda>p. fst p + snd p) (zip (fst xa) (take (length (fst (a, c))) (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd xa) (drop (Suc (length (fst (a, c)))) (map (\<lambda>q. q x) cs))))"
          proof 
            let ?l = "((map2 (\<lambda>a q. a-q) a (take (length a) (map (\<lambda>q. q x) cs))), (map2 (\<lambda>c q. c-q) c (drop (Suc(length a)) (map (\<lambda>q. q x) cs))))"
            have 1:"length (map2 (\<lambda>a q. a-q) a (take (length a) (map (\<lambda>q. q x) cs))) = length a"
              using assms H2 by(auto)
            have 2:"length (map2 (\<lambda>c q. c-q) c (drop (Suc(length a)) (map (\<lambda>q. q x) cs))) = length cs - Suc (length a)"
              using assms H1 by auto
            have 3:"a = map (\<lambda>p. fst p + snd p) (zip (map2 (\<lambda>a q. a-q) a (take (length a) (map (\<lambda>q. q x) cs))) (take (length a) (map (\<lambda>q. q x) cs)))"
              using list_restore_by_map2_sub_add H2 1 by simp
            have 4:"c = map (\<lambda>p. fst p + snd p) (zip (map2 (\<lambda>c q. c-q) c (drop (Suc(length a)) (map (\<lambda>q. q x) cs))) (drop (Suc (length a)) (map (\<lambda>q. q x) cs)))"
              using list_restore_by_map2_sub_add H1 2 by simp
            show "(a,c) = (map (\<lambda>p. fst p + snd p) (zip (fst ?l) (take (length (fst (a, c))) (map (\<lambda>q. q x) cs))), map (\<lambda>p. fst p + snd p) (zip (snd ?l) (drop (Suc (length (fst (a, c)))) (map (\<lambda>q. q x) cs))))"
              using 3 4 by simp
           show "?l \<in> {p. length (fst p) = length (fst (a, c)) \<and> length (snd p) = length cs - (length (fst (a, c)) + 1)}"
             using 1 2 by simp
         qed
       qed
     qed
   qed
 qed
  also have "... = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
         \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
  proof(rule nn_integral_cong,clarify)
    fix ra rc::"int list"
    assume "(ra, rc) \<in> space (count_space {(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)})"
    then have H:"z = length ra" and "length rc = length cs - Suc(length ra)" by simp_all
    show "(\<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ b # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ b # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))) =
           (\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
      using nn_integral_bij_count_space[of "\<lambda>rb. rb+(cs!z) x" "{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}"
                                             "{b. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ b # map2 (+) rc (drop (Suc (z)) (map (\<lambda>q. q x) cs))))}"
                                             "\<lambda>b. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ b # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))"]
      unfolding case_prod_beta fst_conv snd_conv
    proof
      show "bij_betw (\<lambda>rb. rb + (cs ! z) x) {rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}
     {b. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ b # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))} "
        unfolding bij_betw_def inj_on_def image_def
      proof 
        show "\<forall>rb1\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}.
              \<forall>rb2\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}. rb1 + (cs ! z) x = rb2 + (cs ! z) x \<longrightarrow> rb1 = rb2"
          apply clarify
          using H by simp
        show "{b. \<exists>rb\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}. b = rb + (cs ! z) x} =
              {b. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ b # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}"
        proof
          show "{b. \<exists>rb\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}. b = rb + (cs ! z) x}
              \<subseteq> {b. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ b # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}"
            using H by auto
          show "{b. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ b # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}
              \<subseteq> {b. \<exists>rb\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}. b = rb + (cs ! z) x}"
          proof clarify
            fix b::int
            assume H1:"z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ b # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
            show "\<exists>rb\<in>{rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}. b = rb + (cs ! z) x"
            proof
              show "b= (b- (cs ! z) x) + (cs ! z) x"
                using H H1 by simp
              show "(b- (cs ! z) x)\<in> {rb. z = snd (argmax_int_list (map (\<lambda>p. fst p + snd p) (zip ra (take z (map (\<lambda>q. q x) cs))) @ (rb + (cs ! z) x) # map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))}"
                using H H1 by simp
            qed
          qed
        qed
      qed
    qed
  qed
  finally show ?thesis
    by simp
qed

lemma ennreal_spmf_report_noisy_max_simps:
  assumes "0<length cs"
and "1\<le>epsilon1" and "1\<le>epsilon2"
and "z<length cs"
  shows "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) =
         (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
       \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
proof -
  have "ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) = (\<Sum>\<^sup>+ list\<in>{list. length list = length cs \<and> z = snd (argmax_int_list list)}. ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) list))"
    using assms ennreal_spmf_report_noisy_max_simps_step1 by simp
  also have "... = (\<Sum>\<^sup>+ (a, c)\<in>{(a, c). length a = z \<and> length c = length cs - (z + 1)}.
       \<Sum>\<^sup>+ b\<in>{b. z = snd (argmax_int_list (a @ b # c))}.
       ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (a @ b # c)))"
    using ennreal_spmf_report_noisy_max_simps_step2 assms by simp
  also have "... = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
         \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
         ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb+nth cs z x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
    using ennreal_spmf_report_noisy_max_simps_step3 assms by simp
  finally show ?thesis by simp
qed
    
lemma fix_noise:
  assumes "1\<le>epsilon1"
    and "1\<le>epsilon2"
    and "length cs = length ra + length rc +1"
  shows "spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))
        = ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs * 
          (\<Prod>(r,i)\<in>set (zip (map real_of_int ra) [0.. int(length ra)-1]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))
          * exp (- (real epsilon1 * \<bar>rb\<bar>) / real epsilon2) 
          * (\<Prod>(r,i)\<in>set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
proof-
  have 1:"spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))
      = ((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs *
    (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)]).
       exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))"
  apply(rewrite spmf_discrete_laplace_noise_add_list)
    using assms by simp_all  
  have 2:"(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
      = (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
        (\<Prod>((c, z), i)\<in>{((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}. exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
        (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))"
  proof -
    have 1:"set (zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [0..int (length cs - 1)])
           = set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y)  cs))))) [0..int(length ra -1)])
           \<union> {(((\<lambda>x::'a list. real_of_int ((cs ! length ra)x)), real_of_int(rb + (cs ! length ra) y)), int (length ra))}
           \<union> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra))cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y)  cs))))) [(length ra +1)..int(length cs -1)])"
    proof -
      have 1:"zip
                  (zip 
                      (map (\<lambda>h x. real_of_int (h x)) cs) 
                      (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) 
                                        @ (rb + (cs ! length ra) y) 
                                        # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) 
                   [0..int (length cs - 1)]
      = zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs))  (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y)  cs))))) [0..int(length ra -1)] 
        @ (((\<lambda>x::'a list. real_of_int ((cs ! length ra)x)), real_of_int(rb + (cs ! length ra) y)), int (length ra)) 
        # zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra))cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y)  cs))))) [(length ra +1)..int(length cs -1)]" (is "?lhs = ?rhs")
      proof -
        have r1:"(((\<lambda>x::'a list. real_of_int ((cs ! length ra)x)), real_of_int(rb + (cs ! length ra) y)), int (length ra))# zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra))cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y)  cs))))) [(length ra +1)..int(length cs -1)]
            = zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (length ra)cs)) (map real_of_int (map2 (+) (rb#rc) (drop (length ra) (map (\<lambda>q. q y)  cs))))) [(length ra)..int(length cs -1)]"
        proof(rewrite list_eq_iff_nth_eq)
          let ?l1 = "((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra)) # zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]"
          let ?l2 = "zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (length ra) cs)) (map real_of_int (map2 (+) (rb # rc) (drop (length ra) (map (\<lambda>q. q y) cs))))) [int (length ra)..int (length cs - 1)]"
          have length:"length ?l1 = length ?l2"
            using assms by simp
          have elem:"\<forall>i<length ?l1. ?l1 ! i = ?l2 ! i"
          proof clarify
            fix i
            assume i:"i < length ?l1"
            show "?l1 ! i = ?l2 ! i"
            proof(cases "i=0")
              case True
              then show ?thesis
                apply(rewrite True, rewrite True, rewrite nth_Cons_0)
                apply(rewrite nth_zip,simp add:assms, simp add:assms)
                apply(rewrite nth_zip, simp add:assms,simp add:assms)
                by(rewrite drop_map[symmetric], rewrite nth_drop, simp_all add: assms)
            next
              case False
              then show ?thesis 
                using i assms by simp
            qed
          qed
          show "(length ?l1 = length ?l2) \<and> (\<forall>i<length ?l1. ?l1 ! i = ?l2 ! i)"
            using length elem assms by simp
        qed
        have r:"?rhs = zip (zip (map (\<lambda>h x. real_of_int (h x)) cs)  (map real_of_int (map2 (+) (ra@rb#rc) (map (\<lambda>q. q y)  cs)))) [0..int(length cs -1)]"
        proof(rewrite r1)
          let ?l = "zip (zip (map (\<lambda>h x. real_of_int (h x)) cs)  (map real_of_int (map2 (+) (ra@rb#rc) (map (\<lambda>q. q y)  cs)))) [0..int(length cs -1)]"
          let ?a = "zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)] "
          let ?bc = "zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (length ra) cs)) (map real_of_int (map2 (+) (rb # rc) (drop (length ra) (map (\<lambda>q. q y) cs))))) [int (length ra)..int (length cs - 1)]"
          show "?a @ ?bc = ?l"
          proof (cases "ra = []")
            case True
            then show ?thesis by simp
          next
            case False
            then show ?thesis 
            proof -
              have 1:"zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)))) @
                  zip (map (\<lambda>h x. real_of_int (h x)) (drop (length ra) cs)) (map real_of_int (map2 (+) (rb # rc) (drop (length ra) (map (\<lambda>q. q y) cs)))) 
                = zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) (ra@rb#rc)  (map (\<lambda>q. q y) cs)))"
                apply(rewrite zip_append[symmetric], simp add: assms)
                apply(rewrite drop_map[symmetric],rewrite take_map[symmetric])
                apply(rewrite append_take_drop_id)
                apply(rewrite map_append[symmetric])
                apply(rewrite map_append[symmetric])
                apply(rewrite zip_append[symmetric], simp add:assms)
                apply(rewrite append_take_drop_id)
                by simp
              have 2:"[0..int (length ra - 1)] @ [int (length ra)..int (length cs - 1)] = [0..(length cs -1)]" 
              proof -
                have "int (length ra - 1) = int (length ra) - 1"
                proof(rewrite SMT.int_ops(6))
                  have "0 < length ra"
                    using False by simp
                  then have "\<not> int (length ra) < 1"
                    by linarith
                  then show "(if int (length ra) < int 1 then 0 else int (length ra) - int 1) = int (length ra) - 1" by simp
                qed
                then show ?thesis
                  using False assms
                  by (metis add_implies_diff le_add1 nat_int_comparison(3) of_nat_0_le_iff upto_split1)
              qed
              have 3:"length (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) = length [0..int (length ra - 1)]"
                using assms False by (simp)(metis Suc_pred int_ops(4) length_greater_0_conv nat_int)
              show ?thesis
                using False 3
                apply (rewrite zip_append[symmetric])
                 apply simp
                apply(rewrite zip_append)
                 apply simp
                apply(rewrite zip_append[symmetric])
                 apply simp
                using 1 2 by simp
            qed
          qed
        qed
        have l:"?lhs = zip (zip (map (\<lambda>h x. real_of_int (h x)) cs) (map real_of_int (map2 (+) (ra @ rb # rc) (map (\<lambda>q. q y) cs)))) [0..int (length cs - 1)]"
        proof -
          have " (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) = (map2 (+) (ra @ rb # rc) (map (\<lambda>q. q y) cs))"
          proof -
            have 1:"(rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)) =  map2 (+) (rb#rc) (drop (length ra) (map (\<lambda>q. q y) cs))"
            proof(rewrite list_eq_iff_nth_eq)
              let ?l1 = "(rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))"
              let ?l2 = "map2 (+) (rb # rc) (drop (length ra) (map (\<lambda>q. q y) cs))"
              have 1:"length ?l1 = length ?l2" using assms by simp
              have 2:"\<forall>i<length ?l1. ?l1 ! i = ?l2 ! i"
              proof clarify
                fix i
                assume i:"i < length ?l1"
                show "?l1 ! i = ?l2 ! i"
                proof (cases "i=0")
                  case True
                  then show ?thesis
                    apply(rewrite True,rewrite True, rewrite nth_Cons_0)
                    by(rewrite nth_map,simp add:assms, rewrite nth_zip,simp_all add:assms)
                next
                  case False
                  then show ?thesis
                    using i assms by simp
                qed
              qed
              show "(length ?l1 = length ?l2) \<and> (\<forall>i<length ?l1. ?l1 ! i = ?l2 ! i)"
                using 1 2 assms by simp
            qed
            show ?thesis
              apply(rewrite 1)
              apply(rewrite map_append[symmetric], rewrite zip_append[symmetric],simp add:assms)
              by(rewrite append_take_drop_id, simp)
          qed
          then show ?thesis by simp
        qed
        show ?thesis using l r by simp
      qed
      then show ?thesis by simp
    qed
    have 2:"(set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]) \<union>
             {((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}) \<inter>
            set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]) = {}"
    proof(rule subset_antisym,clarify)
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
    proof(rule subset_antisym,clarify)
      fix a b ba
      have " ((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))
         \<notin> set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)])"
        by(rewrite in_set_zip, auto)
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
   have ra:"(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (epsilon1 * \<bar>z - c y\<bar>) / epsilon2))
       = (\<Prod>(r,i)\<in>set (zip (map real_of_int ra) [0.. int(length ra)-1]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
   proof(cases "ra=[]")
     case True
     then show ?thesis by simp
   next
     case False
     show ?thesis
       using comm_monoid_mult_class.prod.reindex_bij_betw[of "\<lambda>((c,z),i). (z - c y,i)" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)])"
                                                         "set (zip ra [0.. int(length ra)-1])" "\<lambda>(r,i). exp (- (epsilon1 * \<bar>r\<bar>) / epsilon2)"]
       unfolding case_prod_beta fst_conv snd_conv
     proof
       show "bij_betw (\<lambda>p. (snd (fst p) - fst (fst p) y, snd p)) (set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]))
       (set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1])))"
         unfolding bij_betw_def inj_on_def image_def
       proof
         show "\<forall>a1\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]).
               \<forall>a2\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]).
                (snd (fst a1) - fst (fst a1) y, snd a1) = (snd (fst a2) - fst (fst a2) y, snd a2) \<longrightarrow> a1 = a2"
         proof (clarify)
           fix a1 i1 c1 a2 i2 c2 
           assume H1:"((a1, c1), i1) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)])"
              and H2:"((a2, c2), i2) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)])" 
              and H3:"snd (fst ((a1, c1), i1)) - fst (fst ((a1, c1), i1)) y = snd (fst ((a2, c2), i2)) - fst (fst ((a2, c2), i2)) y "
              and H4:"snd ((a1, c1), i1) = snd ((a2, c2), i2)"
           show "(a1, c1) = (a2, c2) \<and> i1 = i2"
             using H1 H2 H3 H4 assms unfolding in_set_zip by auto
         qed
       next
         show "{ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)} 
             = set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
         proof 
           show "{ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)}
                  \<subseteq> set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
           proof clarify
             fix a b c
             assume H:"((a, b), c) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)])"
             have c:"0\<le>c"
               using H set_zip_rightD by fastforce
           have c':"c\<le> length ra - Suc 0"
             using H set_zip_rightD by fastforce
           have c_ra:"nat c < length ra"   
             using False c' Suc_le_eq length_0_conv nat.distinct(1) of_nat_diff of_nat_le_0_iff of_nat_less_imp_less by fastforce
           have a:"a = (map (\<lambda>h p. real_of_int (h p)) (take(length ra) cs)) ! (nat c)"
             using H c unfolding in_set_zip by auto
           have b:"b = (map (real_of_int \<circ> (\<lambda>p. fst p + snd p)) (zip ra (take (length ra) (map (\<lambda>q. q y) cs))))! (nat c)"
             using H c unfolding in_set_zip by auto    
           have p1:"snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y = ra ! (nat c)"
             unfolding fst_conv snd_conv
             apply(rewrite a, rewrite b)
             using assms c c' c_ra by simp
           have p2:"ra ! nat c = fst (ra ! nat c,c) \<and> c = snd (ra ! nat c, c)" by simp
           show "(snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y, snd ((a, b), c)) \<in> set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
             apply(rewrite p1,simp)
             unfolding image_def 
             apply simp
             apply(rule bexI)
             using p2 apply blast
             unfolding in_set_zip using c c_ra False by auto
         qed
         show "set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))
                \<subseteq> {ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)}"
         proof clarify
           fix r i
           assume H:"(r, i) \<in> set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
           have i1:"0\<le> i"
             using H set_zip_rightD by fastforce
           have i2:"nat i < length ra "
             using H set_zip_rightD by fastforce
           show "\<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)]). (r, i) = (snd (fst x) - fst (fst x) y, snd x)"
           proof
             let ?x = "(((map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) ! nat i , real_of_int (ra ! nat i + (cs ! nat i) y)),i)"
             show "(r, i) = (snd (fst ?x) - fst (fst ?x) y, snd ?x)"
               using H apply simp
               using i1 i2 assms apply simp
               unfolding image_def
               apply simp
               apply clarify
               apply simp
               unfolding in_set_zip by auto
             show "?x \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) [0..int (length ra - 1)])"
               unfolding in_set_zip
             proof
               let ?n = "nat i"
               have 1:"zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs))))) ! ?n = fst ((map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs) ! nat i, real_of_int (ra ! nat i + (cs ! nat i) y)), i)"
                 apply(rewrite nth_zip)
                 using assms i1 i2 by simp_all
               have 2:"[0..int (length ra - 1)] ! ?n = snd ((map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs) ! nat i, real_of_int (ra ! nat i + (cs ! nat i) y)), i)"
                 using i2 i1 by simp
               have 3:"?n < length (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) \<and> ?n < length [0..int (length ra - 1)]"
                 using i1 i2 assms by simp
               show "zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs))))) ! ?n = fst ((map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs) ! nat i, real_of_int (ra ! nat i + (cs ! nat i) y)), i) \<and>
                    [0..int (length ra - 1)] ! ?n = snd ((map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs) ! nat i, real_of_int (ra ! nat i + (cs ! nat i) y)), i) \<and>
                    ?n < length (zip (map (\<lambda>h p. real_of_int (h p)) (take (length ra) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip ra (take (length ra) (map (\<lambda>q. q y) cs)))))) \<and> ?n < length [0..int (length ra - 1)]"
                 using 1 2 3 by simp
             qed
           qed
         qed
       qed
     qed 
     show "(\<Prod>p\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2)) = (\<Prod>p\<in>set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1])). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2))" 
     proof-
       have "set (zip (map real_of_int ra) [0..int (length ra) - 1]) = set (map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1]))"
       proof -
         have "zip (map real_of_int ra) [0..int (length ra) - 1] = map (\<lambda>p. (real_of_int (fst p), snd p)) (zip ra [0..int (length ra) - 1])"
           by(rewrite zip_map1,auto)
         then show ?thesis by simp
       qed
       then show ?thesis by auto
     qed
   qed
 qed
  have rc:"(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
      = (\<Prod>(r,i)\<in>set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / epsilon2))"
    using comm_monoid_mult_class.prod.reindex_bij_betw[of "\<lambda>((c,z),i). (z - c y,i)" "set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)])"
                                                          "set (zip (map real_of_int rc) [int(length ra+1).. int(length cs -1)])" "\<lambda>(r,i). exp (- (epsilon1 * \<bar>r\<bar>) / epsilon2)"]
    unfolding case_prod_beta fst_conv snd_conv
  proof
    show "bij_betw (\<lambda>p. (snd (fst p) - fst (fst p) y, snd p))
     (set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]))
     (set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]))"
      unfolding bij_betw_def inj_on_def image_def
    proof
      show "\<forall>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]).
       \<forall>ya\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]).
          (snd (fst x) - fst (fst x) y, snd x) = (snd (fst ya) - fst (fst ya) y, snd ya) \<longrightarrow> x = ya"
      proof clarify
        fix a b ba aa bb bc
        assume H1:"((a, b), ba) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)])" and
               H2:"((aa, bb), bc) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)])"
        show "snd (fst ((a, b), ba)) - fst (fst ((a, b), ba)) y = snd (fst ((aa, bb), bc)) - fst (fst ((aa, bb), bc)) y \<Longrightarrow> snd ((a, b), ba) = snd ((aa, bb), bc) \<Longrightarrow> (a, b) = (aa, bb) \<and> ba = bc"
        using H1 H2 assms unfolding in_set_zip
        by auto
    qed
    next 
      show "{ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)} 
            = set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)])"
        unfolding image_def
      proof 
        show " {ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)}
               \<subseteq> set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)])"
        proof clarify
          fix a b c
          assume H:"((a, b), c) \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)])"
          show "(snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y, snd ((a, b), c)) \<in> set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)])"
            unfolding in_set_zip
          proof
            let ?n = "nat c - length ra - 1"
            have n1:"0\<le> ?n"
              using H set_zip_rightD by simp
            have n2:"?n < length rc"
              using H set_zip_rightD assms by fastforce
            have c1:"length ra + 1\<le> c"
              using H unfolding in_set_zip by auto
            have c2:"nat c < length cs"
              using H unfolding in_set_zip by auto
            have n:"\<And>n.  n < length [1 + int (length ra)..int (length cs - Suc 0)] \<Longrightarrow> (c = [1 + int (length ra)..int (length cs - Suc 0)] ! n) \<Longrightarrow> n = ?n"
              using n1 n2 assms by simp
            have ab:"(a,b) = (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) ! ?n"
              using H unfolding in_set_zip n1 n2 apply simp
              apply(rewrite nth_zip)
              using n1 n2 assms apply simp_all
              using n by auto
            have a:"a = (map (\<lambda>h p. real_of_int (h p)) cs) ! (nat c)"
            proof -
              have "a = (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) ! ?n"
                using nth_zip[of "?n" "(map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs))" _ ] assms n1 n2 ab by simp 
              also have "(map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) ! (nat c - length ra -1) = (map (\<lambda>h p. real_of_int (h p)) cs) ! (nat c)"
                apply(rewrite nth_map)
                using n1 n2 assms apply(simp)
                apply(rewrite nth_drop, simp add:assms)
                apply(rewrite nth_map)
                using n1 n2 assms apply(simp)
                using H set_zip_rightD by fastforce
              finally show ?thesis by simp
            qed
            have b:"b= (rc ! (nat c - length ra -1))+ ((cs ! nat c) y)"
            proof-
              have "b = (map (real_of_int \<circ> (\<lambda>p. fst p + snd p)) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) ! ?n"
                using ab nth_zip[of "nat c -length ra-1"] assms n1 n2 by simp 
              also have "... = (rc ! (nat c - length ra -1))+ ((cs ! nat c) y)"
                apply(rewrite nth_map)
                using assms n1 n2 apply(simp)
                apply(rewrite nth_zip)
                using assms n1 n2 c1 by simp_all
              finally show ?thesis by simp
            qed
            have p:"b- a y = rc ! ?n"
              by(rewrite a, rewrite b, rewrite nth_map,simp_all add:c1 c2)
            then have "map real_of_int rc ! ?n = fst (snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y, snd ((a, b), c))" 
              apply simp
              apply(rewrite nth_map)
              using n2 by simp_all
            then show "map real_of_int rc ! ?n = fst (snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y, snd ((a, b), c)) \<and>
                       [int (length ra + 1)..int (length cs - 1)] ! ?n = snd (snd (fst ((a, b), c)) - fst (fst ((a, b), c)) y, snd ((a, b), c)) 
                        \<and> ?n < length (map real_of_int rc) 
                        \<and> ?n < length [int (length ra + 1)..int (length cs - 1)]"
              using n1 n2 c1 assms by simp
          qed
        qed
      next
        show "set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)])
               \<subseteq> {ya. \<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]). ya = (snd (fst x) - fst (fst x) y, snd x)}"
        proof clarify
          fix r i
          assume H:"(r, i) \<in> set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)])"
          show "\<exists>x\<in>set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)]).
                (r, i) = (snd (fst x) - fst (fst x) y, snd x)"
          proof
            let ?n = "nat i - length ra -1"
            let ?x = "(((map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) ! ?n, (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))! ?n),i)"
            have i1:"1+length ra \<le> nat i"
              using H set_zip_rightD by fastforce
            have i2:"nat i \<le> length cs - 1"
              using H set_zip_rightD by fastforce
            have i:"i = [1+int (length ra) ..int(length cs - 1)] ! ?n"
              using H i1 i2 unfolding in_set_zip by simp
            have r:"r = rc ! ?n"
              using H i i1 i2 unfolding in_set_zip by fastforce
            show "(r,i) = (snd (fst ?x) - fst (fst ?x) y, snd ?x)"
              unfolding fst_conv snd_conv using r apply simp
              apply(rewrite nth_map)
              using i1 i2 assms apply simp
              apply(rewrite nth_map)
              using i1 i2 assms apply simp
              apply(rewrite nth_zip)
              using i1 i2 assms by simp_all
            show "?x \<in> set (zip (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) [int (length ra + 1)..int (length cs - 1)])"
              unfolding in_set_zip fst_conv snd_conv
            proof
              have "zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) ! ?n =
                   (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs) ! (nat i - length ra - 1), map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) ! (nat i - length ra - 1))"
                apply(rewrite nth_zip)
                using i1 i2 assms by simp_all
              then show "zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) ! ?n =
                   (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs) ! (nat i - length ra - 1), map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) ! (nat i - length ra - 1)) 
                 \<and> [int (length ra + 1)..int (length cs - 1)] ! ?n = i 
                 \<and> ?n < length (zip (map (\<lambda>h p. real_of_int (h p)) (drop (Suc (length ra)) cs)) (map real_of_int (map (\<lambda>p. fst p + snd p) (zip rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))) 
                 \<and> ?n < length [int (length ra + 1)..int (length cs - 1)]"
                using i1 i2 assms apply simp
                using i by simp
            qed
          qed
        qed
      qed
    qed
    show "(\<Prod>p\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2)) =
    (\<Prod>p\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>fst p\<bar>) / real epsilon2))"
      by simp
  qed
  have 3:"(\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (take (length ra) cs)) (map real_of_int (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))))) [0..int (length ra - 1)]). exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>{((\<lambda>x. real_of_int ((cs ! length ra) x), real_of_int (rb + (cs ! length ra) y)), int (length ra))}. exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2)) *
    (\<Prod>((c, z), i)\<in>set (zip (zip (map (\<lambda>h x. real_of_int (h x)) (drop (Suc (length ra)) cs)) (map real_of_int (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))) [int (length ra + 1)..int (length cs - 1)]).
       exp (- (real epsilon1 * \<bar>z - c y\<bar>) / real epsilon2))
        = (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)) * exp (- (real epsilon1 * \<bar>rb\<bar>) / real epsilon2) *
    (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))"
    by(rewrite ra, rewrite rc,auto)
  show ?thesis
    by(rewrite 1,rewrite 2,rewrite 3,simp)
qed


lemma pointwise_pure_dp_inequality_report_noisy_max:
  assumes "is_count_queries cs" and "(x,y)\<in>adj"
and "n = length cs" and "1\<le>epsilon1" and "1\<le>epsilon2"
shows "\<And>z. spmf (report_noisy_max cs epsilon1 epsilon2 x) z
          \<le> exp(epsilon1/epsilon2) * spmf (report_noisy_max cs epsilon1 epsilon2 y) z"
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
        assume z:"z<length cs"
        have x:"ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 x) z) 
              = (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
                  \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
                    ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))"
          using assms ennreal_spmf_report_noisy_max_simps[of "cs" "epsilon1" "epsilon2"  "z" "x"] True
          by linarith
        have y:"ennreal (spmf (report_noisy_max cs epsilon1 epsilon2 y) z)
            =  (\<Sum>\<^sup>+ (ra, rc)\<in>{(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)}.
   \<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
     ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
          using assms ennreal_spmf_report_noisy_max_simps[of "cs" "epsilon1" "epsilon2"  "z" "y"] True
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
        proof(rewrite x, rewrite exp_y,rule nn_integral_mono,clarify)
          fix ra rc::"int list"
          assume "(ra, rc)\<in>space (count_space {(ra, rc). length ra = z \<and> length rc = length cs - (z + 1)})"
          then have  H1:"z = length ra" and H2:"length rc = length cs - Suc(length ra)"
            by simp_all
          show "(\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))
           \<le> (\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
                 ennreal (exp (real epsilon1 / real epsilon2)) * ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))"
          proof -
            have lhs:"(\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs))))}.
              ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 x) (map2 (+) ra (take z (map (\<lambda>q. q x) cs)) @ (rb + (cs ! z) x) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q x) cs)))))
              = ennreal (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs * (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              unfolding H1
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
            have rhs:"(\<Sum>\<^sup>+ rb\<in>{rb. z = snd (argmax_int_list (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs))))}.
          ennreal (exp (real epsilon1 / real epsilon2)) * ennreal (spmf (discrete_laplace_noise_add_list cs epsilon1 epsilon2 y) (map2 (+) ra (take z (map (\<lambda>q. q y) cs)) @ (rb + (cs ! z) y) # map2 (+) rc (drop (Suc z) (map (\<lambda>q. q y) cs)))))
                = ennreal (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs * (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. 
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              unfolding H1
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
            proof(cases "length cs = 1")
              case True
              show ?thesis
              proof -
                have ra:"ra = []" using True H1 H2 z by simp
                have rc:"rc = []" using True H2 by simp
                have "(\<Sum>\<^sup>+ x\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))
                    = (\<Sum>\<^sup>+ x\<in>{rb. True}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))"
                  using ra rc by simp
                also have "... \<le>  (\<Sum>\<^sup>+ rb\<in>{rb. True}. (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
                  by(rule nn_integral_mono, auto)
                also have "... = (\<Sum>\<^sup>+ x\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. ennreal (exp (real epsilon1 / real epsilon2) * exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))"
                  using ra rc by simp
                finally show ?thesis by simp
              qed
            next
              case False
              assume cs_gt1:"length cs \<noteq> 1"
              show ?thesis
              proof -
                let ?p = "\<lambda>rb x. (\<forall>k<length ra. (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! k < (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra)"
                have "(\<Sum>\<^sup>+ x\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))
                    = (\<Sum>\<^sup>+ x\<in>{rb. rb\<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! (length ra)) x \<and> ?p rb x}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))"
                proof -
                  have "{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}
                      = {rb. rb\<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! (length ra)) x \<and> ?p rb x}"
                  proof -
                    have "\<And>rb. (length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))))
                                = (Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! length ra) x \<le> rb \<and> ?p rb x)"
                    proof -
                      fix rb
                      have "(length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))))
                          = ((map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! (length ra) = Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) \<and> ?p rb x)"
                        using argmax_int_list_snd[of "(map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))"]
                        by simp
                      also have "... = (rb\<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! (length ra)) x \<and> ?p rb x)"
                      proof -
                        have "(map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra = Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))
                            = (rb\<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! (length ra)) x)"
                        proof -
                          have p:"(map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra = rb + (cs ! length ra)x"
                          proof -
                            have "length (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) = length ra"
                              apply(rewrite length_map,rewrite length_zip,rewrite length_take,rewrite length_map)
                              using H1 z by linarith
                            then show ?thesis
                              using nth_append_length by(rule subst)
                          qed
                          show ?thesis
                            apply(rewrite p)
                            apply(rewrite set_append, rewrite set_simps)
                            apply(simp,rewrite Max_insert,auto)
                            using H1 H2 z False by auto
                        qed
                        then show ?thesis by simp
                      qed
                      finally show "(length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))))
                                = (Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) - (cs ! length ra) x \<le> rb \<and> ?p rb x)"
                        by simp
                    qed
                    then show ?thesis by simp
                  qed 
                  then show ?thesis by simp
                qed
                also have "... \<le> (\<Sum>\<^sup>+ x\<in>{rb. rb \<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y -  1 \<and> ?p (rb+1) y}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))"            
                proof-
                  have p:"(\<exists>i. i < length ra) \<or> (\<exists>i. i < length rc)"    
                    using cs cs_gt1 H2 
                    by presburger
                  have set1:"set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))
                            =  {ra ! i + (cs ! i) y|i. i < length ra} 
                            \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}"  
                    unfolding set_map set_zip length_take length_drop length_map
                  proof -
                    have 1:"(\<lambda>(x, y). x + y) ` {(ra ! i, take (length ra) (map (\<lambda>q. q y) cs) ! i) |i. i < min (length ra) (min (length cs) (length ra))}
                          = {ra ! i + (cs ! i) y |i. i < length ra}"
                      apply(rewrite min_absorb1)
                      using H1 z by force+           
                    have 2:"(\<lambda>(x, y). x + y) ` {(rc ! i, drop (Suc (length ra)) (map (\<lambda>q. q y) cs) ! i) |i. i < min (length rc) (length cs - Suc (length ra))}
                          = {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}"
                      apply(rewrite min_absorb1)                     
                      using H2 by force+
                    show "(\<lambda>(x, y). x + y) ` {(ra ! i, take (length ra) (map (\<lambda>q. q y) cs) ! i) |i. i < min (length ra) (min (length cs) (length ra))}
                        \<union> (\<lambda>(x, y). x + y) ` {(rc ! i, drop (Suc (length ra)) (map (\<lambda>q. q y) cs) ! i) |i. i < min (length rc) (length cs - Suc (length ra))} 
                        = {ra ! i + (cs ! i) y|i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}"
                      using 1 2 by simp  
                  qed
                  have set2:"set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))
                            =  {ra ! i + (cs ! i) x |i. i < length ra} 
                            \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}"  
                    unfolding set_map set_zip length_take length_drop length_map
                  proof -
                    have 1:"(\<lambda>(x, y). x + y) ` {(ra ! i, take (length ra) (map (\<lambda>q. q x) cs) ! i) |i. i < min (length ra) (min (length cs) (length ra))}
                          = {ra ! i + (cs ! i) x |i. i < length ra}"
                      apply(rewrite min_absorb1)
                      using H1 z by force+           
                    have 2:"(\<lambda>(x, y). x + y) ` {(rc ! i, drop (Suc (length ra)) (map (\<lambda>q. q x) cs) ! i) |i. i < min (length rc) (length cs - Suc (length ra))}
                          = {rc ! i + (cs ! (Suc (length ra) + i)) x  |i. i < length rc}"
                      apply(rewrite min_absorb1)                     
                      using H2 by force+
                    show "(\<lambda>(x, y). x + y) ` {(ra ! i, take (length ra) (map (\<lambda>q. q x) cs) ! i) |i. i < min (length ra) (min (length cs) (length ra))}
                        \<union> (\<lambda>(x, y). x + y) ` {(rc ! i, drop (Suc (length ra)) (map (\<lambda>q. q x) cs) ! i) |i. i < min (length rc) (length cs - Suc (length ra))} 
                        = {ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x  |i. i < length rc}"
                      using 1 2 by simp  
                  qed
                  have 1:"Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y -1
                           \<le> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs)))) -  (cs ! (length ra)) x"
                  proof(cases "length x < length y")
                    case True
                    show ?thesis
                    proof(rewrite set1,rewrite set2)
                      have 1:"Max ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc})- 1
                           \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})"
                      proof(rewrite hom_Max_commute[of "\<lambda>x. x-1"])
                        show "\<And>x y::int. max x y - 1 = max (x - 1) (y - 1)" by simp
                        show  "finite ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc})" by simp
                        show  "{ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc} \<noteq> {}" by (simp add: p)
                        show "(MAX x\<in>{ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}. x - 1) \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})"
                        proof(rewrite image_Un, rewrite Max_le_iff)
                          show "finite ((\<lambda>x. x - 1) ` {ra ! i + (cs ! i) y |i. i < length ra} \<union> (\<lambda>x. x - 1) ` {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc})" by simp
                          show "(\<lambda>x. x - 1) ` {ra ! i + (cs ! i) y |i. i < length ra} \<union> (\<lambda>x. x - 1) ` {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc} \<noteq> {}" by (simp add:p)
                          show "\<forall>a\<in>(\<lambda>x. x - 1) ` {ra ! i + (cs ! i) y |i. i < length ra} \<union> (\<lambda>x. x - 1) ` {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}. a \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})"
                          proof(rewrite Max_ge_iff)
                            show "finite ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})" by simp
                            show " \<And>xa. {ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc} \<noteq> {}" by (simp add:p)
                            show "\<forall>a\<in>(\<lambda>x. x - 1) ` {ra ! i + (cs ! i) y |i. i < length ra} \<union> (\<lambda>x. x - 1) ` {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}. \<exists>aa\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. a \<le> aa"
                            proof safe
                              fix i
                              assume H:"i < length ra"
                              have "ra ! i + (cs ! i) y - 1 \<le> ra ! i + (cs ! i) x"
                                using True H count_queries_1'[of "x" "y" "cs"] assms(1) assms(2) H1 z unfolding adj_def by simp
                              then show "\<exists>a\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. ra ! i + (cs ! i) y - 1 \<le> a"
                                using H by blast
                            next
                              fix i
                              assume H:"i < length rc"
                              have "rc ! i + (cs ! (Suc (length ra) + i)) y - 1 \<le> rc ! i + (cs ! (Suc (length ra) + i)) x"
                                using True H count_queries_1'[of "x" "y" "cs"] assms(1) assms(2) H2 unfolding adj_def by simp
                              then show "\<exists>a\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. rc ! i + (cs ! (Suc (length ra) + i)) y - 1 \<le> a"
                                using H by blast
                            qed
                          qed
                        qed
                      qed
                      have 2:"(cs ! length ra) x \<le> (cs ! length ra) y"
                      proof -
                        have "(cs ! length ra)\<in> set cs"
                          using nth_mem[of "length ra" "cs"] H1 z by simp
                        then show ?thesis
                          using count_queries_1 assms(1) assms(2) True unfolding adj_def by fastforce
                      qed
                      show "Max ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}) - (cs ! length ra) y - 1
                          \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}) - (cs ! length ra) x"
                        using 1 2 by simp
                    qed
                  next
                    case False
                    then show ?thesis
                    proof(rewrite set1,rewrite set2)
                      have 1:"Max ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc})
                           \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})"
                      proof(rewrite Max_le_iff)
                        show "finite ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc})" by simp
                        show "{ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc} \<noteq> {}" using p by simp
                        show "\<forall>a\<in>{ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}. a \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})"
                        proof(rewrite Max_ge_iff)
                          show "finite ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc})" by simp
                          show "{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc} \<noteq> {}" using p by simp
                          show "\<forall>a\<in>{ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}. \<exists>aa\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. a \<le> aa"
                          proof safe
                            fix i
                            assume H:"i < length ra"
                            have "ra ! i + (cs ! i) y \<le> ra ! i + (cs ! i) x"
                              using False H count_queries_2'[of "x" "y" "cs"] assms(1) assms(2) H1 z unfolding adj_def by simp
                            then show "\<exists>a\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. ra ! i + (cs ! i) y \<le> a"
                              using H by blast
                          next
                            fix i
                            assume H:"i < length rc"
                            have "rc ! i + (cs ! (Suc (length ra) + i)) y \<le> rc ! i + (cs ! (Suc (length ra) + i)) x "
                              using False H count_queries_2'[of "x" "y" "cs"] assms(1) assms(2) H2 unfolding adj_def by simp
                            then show "\<exists>a\<in>{ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}. rc ! i + (cs ! (Suc (length ra) + i)) y \<le> a"
                              using H by blast
                          qed
                        qed
                      qed
                      have 2:"(cs ! length ra) x - 1 \<le> (cs ! length ra) y"
                      proof -
                        have "(cs ! length ra)\<in> set cs"
                          using nth_mem[of "length ra" "cs"] H1 z by simp
                        then show ?thesis
                          using count_queries_2 assms(1) assms(2) False unfolding adj_def by fastforce
                      qed
                      show "Max ({ra ! i + (cs ! i) y |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) y |i. i < length rc}) - (cs ! length ra) y - 1
                         \<le> Max ({ra ! i + (cs ! i) x |i. i < length ra} \<union> {rc ! i + (cs ! (Suc (length ra) + i)) x |i. i < length rc}) - (cs ! length ra) x"
                        using 1 2 by simp
                    qed
                  qed
                  have 2:"\<And>rb. ?p rb x \<Longrightarrow> ?p (rb+1) y"
                  proof(safe)
                    fix rb k
                    assume k:"k<length ra"
                      and H:"\<forall>k<length ra. (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! k
                                       < (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra"
                    have k1:"k < length cs"
                      using k H1 z by simp
                    have ra:"\<And>d. length (map2 (+) ra (take (length ra) (map (\<lambda>q. q d) cs))) = length ra"
                      apply(rewrite length_map,rewrite length_zip,rewrite length_take,rewrite length_map)
                      using H1 z by simp
                    have 1:"\<And>d r. (map2 (+) ra (take (length ra) (map (\<lambda>q. q d) cs)) @ (r + (cs ! length ra) d) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q d) cs))) ! k = ra ! k + (cs ! k) d"
                    proof -
                      fix d r 
                      show "(map2 (+) ra (take (length ra) (map (\<lambda>q. q d) cs)) @ (r + (cs ! length ra) d) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q d) cs))) ! k = ra ! k + (cs ! k) d"
                        apply(rewrite nth_append,rewrite ra)
                        using H1 z k by simp_all
                    qed
                    have 2:"\<And>d r. (map2 (+) ra (take (length ra) (map (\<lambda>q. q d) cs)) @ (r + (cs ! length ra) d) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q d) cs))) ! length ra = r + (cs ! length ra) d"
                      using nth_append_length ra by metis
                    show "(map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! k
                        < (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra"
                    proof(cases "length x < length y")
                      case True
                      show ?thesis
                      proof -
                        have t1:"ra ! k + (cs ! k) y \<le> ra ! k + (cs ! k) x + 1"
                          using k1 assms(1) assms(2) True count_queries_1'[of "x" "y" "cs"] unfolding adj_def by fastforce
                        have t2:"(cs ! length ra) x \<le> (cs ! length ra) y"
                          using H1 z assms(1) assms(2) True count_queries_1'[of "x" "y" "cs"] unfolding adj_def by fastforce
                        have "(map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! k
                             \<le> (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! k + 1"
                          using t1 by(rewrite 1)+ simp
                        also have "... < (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra + 1"
                          using H k by auto
                        also have "... \<le> (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra"
                          using t2 by(rewrite 2)+ simp 
                        finally show ?thesis by simp
                      qed
                    next
                      case False
                      show ?thesis
                      proof -
                        have f1:"ra ! k + (cs ! k) y \<le> ra ! k + (cs ! k) x"
                          using k1 assms(1) assms(2) False count_queries_2'[of "x" "y" "cs"] unfolding adj_def by fastforce
                        have f2:"(cs ! length ra) x \<le> (cs ! length ra) y + 1"
                          using H1 z assms(1) assms(2) False count_queries_2'[of "x" "y" "cs"] unfolding adj_def by fastforce
                        have "(map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! k
                             \<le> (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! k"
                          using f1 by(rewrite 1)+ simp
                        also have "... < (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))) ! length ra"
                          using H k by auto
                        also have "... \<le> (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + 1 + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra"
                          using f2 by(rewrite 2)+ simp 
                        finally show ?thesis by simp
                      qed
                    qed
                  qed
                  show ?thesis
                    apply(rewrite restrict_count_space_subset[symmetric, of _ "UNIV"])
                     apply auto[1]
                    apply(rewrite restrict_count_space_subset[symmetric, of "{rb. rb \<ge> Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y -  1 \<and> ?p (rb+1) y}" "UNIV"])
                     apply auto[1]
                    apply(rewrite nn_integral_restrict_space)
                     apply auto[1]
                    apply(rewrite nn_integral_restrict_space)
                     apply auto[1]
                    apply(rewrite nn_set_integral_set_mono)
                    using 1 2 by auto
                qed
                also have "... = (\<Sum>\<^sup>+ x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y \<le> rb \<and> ?p rb y}. ennreal (exp (- (real epsilon1 * real_of_int \<bar>x-1\<bar>) / real epsilon2)))"
                proof(rule nn_integral_bij_count_space[symmetric, of "\<lambda>x. x-1" "{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y \<le> rb \<and> ?p rb y}"])
                  show "bij_betw (\<lambda>x. x - 1)
                        {rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}
                        {rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y - 1 \<le> rb \<and> ?p (rb+1) y}"
                    unfolding bij_betw_def inj_on_def image_def 
                  proof
                    show "\<forall>x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}.
                      \<forall>y\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}. x - 1 = y - 1 \<longrightarrow> x = y" 
                      by simp
                    show "{ya. \<exists>x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}. ya = x - 1} =
                          {rb.  Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y - 1 \<le> rb \<and> ?p (rb+1) y}"
                    proof
                      show "{ya. \<exists>x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}. ya = x - 1}
                          \<subseteq> {rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y - 1 \<le> rb \<and> ?p (rb+1) y}"
                        by auto
                      show "{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y - 1 \<le> rb \<and> ?p (rb+1) y}
                          \<subseteq> {ya. \<exists>x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}. ya = x - 1}"
                      proof clarify
                        fix rb
                        assume H1:"Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y - 1 \<le> rb" and
                               H2:"?p (rb+1) y"
                        show "\<exists>rb'\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}. rb = rb' - 1"
                        proof
                          show "rb = rb+1 - 1" by simp
                          show "rb+1\<in> {rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! length ra) y \<le> rb \<and> ?p rb y}"
                            using H1 H2 by simp
                        qed
                      qed
                    qed
                  qed
                qed             
                also have "... \<le> (\<Sum>\<^sup>+ x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y \<le> rb \<and> ?p rb y}. ennreal (exp (- (real epsilon1 * (real_of_int \<bar>x\<bar>-1)) / real epsilon2)))"
                proof(rewrite nn_integral_mono)
                  fix x                  
                  have "\<bar>real_of_int x\<bar> - 1 \<le> \<bar>real_of_int x -1\<bar>"
                    by simp                    
                  then show "ennreal (exp (- (real epsilon1 * real_of_int \<bar>x - 1\<bar>) / real epsilon2)) \<le> ennreal (exp (- (real epsilon1 * (real_of_int \<bar>x\<bar> - 1)) / real epsilon2))"
                    using assms                    
                    by (simp add: divide_right_mono)
                  show "True" by simp
                qed                
                also have "... = (\<Sum>\<^sup>+ x\<in>{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) - (cs ! (length ra)) y \<le> rb \<and> ?p rb y}.
                                      ennreal (exp (real epsilon1 / real epsilon2) * exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2)))"
                proof-                
                  have "\<And>x. ennreal (exp (- (real epsilon1 * (real_of_int \<bar>x\<bar> - 1)) / real epsilon2)) = ennreal (exp (real epsilon1 / real epsilon2) * exp (- (real epsilon1 * real_of_int \<bar>x\<bar>) / real epsilon2))"                  
                    apply(rewrite ring_class.right_diff_distrib,rewrite mult_exp_exp,rewrite group_add_class.minus_diff_eq)
                    by(rewrite division_ring_class.diff_divide_distrib, auto)                    
                  then show ?thesis                  
                    using nn_integral_cong by simp                 
                qed                
                also have "... = (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}.
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
                proof-
                  have "{rb. Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y  \<le> rb \<and> ?p rb y} 
                      = {rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}"
                  proof -
                    have "\<And>rb. (Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y  \<le> rb \<and> ?p rb y)
                              = (length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))"
                    proof -
                      fix rb
                      have "(length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))
                          = ((map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra =
                              Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))) \<and> ?p rb y)"
                        using argmax_int_list_snd[of "(map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))"]
                        by simp
                      also have "... = (Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y  \<le> rb \<and> ?p rb y)"
                      proof-
                        have "((map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra = Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))
                            = (Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y  \<le> rb)"
                        proof-
                          have p:"(map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))) ! length ra = rb + (cs ! length ra)y"
                          proof -
                            have "length (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) = length ra"
                              apply(rewrite length_map,rewrite length_zip,rewrite length_take,rewrite length_map)
                              using H1 z by linarith
                            then show ?thesis
                              using nth_append_length by(rule subst)
                          qed
                          show ?thesis
                            apply(rewrite p)
                            apply(rewrite set_append, rewrite set_simps)
                            apply(simp,rewrite Max_insert,auto)
                            using H1 H2 z False by auto
                        qed
                        then show ?thesis by simp
                      qed
                      finally show "(Max (set (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs))) \<union> set (map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))- (cs ! (length ra)) y  \<le> rb \<and> ?p rb y)
                              = (length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs)))))" by simp
                    qed
                    then show ?thesis by simp
                  qed
                  then show ?thesis by simp
                qed
                finally show ?thesis by simp
              qed
            qed
            have 4:"ennreal (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs * (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q x) cs)) @ (rb + (cs ! length ra) x) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q x) cs))))}. exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))
              \<le> ennreal (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs  * (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))
                * (\<Sum>\<^sup>+ rb\<in>{rb. length ra = snd (argmax_int_list (map2 (+) ra (take (length ra) (map (\<lambda>q. q y) cs)) @ (rb + (cs ! length ra) y) # map2 (+) rc (drop (Suc (length ra)) (map (\<lambda>q. q y) cs))))}. 
                   (exp (real epsilon1 / real epsilon2)) * exp (- (real epsilon1 * real_of_int \<bar>rb\<bar>) / real epsilon2))"
              using 3 ordered_semiring_class.mult_left_mono[of _ _ "ennreal (((exp (real epsilon1 / real epsilon2) - 1) / (exp (real epsilon1 / real epsilon2) + 1)) ^ length cs * (\<Prod>(r, i)\<in>set (zip (map real_of_int ra) [0..int (length ra) - 1]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2))
                * (\<Prod>(r, i)\<in>set (zip (map real_of_int rc) [int (length ra + 1)..int (length cs - 1)]). exp (- (real epsilon1 * \<bar>r\<bar>) / real epsilon2)))"]
              by simp
            show ?thesis using lhs rhs 4 by simp
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
