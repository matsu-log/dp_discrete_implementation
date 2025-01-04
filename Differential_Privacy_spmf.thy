section \<open>Differential Privacy\<close>

theory Differential_Privacy_spmf
  imports "HOL-Probability.Probability"
          "Differential_Privacy.Differential_Privacy_Standard"
begin

subsection \<open>Auxiliary Lemmas for pointwise_spmf_bound_imp_pure_dp\<close>

definition int_family :: "nat \<Rightarrow> int set" where
"int_family n = (if even n then {n div 2} else {-((n+1) div 2)})"

lemma disjoint_family_int_family:
"disjoint_family int_family"
  unfolding disjoint_family_on_def UNIV_def
proof(clarify)
  fix m n::nat
  assume mn:"m \<noteq> n"
  show "int_family m \<inter> int_family n = {}"
    unfolding int_family_def 
    using mn
  proof(auto)
    have "even m \<Longrightarrow> even n \<Longrightarrow>int n div 2 \<noteq> int m div 2"
      using mn by fastforce
    then show "even m \<Longrightarrow> even n \<Longrightarrow> int n div 2 = int m div 2 \<Longrightarrow> False"
      by simp
    have "odd m \<Longrightarrow> odd n \<Longrightarrow> int n div 2 \<noteq> int m div 2"
      using mn 
      by (metis bit_eq_rec even_of_nat nat_int_comparison(1))
    then show " odd m \<Longrightarrow> odd n \<Longrightarrow> int n div 2 = int m div 2 \<Longrightarrow> False"
      by simp
  qed
qed

lemma int_family_eq_for_positive:
  assumes "0\<le>x"
  shows "{x} = int_family (nat (2*x))"
  unfolding int_family_def
  using assms
proof(simp)
  have "nat (2* x) = 2 * nat x"
    by simp
  then have "even (nat (2 * x))" 
    by simp
  then show "odd (nat (2 * x)) \<longrightarrow> x = 0"
    by simp
qed 

lemma int_family_eq_for_negative:
  assumes "x<0"
  shows "{x} = int_family (nat(-2*x-1))"
  unfolding int_family_def
  using assms
proof(auto)
  have 1:"\<not> even (nat (-2*x-1))"
  proof -        
    have 1:"nat (-2*x-1) = 2*nat(-x) -1"        
      using assms by simp
    have 2:"\<not> even (2*nat(-x) -1)"        
      using assms by simp
    show ?thesis
      using 1 2 by simp
  qed
  then show "even (nat (- (2 * x) - 1)) \<Longrightarrow> x = (- (2 * x) - 1) div 2"
    by simp
qed

lemma int_family_union:
"\<Union> (range int_family) = UNIV"
proof
  show "\<Union> (range int_family) \<subseteq> UNIV"
    by simp
  show "UNIV \<subseteq> \<Union> (range int_family)"
  proof
    fix x::int
    assume "x \<in> UNIV"
    show "x \<in> \<Union> (range int_family)"
    proof(cases "x<0")
      case True
      show ?thesis
      proof 
        show "nat(-2*x-1) \<in> UNIV"
          by simp
        show "x \<in> int_family (nat(-2*x-1))"
          using int_family_eq_for_negative True
          by auto
      qed
    next
      case False
      show ?thesis
      proof
        show "2*(nat x)\<in> UNIV"
          by simp
        show "x \<in> int_family (2*(nat x))"
          unfolding int_family_def
          using False 
          by simp
      qed
    qed
  qed
qed

thm suminf_emeasure
find_theorems "disjoint_family "

lemma suminf_emeasure_spmf_int_family:
"(\<Sum>i::nat. emeasure (measure_spmf p) (int_family i)) = emeasure (measure_spmf p) (\<Union> (range int_family))"
  apply(rule suminf_emeasure,simp)
  using disjoint_family_int_family by simp

definition int_family_set:: "int set \<Rightarrow> nat \<Rightarrow>int set" where 
"int_family_set A n = (if int_family n \<subseteq> A then int_family n else {})"

lemma disjoint_family_int_family_set:
"disjoint_family (int_family_set A)"
  unfolding int_family_set_def
  using disjoint_family_int_family
  unfolding disjoint_family_on_def
  by simp

lemma int_family_set_union:
"\<Union> (range (int_family_set A)) = A"
proof
  show "\<Union> (range (int_family_set A)) \<subseteq> A"
    unfolding int_family_set_def
    by auto
  show "A \<subseteq> \<Union> (range (int_family_set A))"
    unfolding int_family_set_def
  proof(auto)
    fix x
    assume A:"x\<in>A"
    show "\<exists>xa. int_family xa \<subseteq> A \<and> x \<in> int_family xa "
    proof(cases "x<0")
      case True
      then show ?thesis 
        using A int_family_eq_for_negative[of "x"]
        by auto
    next
      case False
      then show ?thesis
        using A int_family_eq_for_positive[of "x"]
        by auto
    qed
  qed
qed

lemma suminf_emeasure_spmf_int_family_set:
"(\<Sum>i::nat. emeasure (measure_spmf p) (int_family_set A i)) = emeasure (measure_spmf p) A"
proof -
  have "(\<Sum>i::nat. emeasure (measure_spmf p) (int_family_set A i)) = emeasure (measure_spmf p) (\<Union> (range (int_family_set A)))"
  apply(rule suminf_emeasure,simp)
    using disjoint_family_int_family_set by simp
  also have "... = emeasure (measure_spmf p) A"
    using int_family_set_union by simp
  finally show ?thesis by simp
qed

lemma emeasure_spmf_bound:
  fixes A::"int set"
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
and "0<c"
  shows "emeasure (measure_spmf p) A \<le> c * emeasure (measure_spmf q) A"
proof -
  have 1:"emeasure (measure_spmf p) A = (\<Sum>i::nat. emeasure (measure_spmf p) (int_family_set A i))"
    using suminf_emeasure_spmf_int_family_set
    by simp
  have 2:"emeasure (measure_spmf q) A = (\<Sum>i::nat. emeasure (measure_spmf q) (int_family_set A i))"
    using suminf_emeasure_spmf_int_family_set
    by simp
  have 3:"(\<Sum>i::nat. emeasure (measure_spmf p) (int_family_set A i)) \<le>  (\<Sum>i::nat. c *  emeasure (measure_spmf q) (int_family_set A i))"
    apply(rewrite suminf_le,auto)
    unfolding int_family_set_def 
  proof -
    fix n::nat
    show "emeasure (measure_spmf p) (if int_family n \<subseteq> A then int_family n else {}) \<le>  c * emeasure (measure_spmf q) (if int_family n \<subseteq> A then int_family n else {})"
    proof(cases "int_family n \<subseteq> A")
      case True
      then show ?thesis
        apply(simp)
        unfolding int_family_def
        apply(auto)
      proof -
        show "emeasure (measure_spmf p) {int n div 2} \<le> c * emeasure (measure_spmf q) {int n div 2}"
          apply(rewrite emeasure_spmf_single, rewrite emeasure_spmf_single)
        proof -
          have "ennreal c * ennreal (spmf q (int n div 2)) = ennreal (c * (spmf q (int n div 2)))"
            using ennreal_mult' assms by simp
          then show "ennreal (spmf p (int n div 2)) \<le> ennreal c * ennreal (spmf q (int n div 2))"
            using ennreal_leI assms by simp
        qed
        show "emeasure (measure_spmf p) {- (int n div 2) - 1} \<le> c * emeasure (measure_spmf q) {- (int n div 2) - 1}"
          apply(rewrite emeasure_spmf_single, rewrite emeasure_spmf_single)
        proof -
          have "ennreal c * ennreal (spmf q (- (int n div 2) - 1)) = ennreal (c * (spmf q (- (int n div 2) - 1)))"
            using ennreal_mult' assms by simp
          then show "ennreal (spmf p (- (int n div 2) - 1)) \<le> ennreal c * ennreal (spmf q (- (int n div 2) - 1))"
            using ennreal_leI assms by simp
        qed
      qed
    next
      case False
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    using 1 2 3 by auto
qed

lemma measure_spmf_bound: 
  fixes p q:: "int spmf"
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
and "0<c"
  shows "measure (measure_spmf p) A \<le> c * measure (measure_spmf q) A"
proof - 
  have 1:"emeasure (measure_spmf p) A  \<le>  c * emeasure (measure_spmf q) A"
    using emeasure_spmf_bound assms by blast
  have 2:"emeasure (measure_spmf q) A < \<top>"
    using measure_spmf.emeasure_finite[of "q" "A"] less_top 
    by blast
  then show ?thesis 
    unfolding measure_def
    using 1 2 assms
    by (simp add: enn2real_leI ennreal_mult')
qed

definition nat_family:: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
"nat_family A n = (if n\<in>A then {n} else {})"

lemma disjoint_family_nat_family:
"disjoint_family (nat_family A)"
  unfolding nat_family_def
  unfolding disjoint_family_on_def
  by simp

lemma nat_family_union:
"\<Union> (range (nat_family A)) = A"
proof
  show "\<Union> (range (nat_family A)) \<subseteq> A"
    unfolding nat_family_def
    by auto
  show "A \<subseteq> \<Union> (range (nat_family A))"
    unfolding nat_family_def
    by auto
qed

lemma suminf_emeasure_spmf_nat_family:
"(\<Sum>i::nat. emeasure (measure_spmf p) (nat_family A i)) = emeasure (measure_spmf p) A"
proof -
  have "(\<Sum>i::nat. emeasure (measure_spmf p) (nat_family A i)) = emeasure (measure_spmf p) (\<Union> (range (nat_family A)))"
  apply(rule suminf_emeasure,simp)
    using disjoint_family_nat_family by simp
  also have "... = emeasure (measure_spmf p) A"
    using nat_family_union by simp
  finally show ?thesis by simp
qed

lemma emeasure_spmf_bound_nat:
  fixes A::"nat set"
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
and "0<c"
  shows "emeasure (measure_spmf p) A \<le> c * emeasure (measure_spmf q) A"
proof -
  have 1:"emeasure (measure_spmf p) A = (\<Sum>i::nat. emeasure (measure_spmf p) (nat_family A i))"
    using suminf_emeasure_spmf_nat_family
    by simp
  have 2:"emeasure (measure_spmf q) A = (\<Sum>i::nat. emeasure (measure_spmf q) (nat_family A i))"
    using suminf_emeasure_spmf_nat_family
    by simp
  have 3:"(\<Sum>i::nat. emeasure (measure_spmf p) (nat_family A i)) \<le>  (\<Sum>i::nat. c *  emeasure (measure_spmf q) (nat_family A i))"
    apply(rewrite suminf_le,auto)
    unfolding nat_family_def 
  proof -
    fix n::nat
    show "emeasure (measure_spmf p) (if n \<in> A then {n} else {}) \<le> ennreal c * emeasure (measure_spmf q) (if n \<in> A then {n} else {})"
      apply(simp)
      apply(rewrite emeasure_spmf_single, rewrite emeasure_spmf_single)
      apply(auto)
      using assms(1)[of "n"] assms(2) ennreal_mult'[of "c" "spmf q n"] ennreal_leI
      by fastforce
  qed
  show ?thesis
    using 1 2 3 by auto
qed

lemma measure_spmf_bound_nat: 
  fixes p q:: "nat spmf"
  assumes "\<And>z. spmf p z \<le> c * spmf q z"
and "0<c"
  shows "measure (measure_spmf p) A \<le> c * measure (measure_spmf q) A"
proof - 
  have 1:"emeasure (measure_spmf p) A  \<le>  c * emeasure (measure_spmf q) A"
    using emeasure_spmf_bound_nat assms by simp
  have 2:"emeasure (measure_spmf q) A < \<top>"
    using measure_spmf.emeasure_finite[of "q" "A"] less_top 
    by blast
  then show ?thesis 
    unfolding measure_def
    using 1 2 assms
    by (simp add: enn2real_leI ennreal_mult')
qed


subsection \<open>Define pure_dp\<close>

paragraph \<open>type_synonym for query, mechanism.\<close>

text \<open>Regarding lists as datasets\<close>

type_synonym ('a, 'b) query = "'a list \<Rightarrow> 'b"

type_synonym ('a, 'b) mechanism = "'a list \<Rightarrow> 'b spmf"

paragraph \<open>Adjacency of Datasets.\<close>
(*
  Adjacency of two lists has 3 patterns.
    Addition: l2 has an additional element than l1
    Deletion: l2 miss an element than l2
    Update: l2 differs by one element compared to l1
*)
inductive neighbour :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  Addition: "l1 = a @ b \<Longrightarrow> l2= a @ [n] @ b \<Longrightarrow> neighbour l1 l2" |
  Deletion: "l1 = a @ [n] @ b \<Longrightarrow> l2 = a @ b \<Longrightarrow> neighbour l1 l2" |
  Update:   "l1= a @ [n] @ b \<Longrightarrow> l2= a @ [m] @ b \<Longrightarrow> neighbour l1 l2"

definition adj :: "('a list) rel" where
"adj = {(l1,l2). neighbour l1 l2}"

paragraph \<open>Definition of pure differential privacy with adjacency, and its basic properties\<close>

definition pure_dp_inequality :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> real \<Rightarrow> bool" where
"pure_dp_inequality M N \<epsilon> = DP_inequality (measure_spmf M) (measure_spmf N) \<epsilon> 0"

definition pure_dp :: "('a,'b) mechanism \<Rightarrow> real \<Rightarrow> bool" where
"pure_dp M \<epsilon> = differential_privacy (measure_spmf \<circ> M) adj \<epsilon> 0"

definition is_sensitivity :: "('a, int) query \<Rightarrow> nat \<Rightarrow> bool" where
"is_sensitivity q \<Delta> = (\<forall>(l1, l2)\<in>adj. \<bar>q l1 - q l2\<bar>\<le> \<Delta>)"

definition postprocess :: "('a, 'b) mechanism \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>  'a list \<Rightarrow> 'c spmf" where
"postprocess M pp l = do {
  A \<leftarrow> M l;
  return_spmf (pp A)
}"

subsection \<open>lemmas for pure_dp\<close>

lemma adj_sym: "sym adj"
  unfolding adj_def neighbour.simps
  by(auto,rule,blast)

lemma pure_dp_inequality_imp_pure_dp:
  assumes "\<forall>(l1, l2)\<in>adj. pure_dp_inequality (M l1) (M l2) \<epsilon>"
  shows "pure_dp M \<epsilon>"
  unfolding pure_dp_def 
proof(rewrite differential_privacy_adj_sym, simp add: adj_sym)
  show "\<forall>(d1, d2)\<in>adj. DP_inequality ((measure_spmf \<circ> M) d1) ((measure_spmf \<circ> M) d2) \<epsilon> 0"
    using assms 
    unfolding pure_dp_inequality_def o_def
    by auto
qed

lemma sensitivity:
  assumes "is_sensitivity q \<Delta>"
and "(l1, l2)\<in>adj"
shows "\<bar>q l1 - q l2\<bar>\<le> \<Delta>"
  using assms 
  unfolding is_sensitivity_def
  by auto
  
lemma pointwise_spmf_bound_imp_pure_dp:
  fixes M::"('a, int) mechanism"
  assumes "\<And>z l1 l2. (l1, l2)\<in>adj \<Longrightarrow> spmf (M l1)z \<le> exp (\<epsilon>) * spmf (M l2)z"
shows "pure_dp M \<epsilon>"
proof(rule pure_dp_inequality_imp_pure_dp,clarify)
  fix h1 h2:: "'a list"
  assume adj:"(h1, h2)\<in> adj"
  show "pure_dp_inequality (M h1) (M h2) \<epsilon>"
    unfolding pure_dp_inequality_def DP_inequality_def
  proof
    fix A::"int set"
    show "Sigma_Algebra.measure (measure_spmf (M h1)) A \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M h2)) A+0"
      using measure_spmf_bound[of "M h1" "exp(\<epsilon>)" "M h2"] assms[of "h1" "h2"] exp_gt_zero adj
      by simp
  qed
qed

lemma pointwise_spmf_bound_imp_pure_dp_nat:
  fixes M::"('a, nat) mechanism"
  assumes "\<And>z l1 l2. (l1, l2)\<in>adj \<Longrightarrow> spmf (M l1)z \<le> exp (\<epsilon>) * spmf (M l2)z"
shows "pure_dp M \<epsilon>"
proof(rule pure_dp_inequality_imp_pure_dp,clarify)
  fix h1 h2:: "'a list"
  assume adj:"(h1, h2)\<in> adj"
  show "pure_dp_inequality (M h1) (M h2) \<epsilon>"
    unfolding pure_dp_inequality_def DP_inequality_def
  proof
    fix A::"nat set"
    show "Sigma_Algebra.measure (measure_spmf (M h1)) A \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M h2)) A+0"
      using measure_spmf_bound_nat[of "M h1" "exp(\<epsilon>)" "M h2"] assms[of "h1" "h2"] exp_gt_zero adj
      by simp
  qed
qed
                                             
lemma dp_postprocess_theorem:
  assumes "pure_dp M \<epsilon>"
  shows "pure_dp (postprocess M pp) \<epsilon>"
  unfolding pure_dp_def
  apply(rewrite differential_privacy_adj_sym, simp add: adj_sym) 
proof (rule+,auto)
  fix l1 l2:: "'a list" 
  assume adj:"(l1, l2) \<in> adj"
  have p:"DP_inequality (measure_spmf (M l1)) (measure_spmf (M l2)) \<epsilon> 0"
    using assms pure_dp_def[of "M" "\<epsilon>"] adj
    unfolding o_def differential_privacy_def
    by auto
       
  show "DP_inequality (measure_spmf (postprocess M pp l1)) (measure_spmf (postprocess M pp l2)) \<epsilon> 0"
    unfolding DP_inequality_def postprocess_def 
  proof
    fix A
    have l1:"Sigma_Algebra.measure (measure_spmf (M l1 \<bind> (\<lambda>A. return_spmf (pp A)))) A 
        = measure (measure_spmf (map_spmf pp (M l1))) A"
      using map_spmf_conv_bind_spmf by metis
    have l2:"Sigma_Algebra.measure (measure_spmf (M l2 \<bind> (\<lambda>A. return_spmf (pp A)))) A 
        = measure (measure_spmf (map_spmf pp (M l2))) A"
      using map_spmf_conv_bind_spmf by metis
    have "measure (measure_spmf (map_spmf pp (M l1))) A \<le> exp \<epsilon> * measure (measure_spmf (map_spmf pp (M l2))) A"
      apply(rewrite measure_map_spmf)
      apply(rewrite measure_map_spmf)
      using p unfolding DP_inequality_def
      by auto
    then show "Sigma_Algebra.measure (measure_spmf (M l1 \<bind> (\<lambda>A. return_spmf (pp A)))) A 
              \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M l2 \<bind> (\<lambda>A. return_spmf (pp A)))) A + 0"
      using l1 l2 by simp
  qed
qed

lemma lossless_spmf_imp_measurable_as_measure:
  assumes "\<And>x. lossless_spmf (M x)"
  shows "measure_spmf \<circ> M \<in> (count_space UNIV) \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
proof(rewrite measurable_count_space_eq1)
  show "measure_spmf \<circ> M \<in> UNIV \<rightarrow> space (prob_algebra (count_space UNIV))" 
  proof(auto)
    fix x
    have "emeasure (measure_spmf (M x)) (space (measure_spmf (M x))) = 1"
      using assms space_measure_spmf[of "M x"]
      unfolding lossless_spmf_def weight_spmf_def
      by (simp add: measure_spmf.emeasure_eq_measure)
    then have "prob_space (measure_spmf (M x))"
      by rule
    then show "measure_spmf (M x) \<in> space (prob_algebra (count_space UNIV))"
      apply(rewrite space_prob_algebra)
      by(auto)
  qed
qed

lemma prod_measurable:
  fixes N::"'a list \<times>'b \<Rightarrow> 'c spmf"
  assumes "\<And>x y. lossless_spmf (N (x,y))"
and "countable (UNIV:: ('a list) set)"
and "countable (UNIV::'b set)"
  shows "measure_spmf \<circ> N \<in> count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
  unfolding o_def
  apply(rewrite pair_measure_countable)
  using assms 
    apply(auto)
  using lossless_spmf_imp_measurable_as_measure assms
  by force

lemma pure_dp_comp:
  fixes M::"('a, 'b) mechanism" and N::"'a list \<times> 'b \<Rightarrow>'c spmf"
  assumes M:"pure_dp M \<epsilon>"
and N:"\<And>y. pure_dp (\<lambda> x. N (x,y)) \<epsilon>'"
and lossless_M:"\<And>x. lossless_spmf (M x)"
and lossless_N:"\<And>x y. lossless_spmf (N (x,y))"
and "0\<le>\<epsilon>" and "0\<le>\<epsilon>'"
and "countable (UNIV::'a list set)" and "countable (UNIV::'b set)"
shows "pure_dp (\<lambda>x. bind_spmf  (M x) (\<lambda>y. N (x, y))) (\<epsilon>+\<epsilon>')"
  using M N
  unfolding pure_dp_def 
proof -
  have 1:" \<And>y. (\<lambda>x. (measure_spmf \<circ> N) (x, y)) = (measure_spmf \<circ> (\<lambda>x. N (x, y)))"
    unfolding o_def
    by simp                                                                            
  have 2:"(\<lambda>x. (measure_spmf \<circ> M) x \<bind> (\<lambda>y. (measure_spmf \<circ> N) (x, y))) = (measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y))))"
    using measure_spmf_bind
    unfolding o_def
    by metis
  have 3:"measure_spmf \<circ> M \<in> (count_space UNIV) \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using lossless_M lossless_spmf_imp_measurable_as_measure
    by auto
  have 4:"measure_spmf \<circ> N \<in> count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    using assms prod_measurable by blast
  have 5:"differential_privacy (measure_spmf \<circ> M) adj \<epsilon> 0 "
    using M unfolding pure_dp_def by simp
  have 6:"\<forall>y\<in>space (count_space UNIV). differential_privacy (\<lambda>x. (measure_spmf \<circ> N) (x, y)) adj \<epsilon>' 0"
    using N unfolding pure_dp_def 
    by (simp add: o_def)
  have "differential_privacy (\<lambda>x. (measure_spmf \<circ> M) x \<bind> (\<lambda>y. (measure_spmf \<circ> N) (x, y))) adj (\<epsilon> + \<epsilon>') (0 + 0)"
    using differential_privacy_composition_adaptive[of "\<epsilon>" "\<epsilon>'" "measure_spmf \<circ> M" "count_space UNIV" "count_space UNIV" "adj" "0"
                                                   "measure_spmf \<circ> N" "count_space UNIV"]
                                                 3 4 5 6 assms
    by auto
  then show "differential_privacy (measure_spmf \<circ> (\<lambda>x. M x \<bind> (\<lambda>y. N (x, y)))) adj (\<epsilon> + \<epsilon>') 0"
    using 2 by simp
qed
   

      
     

end