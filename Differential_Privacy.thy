section \<open>Differential Privacy\<close>

theory Differential_Privacy
  imports "HOL-Probability.Probability"
          "IEEE_Floating_Point.Double"
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

subsection \<open>Define pure_dp\<close>

(*
This section is based on SampCert
*)

type_synonym ('a, 'b) query = "'a list \<Rightarrow> 'b"

type_synonym ('a, 'b) mechanism = "'a list \<Rightarrow> 'b spmf"

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

definition is_sensitivity :: "('a, int) query \<Rightarrow> nat \<Rightarrow> bool" where
"is_sensitivity q \<Delta> = (\<forall>l1 l2. neighbour l1 l2 \<longrightarrow> \<bar>q l1 - q l2\<bar>\<le> \<Delta>)"

definition pure_dp_inequality :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> real \<Rightarrow> bool" where
"pure_dp_inequality M N \<epsilon> = (\<forall>A::'a set. measure (measure_spmf M) A \<le> exp( \<epsilon>) * measure (measure_spmf N) A)"

definition pure_dp :: "('a,'b) mechanism \<Rightarrow> real \<Rightarrow> bool" where
"pure_dp M \<epsilon> = (\<forall>l1 l2. neighbour l1 l2 \<longrightarrow> pure_dp_inequality (M l1) (M l2) \<epsilon>)"

definition postprocess :: "('a, 'b) mechanism \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>  'a list \<Rightarrow> 'c spmf" where
"postprocess M pp l = do {
  A \<leftarrow> M l;
  return_spmf (pp A)
}"

subsection \<open>lemmas for pure_dp\<close>

lemma sensitivity:
  assumes "is_sensitivity q \<Delta>"
and "neighbour l1 l2"
shows "\<bar>q l1 - q l2\<bar>\<le> \<Delta>"
  using assms 
  unfolding is_sensitivity_def
  by simp
  
lemma pointwise_spmf_bound_imp_pure_dp:
  fixes M::"('a, int) mechanism"
  assumes "\<And>z l1 l2. neighbour l1 l2 \<Longrightarrow> spmf (M l1)z \<le> exp (\<epsilon>) * spmf (M l2)z"
shows "pure_dp M \<epsilon>"
  unfolding pure_dp_def
proof (rule+)
  fix h1 h2:: "'a list"
  assume neighbour:"neighbour h1 h2"
  show "pure_dp_inequality (M h1) (M h2) \<epsilon>"
    unfolding pure_dp_inequality_def
  proof
    fix A::"int set"
    show "Sigma_Algebra.measure (measure_spmf (M h1)) A \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M h2)) A"
      using measure_spmf_bound[of "M h1" "exp(\<epsilon>)" "M h2"] assms[of "h1" "h2"] neighbour exp_gt_zero
      by blast
  qed
qed
     


lemma dp_postprocess_theorem:
  assumes "pure_dp M \<epsilon>"
  shows "pure_dp (postprocess M pp) \<epsilon>"
  unfolding pure_dp_def
proof (rule+)
  fix l1 l2:: "'a list" 
  assume neighbour:"neighbour l1 l2"
  have p:"pure_dp_inequality (M l1) (M l2) \<epsilon>"
    using assms pure_dp_def[of "M" "\<epsilon>"] neighbour
    by blast
  show "pure_dp_inequality (postprocess M pp l1) (postprocess M pp l2) \<epsilon>"
    unfolding pure_dp_inequality_def postprocess_def 
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
      using p unfolding pure_dp_inequality_def
      by auto
    then show "Sigma_Algebra.measure (measure_spmf (M l1 \<bind> (\<lambda>A. return_spmf (pp A)))) A
         \<le> exp \<epsilon> * Sigma_Algebra.measure (measure_spmf (M l2 \<bind> (\<lambda>A. return_spmf (pp A)))) A"
      using l1 l2 by simp
  qed
qed
 



end