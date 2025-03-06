section \<open>Bernoulli distribution that take rational n/d as parameter\<close>

theory Bernoulli_rat
  imports "HOL-Probability.Probability"
          "Probabilistic_While.While_SPMF"
          "Probabilistic_While.Fast_Dice_Roll"
begin

subsection \<open>Define bernoulli_rat\<close>

definition bernoulli_rat :: "nat \<Rightarrow> nat \<Rightarrow> bool spmf" where
"bernoulli_rat n d = 
  (if d=0 then return_spmf False
   else do {
            x \<leftarrow> fast_uniform d;
            return_spmf (x<n)
})"

subsection \<open>Properties of bernoulli_rat\<close>

lemma pmf_bernoulli_rat_None: "pmf (bernoulli_rat n d) None = 0"
proof (cases "d=0")
  case True 
  then show ?thesis by(simp add: bernoulli_rat_def)
next
  case False 
  show ?thesis using False
    apply(simp add: bernoulli_rat_def)
    apply(simp add: fast_uniform_conv_uniform)
  proof -
    show "pmf (spmf_of_set {..<d} \<bind> (\<lambda>x. return_spmf (x < n))) None = 0"
      apply(rewrite spmf_of_pmf_pmf_of_set[symmetric])
        apply simp
      using False apply blast
      using lossless_iff_pmf_None by fastforce
  qed
qed

lemma lossless_bernoulli_rat [simp]: "lossless_spmf (bernoulli_rat n d)"
  by(simp add: lossless_iff_pmf_None pmf_bernoulli_rat_None)

lemma bernoulli_rat_True[simp]: 
  assumes "n/d\<le>1"
  shows  "spmf (bernoulli_rat n d) True = n/d" 
proof (cases "d=0")
  case True
  then show ?thesis by(simp add: bernoulli_rat_def)
next
  case False
  then show ?thesis using assms
    apply(simp add: bernoulli_rat_def)
    apply(simp add: fast_uniform_conv_uniform)
    apply(simp add: spmf_bind)
    apply(simp add: integral_spmf_of_set)
    apply(simp add: indicator_def)
    by (metis card_lessThan inf.absorb_iff2 lessThan_def lessThan_subset_iff)   
qed

lemma bernoulli_rat_False[simp]: 
  assumes "n/d\<le>1"
  shows "spmf (bernoulli_rat n d) False = 1-n/d"
proof -
  show ?thesis using bernoulli_rat_True
    by (simp add: assms spmf_False_conv_True)
qed

lemma bernoulli_rat_pos [simp]:
  assumes "1\<le>n/d"
  shows  "spmf (bernoulli_rat n d) True = 1"
and "spmf (bernoulli_rat n d) False = 0"
proof -
  have "d \<le> n" using assms
    using div_less linorder_not_less by fastforce
  show "spmf (bernoulli_rat n d) True = 1"
    apply(simp add: bernoulli_rat_def)
    apply(simp add: fast_uniform_conv_uniform)
    apply(simp add: spmf_bind)
    apply(simp add: integral_spmf_of_set)
    using assms of_nat_0_less_iff by fastforce
  then show "spmf (bernoulli_rat n d) False = 0"
    by (simp add: assms spmf_False_conv_True)
qed

context begin interpretation pmf_as_function .
lemma bernoulli_rat_eq_bernoulli_pmf:
"bernoulli_rat n d = spmf_of_pmf (bernoulli_pmf (n/d))"
proof -
  have true_eq:"spmf (bernoulli_rat n d) True = pmf (bernoulli_pmf (real n / real d)) True"
  proof (cases "1\<le>n/d")
    case True
    then show ?thesis 
      by (metis bernoulli_eq_bernoulli_pmf bernoulli_pos bernoulli_rat_pos(1) bernoulli_rat_pos(2) pmf_bernoulli_True pmf_le_1 spmf_spmf_of_pmf)
  next
    case False 
    then show ?thesis by simp
  qed
  have false_eq:"spmf (bernoulli_rat n d) False = pmf (bernoulli_pmf (real n / real d)) False" using true_eq 
    apply(simp add: spmf_False_conv_True pmf_False_conv_True)
    done
  have "\<And>i. spmf (bernoulli_rat n d) i = pmf (bernoulli_pmf (real n / real d)) i" using true_eq false_eq
    by (rule bool.induct)
  then show ?thesis 
    by (simp add: spmf_eqI)
qed
end
end