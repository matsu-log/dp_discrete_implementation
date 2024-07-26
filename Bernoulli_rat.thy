theory Bernoulli_rat
  imports "HOL-Probability.Probability"
          "Probabilistic_While.While_SPMF"
          "Probabilistic_While.Fast_Dice_Roll"
begin

definition bernoulli_rat :: "nat \<Rightarrow> nat \<Rightarrow> bool spmf" where
"bernoulli_rat n d = do {
                      x \<leftarrow> fast_uniform d;
                      if x < n then return_spmf True else return_spmf False
}"

lemma pmf_bernoulli_rat_None: "pmf (bernoulli_rat n d) None = 0"
  sorry

lemma lossless_bernoulli_rat [simp]: "lossless_spmf (bernoulli_rat n d)"
  by(simp add: lossless_iff_pmf_None pmf_bernoulli_rat_None)

lemma spmf_if_split:
  "spmf (if b then p else q) x = (if b then spmf p x else spmf q x)"
  by simp

lemma spmf_return_spmf_1: 
  shows "spmf (return_spmf True) True = 1" 
  by simp
lemma spmf_return_spmf_0:
  shows "spmf (return_spmf False) True = 0"
  by (simp)

find_theorems "\<Sum>_\<in>_. if _ then _ else _"
thm "sum.mono_neutral_left"
thm "sum.delta"
thm "sum.union_disjoint"
thm "sum.If_cases"
value "(real 1/real 0)"
value "(real 0/ real 0)"

lemma [simp]: assumes "n/d\<le>1" "d > 0"
  shows bernoulli_rat_True: "spmf (bernoulli_rat n d) True = n/d" (is ?True)
and bernoulli_rat_False: "spmf (bernoulli_rat n d) False = 1 -n/d" (is ?False)
proof -
  show true: "spmf (bernoulli_rat n d) True = n/d" using assms
    apply(simp add: bernoulli_rat_def)
    apply(simp add: fast_uniform_conv_uniform)
    apply(simp add: spmf_bind)
    apply(simp add: integral_spmf_of_set)
    apply(simp add: spmf_if_split)
    apply(rewrite spmf_return_spmf_1)
    apply(rewrite spmf_return_spmf_0)
    apply(simp add: sum.If_cases)
    by (metis card_Collect_less_nat inf.absorb_iff1 inf_commute lessThan_def lessThan_subset_iff)
  show "spmf (bernoulli_rat n d) False = 1-n/d" using true
    by (simp add: spmf_False_conv_True)
qed

lemma bernoulli_rat_pos [simp]:
  assumes "1\<le>n/d"
  shows  "spmf (bernoulli_rat n d) True = 1"
proof -
  have "d \<le> n" using assms
    using div_less linorder_not_less by fastforce
  then show ?thesis
    apply(simp add: bernoulli_rat_def)
    apply(simp add: fast_uniform_conv_uniform)
    apply(simp add: spmf_bind)
    apply(simp add: integral_spmf_of_set)
    using assms of_nat_0_less_iff by fastforce
qed

thm "spmf_eqI"

context begin interpretation pmf_as_function .
lemma bernoulli_rat_eq_bernoulli_pmf:
"bernoulli_rat n d = spmf_of_pmf (bernoulli_pmf (n/d))"
proof -
  have "\<And>i. spmf (bernoulli_rat n d) i = pmf (bernoulli_pmf (real n / real d)) i"
  proof -
    fix i
    have " spmf (bernoulli_rat n d) i = pmf (bernoulli_pmf (real n / real d)) i"
    proof (cases "n/d \<le> 1")
      case True
      then show ?thesis
      proof (cases "i")
        case True
        then show ?thesis
          apply(simp)

  done
end
end