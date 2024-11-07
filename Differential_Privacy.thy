section \<open>Differential Privacy\<close>

theory Differential_Privacy
  imports "HOL-Probability.Probability"
begin

definition Pure_DP_inequality :: "'a spmf \<Rightarrow> 'a spmf \<Rightarrow> real \<Rightarrow> bool" where
"Pure_DP_inequality M N \<epsilon> = (\<forall>A::'a set. measure (measure_spmf M) A \<le> exp(\<epsilon>) * measure (measure_spmf N) A)"

definition Pure_DP :: "('a \<Rightarrow> 'b spmf) \<Rightarrow> ('a rel) \<Rightarrow> real \<Rightarrow> bool" where
"Pure_DP M adj \<epsilon> = (\<forall>(d1,d2)\<in>adj. Pure_DP_inequality (M d1) (M d2) \<epsilon>)"


end