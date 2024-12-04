section \<open>Report Noisy Max with discrete laplace distribution\<close>

theory Report_noisy_max
  imports Discrete_laplace_rat
          Differential_Privacy2
          formalization.Differential_Privacy_Example_Report_Noisy_Max
begin


term ""
term "[]"
term "map (\<lambda>list. map_spmf (f list) noise) list"
term "(\<lambda>list. map_spmf (f list) noise)"


definition report_noisy_max:: "('a, int) query \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> int spmf" where
"report noisy max f epsilon1 epsilon2 x = do {
  
}
"




end
