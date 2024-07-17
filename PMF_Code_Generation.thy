theory PMF_Code_Generation
  imports "HOL-Probability.Probability"
begin
definition uniform_pmf :: "nat \<Rightarrow> nat pmf" where
  "uniform_pmf n = pmf_of_set {1..n}"

value "uniform_pmf 3"



export_code uniform_pmf in Scala module_name PMFExample
end