theory Code_Generation_mechanism
  imports "Executable_Randomized_Algorithms.Randomized_Algorithm"
          "sampler/Code_Generation_sampler"
          "Discrete_laplace_mechanism"
          "Probabilistic_While.Fast_Dice_Roll"
          "Report_noisy_max"
begin

definition discrete_laplace_mechanism_ra :: "('a list \<Rightarrow> int) \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> int random_alg" where
"discrete_laplace_mechanism_ra f \<Delta> epsilon1 epsilon2 x = 
do { 
  noise \<leftarrow> discrete_laplace_rat_ra (epsilon2 * \<Delta>) epsilon1;
  return_ra (noise + f x)
}"

lemma discrete_laplace_mechanism_ra_correct:
"spmf_of_ra (discrete_laplace_mechanism_ra f \<Delta> epsilon1 epsilon2 x) = discrete_laplace_mechanism f \<Delta> epsilon1 epsilon2 x"
  unfolding discrete_laplace_mechanism_def discrete_laplace_mechanism_ra_def
  by(simp add: spmf_of_ra_simps discrete_laplace_rat_ra_correct)

export_code discrete_laplace_mechanism_ra in OCaml

primrec discrete_laplace_noise_add_list_ra :: "('a list \<Rightarrow> int) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> int list random_alg" where
"discrete_laplace_noise_add_list_ra [] epsilon1 epsilon2  ls = return_ra []"|
"discrete_laplace_noise_add_list_ra (c#cs) epsilon1 epsilon2 ls = 
do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list_ra cs epsilon1 epsilon2 ls;
  noisy_c \<leftarrow> discrete_laplace_mechanism_ra c 1 epsilon1 epsilon2 ls;
  return_ra (noisy_c  # noisy_cs)
}"

lemma discrete_laplace_noise_add_list_ra_correct:
"spmf_of_ra (discrete_laplace_noise_add_list_ra cs epsilon1 epsilon2 ls) = discrete_laplace_noise_add_list cs epsilon1 epsilon2 ls"
proof(induct cs)
  case Nil
  then show ?case
    unfolding discrete_laplace_noise_add_list_ra.simps discrete_laplace_noise_add_list.simps
    by(simp add: spmf_of_ra_simps)
next
  case (Cons a cs)
  show ?case 
    unfolding discrete_laplace_noise_add_list_ra.simps discrete_laplace_noise_add_list.simps
    apply(rewrite spmf_of_ra_bind,rewrite spmf_of_ra_bind)
    apply(rewrite Cons)
    apply(rule bind_spmf_cong,simp)
    by(simp add: spmf_of_ra_simps discrete_laplace_mechanism_ra_correct)
qed

definition report_noisy_max_ra:: "(('a, int) query) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat random_alg" where
"report_noisy_max_ra cs epsilon1 epsilon2 x = do {
  noisy_cs \<leftarrow> discrete_laplace_noise_add_list_ra cs epsilon1 epsilon2 x;
  return_ra (snd (argmax_int_list noisy_cs))
}
"

lemma report_noisy_max_ra_correct:
  shows "spmf_of_ra(report_noisy_max_ra cs epsilon1 epsilon2 x) = report_noisy_max cs epsilon1 epsilon2 x"
  unfolding report_noisy_max_ra_def report_noisy_max_def
  by(simp add: spmf_of_ra_simps discrete_laplace_noise_add_list_ra_correct)

export_code discrete_laplace_mechanism_ra report_noisy_max_ra in Scala

end
