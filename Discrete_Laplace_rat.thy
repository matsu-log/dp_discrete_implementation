theory Discrete_Laplace_rat
  imports "Bernoulli_exp_minus_rat"
          "Probabilistic_While.Fast_Dice_Roll"
          "Bernoulli_rat"
begin

term "fast_uniform 3" 

partial_function (spmf) loop :: "nat \<Rightarrow> nat spmf" where
"loop v = do {
              a \<leftarrow> bernoulli_exp_minus_rat 1 1;
              if a = False then return_spmf v
              else  loop (v+1)
}"


partial_function (spmf) discrete_laplace_rat :: "nat \<Rightarrow> nat \<Rightarrow> int spmf" where
"discrete_laplace_rat t s = bind_spmf 
                              (fast_uniform t) 
                              (\<lambda>u. bind_spmf 
                                      (bernoulli_exp_minus_rat u t)
                                      (\<lambda>d. if \<not>d then (discrete_laplace_rat t s)
                                           else bind_spmf (loop 0) (\<lambda>v. let x = u + t * v in
                                                                        let y = floor (x/s) in 
                                                                        bind_spmf 
                                                                                 (bernoulli_rat 1 2) 
                                                                                 (\<lambda>b. if (\<not>b \<and> (y=0)) then discrete_laplace_rat t s 
                                                                                      else if b then return_spmf (-y) 
                                                                                           else return_spmf y ) )))
"




end