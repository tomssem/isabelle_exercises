theory Replace
  imports Main
begin

text\<open>
Define a function @{term replace}, such that @{term"replace x y zs"}
yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.\<close>

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "replace _ _ [] = []" |
  "replace x y (z#zs) = (if x = z
                         then (y #(replace x y zs))
                         else (z # (replace x y zs)))"

lemma replace_app:"replace x y (zs1 @ zs2) = replace x y zs1 @ replace x y zs2"
  apply (induction zs1)
  by auto

text \<open>
Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.
\<close>

theorem "rev(replace x y zs) = replace x y (rev zs)"
  apply (induction zs)
  by (auto simp add: replace_app)

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  oops
(*
Found by quickcheck
  x = a\<^sub>1
  y = a\<^sub>2
  u = a\<^sub>2
  v = a\<^sub>1
  zs = [a\<^sub>1]
*)

theorem "replace y z (replace x y zs) = replace x z zs"
  oops
(*
Found by quickcheck
  y = a\<^sub>1
  z = a\<^sub>2
  x = a\<^sub>2
  zs = [a\<^sub>1]
*)

text\<open>Define two functions for removing elements from a list:
@{term"del1 x xs"} deletes the first occurrence (from the left) of
@{term x} in @{term xs}, @{term"delall x xs"} all of them.\<close>

consts del1'   :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
       delall' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"

fun del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"del1 _ []     = []" |
"del1 x (y#ys) = (if x = y
                  then ys
                  else y#del1 x ys)"

value "del1 1 [1, 11, 43, 0] :: nat list"

fun delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"delall _ []     = []" |
"delall x (y#ys) = (if x = y
                    then delall x ys
                    else y#delall x ys)"

lemma delall_app:"delall a (xs @ ys) = delall a xs @ delall a ys"
  apply (induction xs)
  by auto

text\<open>Prove or disprove (by counterexample) the following theorems.\<close>

theorem [simp]:"del1 x (delall x xs) = delall x xs"
  apply (induction xs)
  by (auto simp add: delall_app)

theorem "delall x (delall x xs) = delall x xs"
  apply (induction xs)
  by (auto simp add: delall_app)

theorem "delall x (del1 x xs) = delall x xs"
  apply (induction xs)
  by (auto simp add: delall_app)

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  apply (induction zs)
  by auto

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  apply (induction zs)
   apply simp
  apply simp
  apply (case_tac "y=a")
   apply (case_tac "x=a")
  by (auto simp add: delall_app)

theorem "delall x (delall y zs) = delall y (delall x zs)"
  apply (induction zs)
  by (auto simp add: delall_app)

theorem "del1 y (replace x y xs) = del1 x xs"
(*
Found by quickcheck
  y = a\<^sub>1
  x = a\<^sub>2
  xs = [a\<^sub>1]
*)
  oops

theorem "delall y (replace x y xs) = delall x xs"
(*
Found by quickcheck
  y = a\<^sub>1
  x = a\<^sub>2
  xs = [a\<^sub>1]
*)
  oops

theorem "replace x y (delall x zs) = delall x zs"
  apply (induction zs)
  by (auto simp add: delall_app)

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
(*
Found by quickcheck:
  x = a\<^sub>1
  y = a\<^sub>2
  z = a\<^sub>1
  zs = [a\<^sub>1]
*)
  oops

theorem "rev(del1 x xs) = del1 x (rev xs)"
(*
Auto Quickcheck found a counterexample:
  x = a\<^sub>1
  xs = [a\<^sub>1, a\<^sub>2, a\<^sub>1]
*)
  oops

theorem "rev(delall x xs) = delall x (rev xs)"
  apply (induction xs)
  by (auto simp add: delall_app)  

end
