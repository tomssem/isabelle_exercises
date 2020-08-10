theory SumFlat
  imports Main
begin

text\<open> Define a function @{text sum}, which computes the sum of
elements of a list of natural numbers. \<close>

primrec  sum :: "nat list \<Rightarrow> nat"
  where
"sum [] = 0" |
"sum (x#xs) = x + sum xs"

text\<open> Then, define a function @{text flatten} which flattens a list
of lists by appending the member lists. \<close>

primrec  flatten :: "'a list list \<Rightarrow> 'a list"
  where
"flatten [] = []" |
"flatten (x#xs) = x @ flatten xs"

text\<open> Test your functions by applying them to the following example lists: \<close>

lemma "sum [2::nat, 4, 8] = 14"
  by simp

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = [2, 3, 4, 5, 7, 9]"
  by simp

text\<open> Prove the following statements, or give a counterexample: \<close>

lemma "length (flatten xs) = sum (map length xs)"
  apply (induction xs) by auto

lemma sum_append[simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply (induction xs) by auto

lemma flatten_append[simp]: "flatten (xs @ ys) = flatten xs @ flatten ys"
  apply (induction xs) by auto

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
  apply (induction xs) by auto

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
  apply (induction xs) by auto

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
  apply (induction xs) by auto

lemma "flatten (rev xs) = flatten xs"
(*
Auto Quickcheck found a counterexample:
  xs = [[a\<^sub>1], [a\<^sub>2]]
*)
  oops

lemma "sum (rev xs) = sum xs"
 apply (induction xs) by auto

text\<open> Find a (non-trivial) predicate @{text P} which satisfies \<close>

lemma "list_all (\<lambda>x. 1 < x) xs \<longrightarrow> length xs \<le> sum xs"
  apply (induction xs) by auto


text\<open> Define, by means of primitive recursion, a function @{text
list_exists} which checks whether an element satisfying a given property
is contained in the list: \<close>


primrec  list_exists :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
  where
"list_exists _ [] = False" |
"list_exists P (x#xs) = (P x \<or> list_exists P xs)"


text\<open> Test your function on the following examples: \<close>

lemma "list_exists (\<lambda> n. n < 3) [4::nat, 3, 7] = False"
  by simp

lemma "list_exists (\<lambda> n. n < 4) [4::nat, 3, 7] = True"
  by simp


text\<open> Prove the following statements: \<close>

lemma list_exists_append: 
  "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)"
  apply (induction xs) by auto

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
  apply (induction xs) by (auto simp add: list_exists_append)

text\<open> You could have defined @{text list_exists} only with the aid of
@{text list_all}.  Do this now, i.e. define a function @{text
list_exists2} and show that it is equivalent to @{text list_exists}. \<close>

definition list_exists2 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"list_exists2 P xs = (\<not>(list_all (\<lambda>x. \<not>P x) xs))"

lemma list_exists_equiv:"list_exists2 P xs = list_exists P xs"
  apply (induction xs) by (auto simp add: list_exists2_def)

(*<*) end (*>*)
