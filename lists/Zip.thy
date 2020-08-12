(*
    $Id: ex.thy,v 1.4 2012/01/04 14:35:44 webertj Exp $
    Author: Farhad Mehta
*)

header \<open> Recursive Functions and Induction: Zip \<close>

theory Zip
  imports Main
begin

text \<open>
Read the chapter about total recursive functions in the ``Tutorial on
Isabelle/HOL'' (@{text fun}, Chapter 3.5).
\<close>

text \<open>
In this exercise you will define a function @{text Zip} that merges two lists
by interleaving.
 Examples:
@{text "Zip [a1, a2, a3]  [b1, b2, b3] = [a1, b1, a2, b2, a3, b3]"} 
 and
@{text "Zip [a1] [b1, b2, b3] = [a1, b1, b2, b3]"}.

Use three different approaches to define @{text Zip}:
\begin{enumerate}
\item by primitive recursion on the first list,
\item by primitive recursion on the second list,
\item by total recursion (using @{text fun}).
\end{enumerate}
\<close>


primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"zip1 [] ys = ys" |
"zip1 (x#xs) ys = (if (0 < length ys)
                   then x#hd ys#zip1 xs (tl ys)
                   else (x#xs))"

lemma zip1_empty_ys_empty[simp]:"zip1 xs [] = xs"
  apply (induction xs) by auto

primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"zip2 xs [] = xs" |
"zip2 xs (y#ys) = (case xs of
                    []     \<Rightarrow> (y#ys) |
                    (x#xs) \<Rightarrow> x#y#zip2 xs ys)"

lemma zip2_empty_xs_empty[simp]:"zip2 [] ys = ys"
  apply (induction ys) by auto

fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"zipr [] ys = ys" |
"zipr xs [] = xs" |
"zipr (x#xs) (y#ys) = x#y#zipr xs ys"

lemma zipr_xs_empty_xs[simp]:"zipr xs [] = xs"
  by (metis list.exhaust zipr.simps(1) zipr.simps(2))

text \<open>
Show that all three versions of @{text Zip} are equivalent.
\<close>

lemma zip2_eq_zipr:"zip2 xs ys = zipr xs ys"
  apply (induction xs arbitrary: ys)
   apply simp_all
  apply (case_tac ys) by auto

lemma zip1_eq_zipr:"zip1 xs ys = zipr xs ys"
  apply (induction ys arbitrary: xs)
   apply simp_all
  apply (case_tac xs) by auto


text \<open>
Show that @{text zipr} distributes over @{text append}.
\<close>

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> 
  zipr (p@q) (u@v) = zipr p u @ zipr q v"
  apply (induction p arbitrary: q u v)
   apply auto
  apply (case_tac u) by auto  


text \<open>
{\bf Note:} For @{text fun}, the order of your equations is relevant.
If equations overlap, they will be disambiguated before they are added
to the logic.  You can have a look at these equations using @{text
"thm zipr.simps"}.
\<close>

end
