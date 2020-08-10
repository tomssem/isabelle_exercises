theory SumTail
  imports Main
begin

text \<open>
\begin{description}
\item[\bf (a)] Define a primitive recursive function @{term ListSum} that
computes the sum of all elements of a list of natural numbers.

Prove the following equations.  Note that @{term  "[0..n]"} und @{term
"replicate n a"} are already defined in a theory {\tt List.thy}.
\end{description}
\<close>

primrec ListSum :: "nat list \<Rightarrow> nat"
  where
"ListSum [] = 0" |
"ListSum (x#xs) = x + ListSum xs"

lemma ListSum_append[simp]:"ListSum (xs @ ys) = ListSum xs + ListSum ys"
  apply (induction xs) by auto

theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
  apply (induction n) by auto

theorem "ListSum (replicate n a) = n * a"
  apply (induction n) by auto


text \<open> 
\begin{description}
\item[\bf (b)] Define an equivalent function @{term ListSumT} using a
tail-recursive function @{term ListSumTAux}.  Prove that @{term ListSum}
and @{term ListSumT} are in fact equivalent.
\end{description}
\<close>

primrec ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
"ListSumTAux [] n = n" |
"ListSumTAux (x#xs) n = ListSumTAux xs (x + n)"

lemma ListSumTAux_sum_accum[simp]:"\<forall> a b. ListSumTAux xs (a + b) = a + ListSumTAux xs b"
  apply (induction xs) by auto

lemma ListSumTAux_append[simp]:"ListSumTAux (xs @ ys) 0 = ListSumTAux xs 0 + ListSumTAux ys 0"
  apply (induction xs)
   apply auto
  by (metis ListSumTAux_sum_accum Nat.add_0_right)

definition ListSumT :: "nat list \<Rightarrow> nat"
  where
"ListSumT xs = ListSumTAux xs 0"

lemma ListSumT_append[simp]:"ListSumT (xs @ ys) = ListSumT xs + ListSumT ys"
  apply (induction xs)
   apply (auto simp add: ListSumT_def)
  by (metis ListSumTAux_append ListSumTAux_sum_accum add.commute add.left_neutral)

theorem "ListSum xs = ListSumT xs"
  apply (induction xs)
   apply (auto simp add: ListSumT_def)
  by (metis ListSumTAux_sum_accum Nat.add_0_right)

end
