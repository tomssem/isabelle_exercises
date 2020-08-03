theory Searching imports Main begin

text \<open> Define a function @{text first_pos} that computes the index
of the first element in a list that satisfies a given predicate: \<close>

(*<*) consts (*>*)
  first_pos' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"

primrec first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"
  where
"first_pos _ [] = 0" |
"first_pos P (x#xs) = (if (P x)
                       then 0
                       else (Suc (first_pos P xs)))"

text \<open> The smallest index is @{text 0}.  If no element in the
list satisfies the predicate, the behaviour of @{text first_pos} should
be as described below. \<close>


text \<open> Verify your definition by computing
\begin{itemize}
\item the index of the first number equal to @{text 3} in the list
  @{text "[1::nat, 3, 5, 3, 1]"},
\item the index of the first number greater than @{text 4} in the list
  @{text "[1::nat, 3, 5, 7]"},
\item the index of  the first list with more than one element in the list
  @{text "[[], [1, 2], [3]]"}.
\end{itemize}

\emph{Note:} Isabelle does not know the operators @{text ">"} and @{text
"\<ge>"}.  Use @{text "<"} and @{text "\<le>"} instead. \<close>

value "first_pos (\<lambda>x. x = 3) [1::nat, 3, 5, 3, 1]"
value "first_pos (\<lambda>x. 4 < x) [1::nat, 3, 5, 7]"
value "first_pos (\<lambda>x. 1 < length x) [[], [1, 2], [3::nat]]"


text \<open> Prove that @{text first_pos} returns the length of the list if
and only if no element in the list satisfies the given predicate. \<close>

lemma "((first_pos P xs) = (length xs)) = (\<not>(list_ex P xs))"
  apply (induction xs) by auto

text \<open> Now prove: \<close>

lemma "list_all (\<lambda> x. \<not> P x) (take (first_pos P xs) xs)"
  apply (induction xs) by auto

text \<open> How can @{text "first_pos (\<lambda> x. P x \<or> Q x) xs"} be computed from
@{text "first_pos P xs"} and @{text "first_pos Q xs"}?  Can something
similar be said for the conjunction of @{text P} and @{text Q}?  Prove
your statement(s). \<close>

lemma "(first_pos (\<lambda> x. P x \<or> Q x) xs) = min (first_pos P xs) (first_pos Q xs)"
  apply (induction xs) by auto


text \<open> Suppose @{text P} implies @{text Q}. What can be said about the
relation between @{text "first_pos P xs"} and @{text "first_pos Q xs"}?
Prove your statement. \<close>

lemma "(\<And> x. (P x \<Longrightarrow> Q x)) \<Longrightarrow> (first_pos Q xs \<le> first_pos P xs)"
  apply (induction xs) by auto

text \<open> Define a function @{text count} that counts the number of
elements in a list that satisfy a given predicate. \<close>

(*<*) consts (*>*)
  count' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"

primrec count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"
  where
"count _ []     = 0" |
"count P (x#xs) = (if (P x)
                   then Suc (count P xs)
                   else count P xs)"

lemma [simp]:"count P (xs @ ys) = count P xs + count P ys"
  apply (induction xs) by auto

text \<open> Show: The number of elements with a given property stays the
same when one reverses a list with @{text rev}.  The proof will require
a lemma. \<close>

lemma "count P (rev xs) = count P xs"
  apply (induction xs) by auto

text \<open> Find and prove a connection between the two functions @{text filter}
and @{text count}. \<close>

lemma "length (filter P xs) = count P xs"
  apply (induction xs) by auto

(*<*) end (*>*)
