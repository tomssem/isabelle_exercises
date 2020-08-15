theory Elimination
  imports Main
begin

text \<open> In classical propositional logic, the connectives @{text "=, \<or>,
\<not>"} can be replaced by @{text "\<longrightarrow>, \<and>, False"}.  Define
corresponding simplification rules as lemmas and prove their correctness.  (You
may use automated proof tactics.) \<close>

lemma iff_rewrite:"(A = B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
  by blast

lemma demorgan:"(A \<or> B) = (\<not>(\<not>A \<and> \<not>B))"
  by blast

lemma false_rewrite:"(\<not>A) = (A \<longrightarrow> False)"
  by blast

text \<open> What is the result of your translation for the formula @{text "A \<or>
(B \<and> C) = A"}?  (You can use Isabelle's simplifier to compute the result
by using the simplifier's @{text "only"} option.) \<close>

lemma "(A \<or> (B \<and> C) = A)"
  apply (simp only: iff_rewrite demorgan false_rewrite)
  oops

(*<*) end (*>*)
