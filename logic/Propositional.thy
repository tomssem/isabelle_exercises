theory Propositional
    imports Main
begin

text \<open> In this exercise, we will prove some lemmas of propositional
logic with the aid of a calculus of natural deduction.

For the proofs, you may only use

\begin{itemize}
\item the following lemmas: \\
@{text "notI:"}~@{thm notI[of A,no_vars]},\\
@{text "notE:"}~@{thm notE[of A B,no_vars]},\\
@{text "conjI:"}~@{thm conjI[of A B,no_vars]},\\ 
@{text "conjE:"}~@{thm conjE[of A B C,no_vars]},\\
@{text "disjI1:"}~@{thm disjI1[of A B,no_vars]},\\
@{text "disjI2:"}~@{thm disjI2[of A B,no_vars]},\\
@{text "disjE:"}~@{thm disjE[of A B C,no_vars]},\\
@{text "impI:"}~@{thm impI[of A B,no_vars]},\\
@{text "impE:"}~@{thm impE[of A B C,no_vars]},\\
@{text "mp:"}~@{thm mp[of A B,no_vars]}\\
@{text "iffI:"}~@{thm iffI[of A B,no_vars]}, \\
@{text "iffE:"}~@{thm iffE[of A B C,no_vars]}\\
@{text "classical:"}~@{thm classical[of A,no_vars]}

\item the proof methods @{term rule}, @{term erule} and @{term assumption}.
\end{itemize}

Prove:
\<close>

lemma I: "A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  by assumption

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  by assumption

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  by assumption

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
    apply (rule disjI1, assumption)
   apply (rule disjI2, rule disjI1, assumption)
  apply (rule disjI2, rule disjI2, assumption)
  done

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)
  apply (rule impI)
  by assumption

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
   apply (rule conjI)
    apply (erule disjE)
     apply assumption+
   apply (erule disjE)
    apply assumption+
  apply (erule conjE)
  apply (rule disjI1)
  by assumption
     

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (drule mp, assumption)+
  by assumption
  

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (drule mp, assumption)+
  by assumption

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE, assumption)
  done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE, assumption)
  done

lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE, assumption)
  by (rule notE)

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
    apply (rule impI)
  by (erule notE, assumption)+
    
lemma "A \<or> \<not> A"
  apply (rule classical)
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  by assumption
  

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)
   apply (rule classical)
   apply (rule disjI1)
   apply (rule notI)
   apply (erule notE)
   apply (rule classical)
   apply (rule conjI, assumption)
   apply (rule classical)
   apply (erule notE)
   apply (rule disjI2, assumption)
  apply (rule classical)
  apply (rule notI)
  apply (erule notE)
  apply (erule conjE)
  apply (erule disjE)
  by (erule notE, assumption)+

  

(*<*) end (*>*)

