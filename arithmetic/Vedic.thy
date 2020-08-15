theory Vedic
    imports Main
begin

text\<open>
A book about Vedic mathematics describes three methods to make the calculation of squares of natural numbers easier:

\begin{itemize}
\item {\em MM1}: Numbers whose predecessors have squares that are known or can easily be calculated. For example:
\\ Needed: $61^2$  
\\ Given: $60^2 = 3600$
\\ Observe: $61^2 = 3600 + 60 + 61 = 3721$

\item {\em MM2}: Numbers greater than, but near 100. For example:
\\ Needed: $102^2$
\\ Let $h = 102 - 100 = 2$ , $h^2 = 4$
\\ Observe: $102^2 = (102+h)$ shifted two places to the left $ + h^2 = 10404$
 
\item {\em MM3}: Numbers ending in $5$. For example:
\\ Needed: $85^2$
\\ Observe: $85^2 = (8 * 9)$ appended to $ 25 = 7225$
\\ Needed: $995^2$
\\ Observe: $995^2 = (99 * 100)$ appended to $ 25 = 990025 $
\end{itemize}

In this exercise we will show that these methods are not so magical after all!

\begin{itemize}
\item Based on {\em MM1} define a function @{term "sq"} that calculates the square of a natural number.
\item Prove the correctness of @{term "sq"} (i.e.\ @{term "sq n = n * n"}).
\item Formulate and prove the correctness of {\em MM2}.\\ Hints:
  \begin{itemize}
  \item Generalise {\em MM2} for an arbitrary constant (instead of $100$).
  \item Universally quantify all variables other than the induction variable.
  \end{itemize}
\item Formulate and prove the correctness of {\em MM3}.\\ Hints:
  \begin{itemize}
  \item Try to formulate the property `numbers ending in $5$' such that it is easy to get to the rest of the number.
  \item Proving the binomial formula for $(a+b)^2$ can be of some help.
  \end{itemize}
\end{itemize}
\<close>


primrec sq :: "nat \<Rightarrow> nat"
  where
"sq 0 = 0" |
"sq (Suc n) = (if (10 dvd (Suc n))
               then (Suc n) * (Suc n)
               else (Suc n) + n + (sq n))"

lemma MM1[simp]:"sq n = n * n"
  apply (induction n) by auto

definition sq1 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
"sq1 n c = (let h = (n - c) in (n + h) * c + (sq h))"

lemma sq1_zero[simp]:"sq1 0 c = 0"
  by (simp add: sq1_def)

lemma MM2:"\<forall>c. c \<le> n \<Longrightarrow> (sq1 n c) = n*n"
  apply (simp add: Let_def sq1_def)
  apply (induction n , auto)
  by presburger

value "75 div 10::nat"

lemma bin_theorem_squared[simp]:"((a::nat) + b)^2 = a^2 + 2 * a * b + b^2"
  by algebra

definition sq2 :: "nat \<Rightarrow> nat"
  where
"sq2 n = (let c = n div 10 in ((Suc c) * c) * 100 + 25)"

value "sq2 35 = sq 35"
value "remaninder"

definition div_rem :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "div_rem a b q r = (b = a * q + r)"

lemma MM3:"div_rem 10 n c 5 \<Longrightarrow> ((Suc c) * c) * 100 + 25 = sq n"
  apply (simp add: Let_def sq2_def div_rem_def)
  apply (induction n, auto)
  by algebra

(*<*) end (*>*)
