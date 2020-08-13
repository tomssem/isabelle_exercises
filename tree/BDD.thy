theory BDD
    imports
Main begin

text \<open>
Boolean functions (in finitely many variables) can be represented by so-called
{\it binary decision diagrams} (BDDs), which are given by the following data
type:
\<close>

datatype bdd = Leaf bool | Branch bdd bdd

text \<open>
A constructor @{term "Branch b1 b2"} that is $i$ steps away from the root of
the tree corresponds to a case distinction based on the value of the variable
$v_i$.  If the value of $v_i$ is @{term "False"}, the left subtree @{term "b1"}
is evaluated, otherwise the right subtree @{term "b2"} is evaluated.  The
following figure shows a Boolean function and the corresponding BDD.
\begin{center}
\begin{minipage}{8cm}
\begin{tabular}{|c|c|c|c|} \hline
$v_0$ & $v_1$ & $v_2$ & $f(v_0,v_1,v_2)$ \\ \hline
@{term "False"} & @{term "False"} & *               & @{term "True"} \\
@{term "False"} & @{term "True"}  & *               & @{term "False"} \\
@{term "True"}  & @{term "False"} & *               & @{term "False"} \\
@{term "True"}  & @{term "True"}  & @{term "False"} & @{term "False"} \\
@{term "True"}  & @{term "True"}  & @{term "True"}  & @{term "True"} \\ \hline
\end{tabular}
\end{minipage}
\begin{minipage}{7cm}
\begin{picture}(0,0)%
\includegraphics[scale=0.5]{bdd}%
\end{picture}%
\setlength{\unitlength}{2072sp}%
\begin{picture}(6457,3165)(1329,-4471)
\put(1351,-3571){\makebox(0,0)[b]{@{term "True"}}}%
\put(3151,-3571){\makebox(0,0)[b]{@{term "False"}}}%
\put(4951,-3571){\makebox(0,0)[b]{@{term "False"}}}%
\put(5851,-4471){\makebox(0,0)[b]{@{term "False"}}}%
\put(7651,-4471){\makebox(0,0)[b]{@{term "True"}}}%
\put(7786,-3301){\makebox(0,0)[lb]{$v_2$}}%
\put(7786,-2401){\makebox(0,0)[lb]{$v_1$}}%
\put(7786,-1501){\makebox(0,0)[lb]{$v_0$}}%
\end{picture}
\end{minipage}
\end{center}

{\bf Exercise 1:} Define a function
\<close>

primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool"
  where
"eval _ _ (Leaf b) = b" |
"eval val i (Branch b1 b2) = (if (val i)
                             then (eval val (Suc i) b2)
                             else (eval val (Suc i) b1))"

text \<open>
that evaluates a BDD under a given variable assignment, beginning at a variable
with a given index.
\<close>


text \<open>
{\bf Exercise 2:} Define two functions
\<close>


primrec  bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd"
  where
"bdd_unop f (Leaf b) = Leaf (f b)" |
"bdd_unop f (Branch b1 b2) = Branch (bdd_unop f b1) (bdd_unop f b2)"

lemma bdd_unop_correct:"eval val i (bdd_unop f b) = f (eval val i b)"
  apply (induction b arbitrary: i) by auto

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  where
"bdd_binop f (Leaf x) b = bdd_unop (f x) b" |
"bdd_binop f (Branch b1\<^sub>1 b2\<^sub>1) b =
   (case b of
   Leaf x          \<Rightarrow> Branch (bdd_binop f b1\<^sub>1 b) (bdd_binop f b2\<^sub>1 b) |
   Branch b1\<^sub>2 b2\<^sub>2  \<Rightarrow> Branch (bdd_binop f b1\<^sub>1 b1\<^sub>2) (bdd_binop f b2\<^sub>1 b2\<^sub>2))"

lemma bdd_binop_correct:"eval val i (bdd_binop f b1 b2) = f (eval val i b1) (eval val i b2)"
  apply (induction b1 arbitrary: i b2)
  by (auto simp add: bdd_unop_correct split: bdd.split)

text \<open>
for the application of unary and binary operators to BDDs, and prove their
correctness.
\<close>


text \<open>
Now use @{term "bdd_unop"} and @{term "bdd_binop"} to define
\<close>

definition bdd_and :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  where
"bdd_and b1 b2 = bdd_binop (\<and>) b1 b2"

definition bdd_or :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  where
"bdd_or b1 b2 = bdd_binop (\<or>) b1 b2"

definition  bdd_not :: "bdd \<Rightarrow> bdd"
  where
"bdd_not b = bdd_unop (\<lambda>x. \<not>x) b"

definition xor:: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<oplus>" 60)
  where
"xor a b = ((a \<and> \<not>b) \<or> (\<not>a \<and> b))"

definition bdd_xor :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  where
"bdd_xor b1 b2 = bdd_binop (\<oplus>) b1 b2"

lemma bdd_and_correct:"eval val i (bdd_and b1 b2) = ((eval val i b1) \<and> (eval val i b2))"
  by (simp add: bdd_and_def bdd_binop_correct)

lemma bdd_or_correct:"eval val i (bdd_or b1 b2) = ((eval val i b1) \<or> (eval val i b2))"
  by (simp add: bdd_or_def bdd_binop_correct)

lemma bdd_not_correct:"eval val i (bdd_not b) = (\<not>(eval val i b))"
  by (simp add: bdd_not_def bdd_unop_correct)

lemma bdd_xor_correct:"eval val i (bdd_xor b1 b2) = (eval val i b1) \<oplus> (eval val i b2)"
  by (simp add: bdd_xor_def bdd_binop_correct)

text \<open>
and show correctness.
\<close>


text \<open>
Finally, define a function
\<close>

primrec bdd_var :: "nat \<Rightarrow> bdd"
  where
"bdd_var 0 = (Branch (Leaf False) (Leaf True))" |
"bdd_var (Suc n) = (Branch (bdd_var n) (bdd_var n))"

text \<open>
to create a BDD that evaluates to @{term "True"} if and only if the variable
with the given index evaluates to @{term "True"}.  Again prove a suitable
correctness theorem.

{\bf Hint:} If a lemma cannot be proven by induction because in the inductive
step a different value is used for a (non-induction) variable than in the
induction hypothesis, it may be necessary to strengthen the lemma by universal
quantification over that variable (cf.\ Section 3.2 in the Tutorial on
Isabelle/HOL).
\<close>

lemma bdd_var_correct:"eval val j (bdd_var i) = val (i + j)"
  apply (induction i arbitrary: j) by auto

text_raw \<open> \begin{minipage}[t]{0.45\textwidth} \<close>
 
text\<open>
{\bf Example:} instead of
\<close>

lemma "P (b::bdd) x" 
apply (induct b) (*<*) oops (*>*)

text_raw \<open> \end{minipage} \<close>
text_raw \<open> \begin{minipage}[t]{0.45\textwidth} \<close>   

text \<open> Strengthening: \<close>

lemma "\<forall>x. P (b::bdd) x"
apply (induct b) (*<*) oops (*>*)  

text_raw \<open> \end{minipage} \\[0.5cm]\<close> 


text \<open>
{\bf Exercise 3:} Recall the following data type of propositional formulae
(cf.\ the exercise on ``Representation of Propositional Formulae by
Polynomials'')
\<close>

datatype form = T | Var nat | And form form | Xor form form

text \<open>
together with the evaluation function @{text "evalf"}:
\<close>

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
  "evalf e T = True"
| "evalf e (Var i) = e i"
| "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"
| "evalf e (Xor f1 f2) = xor (evalf e f1) (evalf e f2)"

text \<open>
Define a function
\<close>

primrec mk_bdd :: "form \<Rightarrow> bdd"
  where
"mk_bdd T = (Leaf True)" |
"mk_bdd (Var n) = bdd_var n" |
"mk_bdd (And f1 f2) = bdd_and (mk_bdd f1) (mk_bdd f2)" |
"mk_bdd (Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)"

text \<open>
that transforms a propositional formula of type @{typ "form"} into a BDD.
Prove the correctness theorem
\<close>

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
  apply (induction f arbitrary: e)
    by (auto simp add: bdd_var_correct bdd_and_correct bdd_xor_correct)


(*<*) end (*>*)
