theory Polynomial imports Main begin (*>*)

text \<open>
Let the following data type for propositional formulae be given:
\<close>

datatype form = T | Var nat | And form form | Xor form form

text \<open>
Here @{term "T"} denotes a formula that is always true, @{term "Var n"} denotes
a propositional variable, its name given by a natural number, @{term "And f1
f2"} denotes the AND combination, and @{term "Xor f1 f2"} the XOR (exclusive or)
combination of two formulae.  A constructor @{term "F"} for a formula that is
always false is not necessary, since @{term "F"} can be expressed by @{term "Xor
T T"}.

{\bf Exercise 1:} Define a function
\<close>

definition xor::"bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<oplus>" 60)
  where
"xor a b = ((a \<and> \<not>b) \<or> (\<not>a \<and> b))"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
  where
"evalf _ T = True" |
"evalf val (Var n) = val n" |
"evalf val (And f\<^sub>1 f\<^sub>2) = (evalf val f\<^sub>1 \<and> evalf val f\<^sub>2)" |
"evalf val (Xor f\<^sub>1 f\<^sub>2) = (evalf val f\<^sub>1 \<oplus> evalf val f\<^sub>2)"

text \<open>
that evaluates a formula under a given variable assignment.
\<close>


text \<open>
Propositional formulae can be represented by so-called {\it polynomials}.  A
polynomial is a list of lists of propositional variables, i.e.\ an element of
type @{typ "nat list list"}.  The inner lists (the so-called {\it monomials})
are interpreted as conjunctive combination of variables, whereas the outer list
is interpreted as exclusive-or combination of the inner lists.

{\bf Exercise 2:} Define two functions
\<close>

primrec  evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool"
  where
"evalm _ [] = True" |
"evalm val (x#xs) = (val x \<and> evalm val xs)"

lemma evalm_correct[simp]:"evalm f (l1 @ l2) = (evalm f l1 \<and> evalm f l2)"
  apply (induction l1 arbitrary: l2) by auto

primrec evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool"
  where
"evalp _ [] = False" |
"evalp val (x#xs) = (evalm val x \<oplus> evalp val xs)"

lemma evalp_correct[simp]:"evalp f (l1 @ l2) = (evalp f l1 \<oplus> evalp f l2)"
  apply (induction l1 arbitrary: l2) by (auto simp add: xor_def)

text \<open>
for evaluation of monomials and polynomials under a given variable assignment.
In particular think about how empty lists have to be evaluated.
\<close>


text \<open>
{\bf Exercise 3:} Define a function
\<close>

primrec mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"
  where
"mulpp [] _ = []" |
"mulpp (x#xs) ys = (map (append x) ys) @ mulpp xs ys"

lemma mulpp_append[simp]:"mulpp (xs1 @ xs2) ys = mulpp xs1 ys @ mulpp xs2 ys"
  apply (induction xs1 arbitrary: xs2) by auto

lemma mulpp_empty_singletonL[simp]:"mulpp [[]] ys = ys"
  apply (induction ys) by auto

lemma mulpp_emptyR[simp]:"mulpp xs [] = []"
  apply (induction xs) by auto


lemma mulpp_empty_SingletonR[simp]:"mulpp xs [[]] = xs"
  apply (induction xs) by auto

lemma mulpp_map_eval[simp]:"evalp f (map (append l1) l2) = (evalm f l1 \<and> evalp f l2)"
  apply (induction l2) by (auto simp add: xor_def)

lemma eval_mulpp[simp]:"evalp f (mulpp l1 l2) = (evalp f l1 \<and> evalp f l2)"
  apply (induction l1)
  by (auto simp add: xor_def)


primrec poly :: "form \<Rightarrow> nat list list"
  where
"poly T = [[]]" |
"poly (Var n) = [[n]]" |
"poly (And f\<^sub>1 f\<^sub>2) = mulpp (poly f\<^sub>1) (poly f\<^sub>2)" |
"poly (Xor f\<^sub>1 f\<^sub>2) = (poly f\<^sub>1) @ (poly f\<^sub>2)"

text \<open>
that turns a formula into a polynomial.  You will need an auxiliary function
\<close>

text \<open>
to ``multiply'' two polynomials, i.e.\ to compute
\[
((v^1_1 \mathbin{\odot} \cdots \mathbin{\odot} v^1_{m_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (v^k_1 \mathbin{\odot} \cdots \mathbin{\odot} v^k_{m_k})) \mathbin{\odot}
((w^1_1 \mathbin{\odot} \cdots \mathbin{\odot} w^1_{n_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (w^l_1 \mathbin{\odot} \cdots \mathbin{\odot} w^l_{n_l}))
\]
where $\mathbin{\oplus}$ denotes ``exclusive or'', and $\mathbin{\odot}$ denotes
``and''.  This is done using the usual calculation rules for addition and
multiplication.
\<close>


text \<open>
{\bf Exercise 4:} Now show correctness of your function @{term "poly"}:
\<close>

theorem poly_correct: "evalf e f = evalp e (poly f)"
  apply (induction f) by (auto simp add: xor_def)

text \<open>
It is useful to prove a similar correctness theorem for @{term "mulpp"} first.
\<close>


(*<*) end (*>*)
