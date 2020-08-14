theory PowSum
  imports Main
begin

subsubsection \<open> Power \<close>

text \<open> Define a primitive recursive function $pow~x~n$ that
computes $x^n$ on natural numbers. \<close>

primrec pow :: "nat => nat => nat"
  where
"pow _ 0 = 1" |
"pow x (Suc n) = x * (pow x n)"

lemma pow_add:"pow x (m + n) = pow x m * pow x n"
  apply (induction m) by auto

lemma pow_0[simp]:"pow 0 (Suc n) = 0"
  by auto

lemma pow_1[simp]:"pow 1 n = 1"
  apply (induction n) by auto

lemma pow_same_num:"pow x n * pow y n = pow (x * y) n"
  apply (induction n) by auto
  
text \<open> Prove the well known equation $x^{m \cdot n} = (x^m)^n$: \<close>

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  apply (induction m)
  using pow_1 pow_add pow_same_num apply auto
  done

text \<open> Hint: prove a suitable lemma first.  If you need to appeal to
associativity and commutativity of multiplication: the corresponding
simplification rules are named @{text mult_ac}. \<close>


subsubsection \<open> Summation \<close>

text \<open> Define a (primitive recursive) function $sum~ns$ that sums a list
of natural numbers: $sum [n_1, \dots, n_k] = n_1 + \cdots + n_k$. \<close>

primrec sum :: "nat list => nat"
  where
"sum [] = 0" |
"sum (x#xs) = x + sum xs"

lemma sum_append[simp]:"sum (xs @ ys) = sum xs + sum ys"
  apply (induction xs) by auto


text \<open> Show that $sum$ is compatible with $rev$. You may need a lemma. \<close>

theorem sum_rev: "sum (rev ns) = sum ns"
  apply (induction ns) by auto


text \<open> Define a function $Sum~f~k$ that sums $f$ from $0$ up to $k-1$:
$Sum~f~k = f~0 + \cdots + f(k - 1)$. \<close>

primrec Sum :: "(nat => nat) => nat => nat"
  where
"Sum _ 0 = 0" |
"Sum f (Suc n) = (f n) + Sum f n"


text \<open> Show the following equations for the pointwise summation of functions.
Determine first what the expression @{text whatever} should be. \<close>

theorem Sum_plus:"Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k"
  apply (induction k) by auto

theorem "Sum f (k + l) = Sum f k + Sum (\<lambda>i. f (k + i)) l"
  apply (induction l) by (auto simp add: Sum_plus)

text \<open> What is the relationship between @{term sum} and @{text Sum}?
Prove the following equation, suitably instantiated. \<close>

theorem "Sum f k = sum (map f [0..<k])"
  apply (induction k) by auto
 

text \<open> Hint: familiarize yourself with the predefined functions @{term map}
and @{text"[i..<j]"} on lists in theory List. \<close>


end
