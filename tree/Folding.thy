theory Folding
  imports Main
begin

subsubsection \<open> Some more list functions \<close>

text \<open> Recall the summation function \<close>

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

text \<open> In the Isabelle library, you will find (in the theory {\tt List.thy})
the functions @{text foldr} and @{text foldl}, which allow you to define some
list functions, among them @{text sum} and @{text length}.  Show the following:
\<close>

lemma sum_foldr: "sum xs = foldr (+) xs 0"
  apply (induction xs) by auto

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  apply (induction xs) by auto


text \<open> Repeated application of @{text foldr} and @{text map} has the
disadvantage that a list is traversed several times.  A single traversal is
sufficient, as illustrated by the following example: \<close>

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda> x a. x + 3 + a) xs 0"
  apply (induction xs) by auto
  

text \<open> Find terms @{text h} and @{text b} which solve this equation. \<close>


text \<open> Generalize this result, i.e.\ show for appropriate @{text h} and @{text
b}: \<close>

lemma "foldr g (map f xs) a = foldr (g \<circ> f) xs a"
  apply (induction xs) by auto

text \<open> Hint: Isabelle can help you find the solution if you use the equalities
arising during a proof attempt. \<close>


text \<open> The following function @{text rev_acc} reverses a list in linear time:
\<close>

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

text \<open> Show that @{text rev_acc} can be defined by means of @{text foldl}. \<close>

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  apply (induction xs arbitrary: a) by auto


text \<open> Prove the following distributivity property for @{text sum}: \<close>

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply (induction xs) by auto


text \<open> Prove a similar property for @{text foldr}, i.e.\ something like @{text
"foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"}.  However, you will
have to strengthen the premises by taking into account algebraic properties of
@{text f} and @{text a}. \<close>

lemma foldr_append: "\<lbrakk>\<forall> x. f a x = x; \<forall> x y z. f x (f y z) = f (f x y) z\<rbrakk> \<Longrightarrow>
                      foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
  apply (induction xs) by auto


text \<open> Now, define the function @{text prod}, which computes the product of
all list elements \<close>

definition prod :: "nat list \<Rightarrow> nat" where "prod xs = foldr (*) xs 1"


text \<open> directly with the aid of a fold and prove the following: \<close>

lemma "prod (xs @ ys) = prod xs * prod ys"
  apply (induction xs) by (auto simp add: prod_def)


subsubsection \<open> Functions on Trees \<close>

text \<open> Consider the following type of binary trees: \<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text \<open> Define functions which convert a tree into a list by traversing it in
pre-, resp.\ postorder: \<close>

primrec preorder :: "'a tree \<Rightarrow> 'a list"
  where
"preorder Tip = []" |
"preorder (Node l x r) = x#preorder l @ preorder r"

primrec postorder :: "'a tree \<Rightarrow> 'a list"
  where
"postorder Tip = []" |
"postorder (Node l x r) = postorder l @ postorder r @ [x]"


text \<open> You have certainly realized that computation of postorder traversal can
be efficiently realized with an accumulator, in analogy to @{text rev_acc}: \<close>

primrec  postorder_acc :: "['a tree, 'a list] \<Rightarrow> 'a list"
  where
"postorder_acc Tip xs = xs" |
"postorder_acc (Node l x r) xs = postorder_acc l (postorder_acc r (x#xs))"


text \<open> Define this function and show: \<close>

lemma "postorder_acc t xs = (postorder t) @ xs"
  apply (induction t arbitrary: xs) by auto


text \<open> @{text postorder_acc} is the instance of a function @{text foldl_tree},
which is similar to @{text foldl}. \<close>

primrec  foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b"
  where
"foldl_tree _ a Tip = a" |
"foldl_tree f a (Node l x r) = foldl_tree f (foldl_tree f (f a x) r) l"


text \<open> Show the following: \<close>

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
  apply (induction t) by auto
  
text \<open> Define a function @{text tree_sum} that computes the sum of the
elements of a tree of natural numbers: \<close>

primrec tree_sum :: "nat tree \<Rightarrow> nat"
  where
"tree_sum Tip = 0" |
"tree_sum (Node l x r) = x + tree_sum l + tree_sum r"

text \<open> and show that this function satisfies \<close>

lemma "tree_sum t = sum (preorder t)"
  apply (induction t) by auto

(*<*) end (*>*)
