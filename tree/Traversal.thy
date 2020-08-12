theory Traversal imports Main begin

text \<open> Define a datatype @{text"'a tree"} for binary trees. Both leaf and
internal nodes store information. \<close>

datatype 'a tree = Tip "'a" | Node "'a" "'a tree" "'a tree"


text \<open> Define the functions @{term preOrder}, @{term postOrder}, and @{term
inOrder} that traverse an @{text"'a tree"} in the respective order. \<close>


primrec  preOrder :: "'a tree \<Rightarrow> 'a list"
  where
"preOrder (Tip x) = [x]" |
"preOrder (Node x l r) = x # preOrder l @ preOrder r"

primrec  postOrder :: "'a tree \<Rightarrow> 'a list"
  where
"postOrder (Tip x) = [x]" |
"postOrder (Node x l r) = postOrder l @ postOrder r @ [x]"

primrec inOrder :: "'a tree \<Rightarrow> 'a list"
  where
"inOrder (Tip x) = [x]" |
"inOrder (Node x l r) = inOrder l @ [x] @ inOrder r"

text \<open> Define a function @{term mirror} that returns the mirror image of an
@{text "'a tree"}. \<close>

primrec  mirror :: "'a tree \<Rightarrow> 'a tree"
  where
"mirror (Tip x) = Tip x" |
"mirror (Node x l r) = Node x (mirror r) (mirror l)"


text \<open> Suppose that @{term xOrder} and @{term yOrder} are tree traversal
functions chosen from @{term preOrder}, @{term postOrder}, and @{term inOrder}.
Formulate and prove all valid properties of the form \mbox{@{text "xOrder
(mirror xt) = rev (yOrder xt)"}}. \<close>

lemma "inOrder (mirror xt) = rev (inOrder xt)"
  apply (induction xt) by auto

lemma "preOrder (mirror xt) = rev (postOrder xt)"
  apply (induction xt) by auto

lemma "postOrder (mirror xt) = rev (preOrder xt)"
  apply (induction xt) by auto

text \<open> Define the functions @{term root}, @{term leftmost} and @{term
rightmost}, that return the root, leftmost, and rightmost element respectively.
\<close>

definition root :: "'a tree \<Rightarrow> 'a"
  where
"root t = (case t of
          Tip x \<Rightarrow> x |
          Node x _ _ \<Rightarrow> x)"

primrec leftmost :: "'a tree \<Rightarrow> 'a"
  where
"leftmost (Tip x) = x" |
"leftmost (Node x l r) = leftmost l"

primrec rightmost :: "'a tree \<Rightarrow> 'a"
  where
"rightmost (Tip x) = x" |
"rightmost (Node x l r) = rightmost r"

text \<open> Prove (or let Isabelle disprove) the theorems that follow.  You
may have to prove some lemmas first. \<close>

lemma inOrder_not_empty:"inOrder xs \<noteq> []"
  apply (induction xs) by auto

theorem "last (inOrder xt) = rightmost xt"
  apply (induction xt) 
  by (auto simp add: inOrder_not_empty)

theorem "hd (inOrder xt) = leftmost xt"
  apply (induction xt)
  by (auto simp add: inOrder_not_empty)

theorem "hd (preOrder xt) = last (postOrder xt)"
  apply (induction xt) by auto

theorem "hd (preOrder xt) = root xt"
  apply (induction xt)
  by (auto simp add: root_def)

theorem "hd (inOrder xt) = root xt"
(*
Auto Quickcheck found a counterexample:
  xt = Node a\<^sub>1 (Tip a\<^sub>2) (Tip a\<^sub>1)
Evaluated terms:
  hd (inOrder xt) = a\<^sub>2
  root xt = a\<^sub>1
*)
(*<*) oops (*>*)

theorem "last (postOrder xt) = root xt"
  apply (induction xt) by (auto simp add: root_def)


(*<*) end (*>*)
