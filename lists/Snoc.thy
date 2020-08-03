theory Snoc
  imports Main
begin

text \<open>Define a primitive recursive function @{text snoc} that appends an element
at the \emph{right} end of a list. Do not use @{text"@"} itself.\<close>

fun snoc :: "'a list => 'a => 'a list"
  where
"snoc [] c = [c]" |
"snoc (x#xs) c = x # (snoc xs c)"

text \<open>Prove the following theorem:\<close>

lemma [simp]:"snoc xs x = xs @ [x]"
  apply(induction xs) by auto

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  apply (induction xs) by auto


text \<open>Hint: you need to prove a suitable lemma first.\<close>

end
