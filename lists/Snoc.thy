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

lemma "\<And>ys xs. rev xs @ [x] = snoc (rev xs) x \<Longrightarrow> rev xs @ rev ys @ [x] = snoc (rev xs @ ys) x"
by try

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  apply (induct "xs")
   apply (simp)
  apply(simp)


text \<open>Hint: you need to prove a suitable lemma first.\<close>

end
