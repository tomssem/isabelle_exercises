theory QuantLists
    imports Main
begin

text \<open> Define a universal and an existential quantifier on lists
using primitive recursion.  Expression @{term "alls P xs"} should
be true iff @{term "P x"} holds for every element @{term x} of
@{term xs}, and @{term "exs P xs"} should be true iff @{term "P x"}
holds for some element @{term x} of @{term xs}.
\<close>

consts 
  alls' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  exs'  :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

fun alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "alls _ [] = True" |
  "alls P (x#xs) = (P x \<and> (alls P xs))"

lemma alls_app[simp]:"alls P (xs @ ys) = (alls P xs \<and> alls P ys)"
  apply (induction xs)
  by auto

fun exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "exs _ [] = False" |
  "exs P (x#xs) = (P x \<or> (exs P xs))"

lemma exs_app[simp]:"exs P (xs @ ys) = (exs P xs \<or> exs P ys)"
  apply (induction xs)
  by auto

lemma alls_exs_dual1:"exs P xs = (\<not>alls (\<lambda> x. \<not>P x) xs)"
  apply (induction xs)
  by auto

lemma exs_alls_dual1:"alls P xs = (\<not>exs (\<lambda> x. \<not>P x) xs)"
  apply (induction xs)
  by auto

text \<open>
Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.

Use the @{text "[simp]"}-attribute only if the equation is truly a
simplification and is necessary for some later proof.
\<close>

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  apply (induction xs) by auto

lemma "alls P (rev xs) = alls P xs"
  apply (induction xs) by auto

lemma "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
  (*
Auto Quickcheck found a counterexample:
  P = {a\<^sub>1}
  Q = {a\<^sub>2}
  xs = [a\<^sub>1, a\<^sub>2]
Evaluated terms:
  exs (\<lambda>x. P x \<and> Q x) xs = False
  exs P xs \<and> exs Q xs = True
*)
  oops

lemma "exs P (map f xs) = exs (P o f) xs"
  apply (induction xs) by auto

lemma "exs P (rev xs) = exs P xs"
  apply (induction xs) by auto

text \<open> Find a (non-trivial) term @{text Z} such that the following equation holds: \<close>

lemma "exs (\<lambda>x. P x \<or> Q x) xs = (exs P xs) \<or> (exs Q xs)"
  apply (induction xs) by auto

text \<open> Express the existential via the universal quantifier --
@{text exs} should not occur on the right-hand side: \<close>

lemma "exs P xs = (\<not> alls (\<lambda>x. \<not>P x) xs)"
  by (rule alls_exs_dual1)

text \<open>
Define a primitive-recursive function @{term "is_in x xs"} that
checks if @{term x} occurs in @{term xs}. Now express
@{text is_in} via @{term exs}:
\<close>

primrec is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"is_in _ [] = False"|
"is_in a (x#xs) = ((a = x) \<or> (is_in a xs))"

lemma "is_in a xs = exs (\<lambda>x. x = a) xs"
  apply (induction xs) by auto

text \<open> Define a primitive-recursive function @{term "nodups xs"}
that is true iff @{term xs} does not contain duplicates, and a
function @{term "deldups xs"} that removes all duplicates.  Note
that @{term "deldups[x,y,x]"} (where @{term x} and @{term y} are
distinct) can be either @{term "[x,y]"} or @{term "[y,x]"}.

Prove or disprove (by counterexample) the following theorems.
\<close>

primrec nodups :: "'a list \<Rightarrow> bool"
  where
"nodups [] = True" |
"nodups (x#xs) = ((x \<in> set xs) \<or> nodups xs)"

primrec deldups :: "'a list \<Rightarrow> 'a list"
  where
"deldups [] = []" |
"deldups (x#xs) = (if (x \<in> set xs)
                   then deldups xs
                   else x#(deldups xs))"

lemma "length (deldups xs) <= length xs"
  apply (induction xs) by auto

lemma "nodups (deldups xs)"
  apply (induction xs) by auto

lemma "deldups (rev xs) = rev (deldups xs)"
(* counter example:
  xs = [1, 2, 3, 1]
  deldups (rev xs) = [3, 2, 1]
  rev (deldups xs) = [2, 3, 1]
*)
  oops

(*<*) end (*>*)
