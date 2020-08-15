theory Grandfather
  imports Main
begin

text \<open>
  First prove the following formula, which is valid in classical predicate
  logic, informally with pen and paper.  Use case distinctions and/or proof by
  contradiction.

  {\it  If every poor man has a rich father,\\
   then there is a rich man who has a rich grandfather.}
\<close>

theorem rich_grandfather: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> 
  \<exists>x. rich x \<and> rich (father (father x))"
proof -
  assume a: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x)"
  have "\<exists>x. rich x"
  proof (rule classical)
    fix y
    assume "\<not> (\<exists>x. rich x)"
    then have "\<forall>x. \<not> rich x" by simp
    then have "\<not> rich y" by simp
    with a have "rich (father y)" by simp
    then show ?thesis by auto
  qed
  then obtain x where x: "rich x" by auto
  show ?thesis
  
  proof cases
    assume "rich (father (father x))"
    with x show ?thesis by auto
  next
    assume b: "\<not> rich (father (father x))"
    with a have "rich (father (father (father x)))" by simp
    moreover have "rich (father x)" 
    proof (rule classical)
      assume "\<not> rich (father x)" 
      with a have "rich (father (father x))" by simp
      with b show ?thesis by contradiction 
    qed
    ultimately show ?thesis by auto
  qed
qed

text \<open>
  Now prove the formula in Isabelle using a sequence of rule applications (i.e.\
  only using the methods @{term rule}, @{term erule} and @{term assumption}).
\<close>

(*<*) end (*>*)
