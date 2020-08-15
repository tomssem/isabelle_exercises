theory MyPredicate
    imports Main
begin

text \<open>
We are again talking about proofs in the calculus of Natural Deduction.  In
addition to the rules given in the exercise ``Propositional Logic'', you may
now also use

  @{text "exI:"}~@{thm exI[no_vars]}\\
  @{text "exE:"}~@{thm exE[no_vars]}\\
  @{text "allI:"}~@{thm allI[no_vars]}\\
  @{text "allE:"}~@{thm allE[no_vars]}\\

Give a proof of the following propositions or an argument why the formula is
not valid:
\<close>



lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  apply (rule impI)
  apply (erule exE)
  apply (rule allI)
  apply (rule exI)
  apply (rule allE)
  by assumption
   

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  apply (rule iffI)

   apply (rule impI)
   apply (erule exE)
   apply (erule allE)
   apply (erule impE)
    apply assumption+

  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule exI)
  by assumption


lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
  apply (rule iffI)

  apply (erule conjE)
   apply (rule allI)
   apply (erule allE)+
   apply (rule conjI)
    apply assumption+

  apply (rule conjI)
   apply (rule allI)
   apply (erule allE)
   apply (erule conjE)
   apply assumption
  apply (rule allI)
  apply (erule allE)
  apply (erule conjE)
  apply (assumption)

lemma "((\<forall> x. P x ) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
(*
  The LHS says that either all values of x are true for P or all values of x are true for Q.
  The RHS says that all values of x are true for either P or Q.
  Let's take P as the predicate "is odd" and for Q the predicate "is even", and let x range
  over the natural numbers. Clearly the LHS is true, every number is either odd or even.
  However the LHS is not true, it is not true that every number is even or every number is odd
*)
  oops

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
  apply (rule iffI)

   apply (erule disjE)
    apply (erule exE)
    apply (rule exI)
    apply (rule disjI1, assumption)
   apply (erule exE)
   apply (rule exI)
   apply (rule disjI2, assumption)

  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule exI, assumption)
  apply (rule disjI2)
  apply (rule exI, assumption)
  done

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
(*
Imagine P is the relation "is greater than"
The left hand side says that for every number there is a number that is bigger than it.
The RHS says the there is a number that is greater than every number. The LHS clearly does
not imply the RHS
*)
  oops

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply (rule iffI)

  apply (rule classical)
   apply (erule notE)
   apply (rule allI)
   apply (rule classical)
   apply (erule notE)
   apply (rule exI, assumption)

  apply (rule notI)
  apply (erule exE)
  apply (erule allE)
  apply (erule notE)
  by (assumption)
  

(*<*) end (*>*)
