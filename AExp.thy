section "Arithmetic and Boolean Expressions"

theory AExp imports Main begin

subsection "Arithmetic Expressions"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"


value "aval (Plus (V ''y'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

(* f (a := b) = (\<lambda>x . if x = a then b else f x ) *)
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"


definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text \<open>In the @{term "<a := b>"} syntax, variables that are not 
      mentioned are 0 by default:\<close>
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text \<open>Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}.\<close>


subsection "Constant Folding"

text \<open>Evaluate constant subexpressions:\<close>


fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of
      (N n1, N n2) \<Rightarrow> N (n1 + n2) |
      (b1, b2) \<Rightarrow> Plus b1 b2)"


lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
  apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)" |
  "plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i = 0 then a else Plus a (N i))" |
  "plus a1 a2 = Plus a1 a2 "

lemma aval_plus [simp]: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
  apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"


value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
  done



end
