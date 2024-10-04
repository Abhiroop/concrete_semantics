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

(* Ex 3.1 *)

fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N i) = True" |
  "optimal (V x) = True" |
  "optimal (Plus (N _) (N _)) = False" |
  "optimal (Plus a b) = ((optimal a) \<and> (optimal b))"

lemma "optimal (asimp_const a)"
  apply(induction a)
  apply(auto split: aexp.split)
  done

(* Ex 3.2 *)
fun plus_ex :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus_ex (N a) (N b) = N (a+b)" |
  "plus_ex (Plus p (N a)) (N b) = Plus p (N (a+b))" |
  "plus_ex (N b) (Plus p (N a)) = Plus p (N (a+b))" |
  "plus_ex (Plus p (N a)) q = Plus (Plus p q) (N a)" |
  "plus_ex q (Plus p (N a)) = Plus (Plus p q) (N a)" |
  "plus_ex p (N i) = (if i = 0 then p else Plus p (N i))" |
  "plus_ex (N i) p = (if i = 0 then p else Plus p (N i))" |
  "plus_ex p q = (Plus p q)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp (N a) = N a" |
  "full_asimp (V x) = V x" |
  "full_asimp (Plus p q) = plus_ex (full_asimp p) (full_asimp q)"

lemma plus_ex_lemma [simp] :
  "aval (plus_ex a1 a2) s = aval a1 s + aval a2 s"
  apply(induction rule: plus_ex.induct)
  apply(auto)
  done

theorem "aval (full_asimp a) s = aval a s"
  apply(induction a)
  apply (auto split: aexp.split)
  done

(* Ex 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst var a (N n) = N n" |
  "subst var a (V x) = (if x = var then a else (V x))" |
  "subst var a (Plus a1 a2) = Plus (subst var a a1) (subst var a a2)"

lemma subst_lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction e)
  apply (auto)
  done

(* Ex 3.4 *)

datatype aexpm = Nm int | Vm vname | Plusm aexpm aexpm | Timesm aexpm aexpm

fun avalm :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
  "avalm (Nm a) s = a" |
  "avalm (Vm x) s = s x" |
  "avalm (Plusm a b) s = avalm a s + avalm b s" |
  "avalm (Timesm a b) s = avalm a s * avalm b s"

fun plusm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
  "plusm (Nm a) (Nm b) = Nm (a+b)" |
  "plusm p (Nm i) = (if i = 0 then p else Plusm p (Nm i))" |
  "plusm (Nm i) p = (if i = 0 then p else Plusm (Nm i) p)" |
  "plusm p q = (Plusm p q)"

fun timesm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
  "timesm (Nm a) (Nm b) = Nm (a*b)" |
  "timesm p (Nm i) = 
    (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
  "timesm (Nm i) p = 
    (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
  "timesm p q = (Timesm p q)"

fun asimpm :: "aexpm \<Rightarrow> aexpm" where
  "asimpm (Nm a) = Nm a" |
  "asimpm (Vm x) = Vm x" |
  "asimpm (Plusm p q) = plusm (asimpm p) (asimpm q)" |
  "asimpm (Timesm p q) = timesm (asimpm p) (asimpm q)"

lemma avalm_plus[simp]: "avalm (plusm p q) s = avalm p s + avalm q s"
  apply (induction rule:plusm.induct)
  apply (auto)
  done

lemma avalm_times[simp]: "avalm (timesm p q) s = avalm p s * avalm q s"
  apply (induction rule:timesm.induct)
  apply (auto)
  done

theorem "avalm (asimpm p) s = avalm p s"
  apply (induction p)
  apply (auto)
  done

end
