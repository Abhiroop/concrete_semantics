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
  "asimpm (Plusm p q)  = plusm (asimpm p) (asimpm q)" |
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

(* Ex 3.5 *)
datatype aexp2 = N2 int | V2 vname | Plus2  aexp2 aexp2
               | PlusPlus2 vname   | Times2 aexp2 aexp2 | Div2 aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 a) s = Some (a, s)" |
  "aval2 (V2 x) s = Some (s x, s)" |
  "aval2 (PlusPlus2 x) s = Some (s x, s(x:= 1 + (s x)))" |
  "aval2 (Plus2 a b) s =
    (case (aval2 a s, aval2 b s) of
      (None, Some q)   \<Rightarrow> None |
      (Some p, None)   \<Rightarrow> None |
      (Some p, Some q) \<Rightarrow>
        Some ((fst p + fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
  "aval2 (Times2 a b) s =
    (case (aval2 a s, aval2 b s) of
      (None, Some q)   \<Rightarrow> None |
      (Some p, None)   \<Rightarrow> None |
      (Some p, Some q) \<Rightarrow>
        Some ((fst p * fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
  "aval2 (Div2 a b) s =
    (case (aval2 a s, aval2 b s) of
      (None, Some q)   \<Rightarrow> None |
      (Some p, None)   \<Rightarrow> None |
      (Some p, Some q) \<Rightarrow>
        (if fst q = 0 then None
        else Some ((fst p div fst q),
            (\<lambda>x.((snd p) x) + ((snd q) x) - (s x)))))"

(* Ex 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp


fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl a) s = a" |
  "lval (Vl x) s = s x" |
  "lval (Plusl p q) s = lval p s + lval q s" |
  "lval (LET x a e) s = lval e (s(x:=lval a s))"


fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl i)     = N i" |
  "inline (Vl vname) = V vname" |
  "inline (Plusl p q) = Plus (inline p) (inline q)" |
  "inline (LET x a e) = subst x (inline a) (inline e)"

lemma "lval e s = aval (inline e) s"
  apply(induction e arbitrary: s)
  apply(auto)
  done

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v ) s = v" |
  "bval (Not b) s = (\<not> bval b s)" |
  "bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)" |
  "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True)  = Bc False" |
  "not (Bc False) = Bc True" |
  "not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and b (Bc True) = b" |
  "and (Bc False) b = Bc False" |
  "and b (Bc False) = Bc False" |
  "and b1 b2 = And b1 b2 "

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n1) (N n2) = Bc(n1 < n2 )" |
  "less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v)  = Bc v" |
  "bsimp (Not b) = not (bsimp b)" |
  "bsimp (And b1 b2)  = and (bsimp b1) (bsimp b2)" |
  "bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

(* Ex 3.7 *)
definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq p q = And (Not (Less p q)) (Not (Less q p))"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le p q = Not (Less q p)"

theorem "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(simp add:Eq_def)
  apply(auto)
  done

theorem "bval (Le a1 a2) s = (aval a1 s <= aval a2 s)"
  apply(simp add:Le_def)
  apply(auto)
  done

(* Ex 3.8 *)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

definition or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or p q = Not (And (Not p) (Not q))"

definition implies :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "implies p q = or (Not p) q"

definition bIf :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "bIf a b c = And (implies a b) (implies (Not a) c)"

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 b) s     = b" |
  "ifval (If a b c) s  = (if (ifval a s) then (ifval b s) else (ifval c s))" |
  "ifval (Less2 x y) s = (aval x s < aval y s)"


fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc b)     = Bc2 b" |
  "b2ifexp (Not b)    = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
  "b2ifexp (And a b)  = (If (b2ifexp a) (b2ifexp b) (Bc2 False))" |
  "b2ifexp (Less x y) = (Less2 x y)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 b) = Bc b" |
  "if2bexp (If a b c) = bIf (if2bexp a) (if2bexp b) (if2bexp c)" |
  "if2bexp (Less2 x y) = (Less x y)"

theorem "bval (if2bexp p) s = ifval p s"
  apply(induction p)
  apply(simp_all add: bIf_def implies_def or_def)
  done

theorem "ifval (b2ifexp p) s = bval p s"
  apply(induction p)
  apply(auto)
  done

(* Ex 3.9 *)
datatype pbexp = VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR x) s = s x" |
  "pbval (NEG b) s = (\<not> pbval b s)" |
  "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
  "pbval (OR b1 b2 ) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR _)       = True" |
  "is_nnf (NEG (VAR _)) = True" |
  "is_nnf (NEG _)       = False" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR  b1 b2) = (is_nnf b1 \<and> is_nnf b2)"


fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = (VAR x)" |
  "nnf (NEG (VAR p)) = (NEG (VAR p))" |
  "nnf (NEG (NEG p)) = nnf p" |
  "nnf (NEG (AND p q)) = OR (nnf (NEG p)) (nnf (NEG q))" |
  "nnf (NEG (OR p q)) = AND (nnf (NEG p)) (nnf (NEG q))" |
  "nnf (AND p q) = AND (nnf p) (nnf q)" |
  "nnf (OR p q) = OR (nnf p) (nnf q)"

lemma "(pbval (nnf b) s = pbval b s)"
  apply(induction rule: nnf.induct)
  apply(auto)
  done

lemma "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
  apply(auto)
  done

fun andb :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "andb p (OR h t) = OR (andb p h) (andb p t)" |
  "andb (OR h t) p = OR (andb h p) (andb t p)" |
  "andb p q = AND p q"

lemma pbval_andb: "pbval (andb a b) s = pbval (AND a b) s"
  apply (induction a b rule:andb.induct)
  apply (auto)
  done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = VAR x" |
  "dnf_of_nnf (NEG p) = NEG p" |
  "dnf_of_nnf (OR p q) = OR (dnf_of_nnf p) (dnf_of_nnf q)" |
  "dnf_of_nnf (AND p q) = andb (dnf_of_nnf p) (dnf_of_nnf q)"

theorem "pbval (dnf_of_nnf p) s = pbval p s"
  apply (induction p)
  apply (auto simp add: pbval_andb)
  done

fun is_no_or :: "pbexp \<Rightarrow> bool" where
  "is_no_or (VAR x) = True" |
  "is_no_or (NEG p) = True" |
  "is_no_or (AND p q) = ((is_no_or p) \<and> (is_no_or q))" |
  "is_no_or (OR p q) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (VAR x) = True" |
  "is_dnf (NEG p) = True" |
  "is_dnf (AND p q) = ((is_no_or p) \<and> (is_no_or q))" |
  "is_dnf (OR p q) = ((is_dnf p) \<and> (is_dnf q))"

lemma isdnf_andb: "is_dnf p \<Longrightarrow> is_dnf q \<Longrightarrow> is_dnf (andb p q)"
  apply (induction p q rule:andb.induct)
  apply (auto)
  done


theorem "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply (induction b)
  apply (auto simp add: isdnf_andb)
  done



end
