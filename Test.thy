theory Test
  imports Main
begin
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02  [simp] : "add m 0 = m"
  apply(induction m)
  apply(auto)
done

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

declare [[names_short]]

value "rev (Cons True (Cons False Nil))"

value "rev (Cons a (Cons b Nil))"


lemma app_Nil2 [simp] : "app xs Nil = xs"
  apply (induction xs)
   apply (auto)
  done
lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
   apply(auto)
  done

lemma rev_app [simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
   apply (auto)
  done

theorem rev_rev [simp] : "rev (rev xs) = xs"
  apply (induction xs)
   apply (auto)
  done

(*
[] is Nil,
x # xs is Cons x xs,
[x1 , . . ., xn ] is x 1 # . . . # x n # [], and
xs @ ys is app xs ys.
*)

value "1 + (2 :: nat)"

(* Ex 2.2 *)

lemma add_suc [simp] : "add a (Suc b) = Suc (add a b)"
  apply(induction a)
   apply (auto)
  done


theorem add_comm [simp] : "add a b = add b a"
  apply(induction a)
   apply (auto)
  done
 

theorem add_assoc : "add c (add a b) = add a (add b c)"
  apply (induction c)
   apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = (Suc (Suc (double m)))"

value "double 2"

theorem double_add [simp] : "double m = add m m"
  apply (induction m)
   apply(auto)
  done

(* Ex 2.3 *)


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ Nil = 0" |
  "count x (Cons y ys) = (if x = y then 1 else 0) + count x ys"

fun length :: "'a list \<Rightarrow> nat" where
  "length Nil = 0" |
  "length (Cons x xs) = 1 + length xs"

lemma count_length : "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* Ex 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = Cons x Nil" |
  "snoc (Cons a as) x = Cons a (snoc as x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = snoc (reverse xs) x"


lemma rev_snoc [simp] : "reverse (snoc xs x) = Cons x (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

theorem rev_rev_02 [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(* Ex 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (Suc n) + (sum_upto n)"



value "sum_upto 10"

value "(10 :: nat) div 3"

theorem sum_upto_lem : "sum_upto n = (n * (n + 1)) div 2"
  apply(induction n)
  apply(auto)
  done

end