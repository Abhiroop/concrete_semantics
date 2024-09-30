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

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
  apply (induction t)
   apply(auto)
  done


fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

lemma "div2 n = n div 2"
  apply(induction n rule: div2.induct)
    apply(auto)
  done

(* Ex 2.6 *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil" |
  "contents (Node l x r) = Cons x (app (contents l) (contents r))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l x r) = x + sum_tree l + sum_tree r"



fun sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list Nil = 0"|
  "sum_list (Cons x xs) = x + sum_list xs"

lemma sum_lemma_aux [simp] : "sum_list (app xs ys) = sum_list xs + sum_list ys"
  apply(induction xs)
   apply(auto)
  done

lemma "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

(* Ex 2.7 *)
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Tip = Nil" |
  "pre_order (Node l x r) = app (Cons x (pre_order l)) (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Tip = Nil" |
  "post_order (Node l x r) = snoc (app (post_order l) (post_order r)) x"

lemma snoc_cons_aux [simp] : "snoc xs x = app xs (Cons x Nil)"
  apply(induction xs)
   apply(auto)
  done

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

(* Ex 2.8 *)
fun map_list :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_list f Nil = Nil" |
  "map_list f (Cons x xs) = Cons (f x) (map_list f xs)"


fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse x Nil = Nil" |
  "intersperse x (Cons a (Cons b xs)) = Cons a (Cons x (intersperse x (Cons b xs)))" |
  "intersperse x xs = Nil"

lemma "map_list f (intersperse a xs) = intersperse (f a) (map_list f xs)"
  apply(induction xs rule: intersperse.induct)
    apply(auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev Nil ys = ys" |
"itrev (Cons x xs) ys = itrev xs (Cons x ys)"

lemma itrev_app [simp] : "itrev xs ys = app (rev xs) ys"
  apply (induction xs arbitrary: ys)
  apply (auto)
  done

lemma "itrev xs Nil = rev xs"
  apply(induction xs)
  apply(auto)
  done

(* Ex 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 3 4"

lemma "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(auto)
  done

(* Ex 2.10 *)
datatype tree0 = Tip0 | Node0 tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip0 = 0" |
  "nodes (Node0 t1 t2) = 1 + (nodes t1) + (nodes t2)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node0 t t )"

value "explode 2 (Node0 Tip0 Tip0)"



end