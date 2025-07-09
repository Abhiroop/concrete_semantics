theory ex02
imports Main
begin

fun list_sum :: "nat list \<Rightarrow> nat" where
    "list_sum [] = 0" |
    "list_sum (x # xs) = x + list_sum xs"

value "list_sum [1, 2, 3]"

definition list_sum' :: "nat list \<Rightarrow> nat" where
    "list_sum' xs \<equiv> fold (+) xs 0"

value "list_sum' [1, 2, 4]"

lemma fold_add[simp] : 
    "fold (+) xs a = list_sum xs + a"
    apply(induct xs arbitrary: a)
    apply auto
    done

lemma "list_sum xs = list_sum' xs"
    apply (induct xs)
    apply (auto simp: list_sum'_def)
    done 

datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree"

fun inorder :: "'a ltree \<Rightarrow> 'a list" where
    "inorder (Leaf x) = [x]" |
    "inorder (Node left right) = inorder left @ inorder right"

fun fold_ltree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" where
    "fold_ltree f (Leaf x) s = f x s" |
    "fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)"

lemma "fold f (inorder t) s = fold_ltree f t s"
    apply (induction t arbitrary: s)
    apply (auto)
    done

fun mirror :: "'a ltree \<Rightarrow> 'a ltree" where
    "mirror (Leaf x) = Leaf x" |
    "mirror (Node left right) = (Node (mirror right) (mirror left))"

lemma "inorder t = rev (inorder (mirror t))"
    apply(induction t)
    apply auto
    done

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
    "shuffles xs [] = [xs]" |
    "shuffles [] ys = [ys]" |
    "shuffles (x#xs) (y#ys) = map (\<lambda>ss . x # ss) (shuffles xs (y#ys)) @
                              map (\<lambda>ss . y # ss) (shuffles (x#xs) ys)"

thm shuffles.induct

lemma "zs \<in> set (shuffles xs ys) \<Longrightarrow> length zs = length xs + length ys"
    apply(induction xs ys arbitrary: zs rule: shuffles.induct)
    apply auto
    done
