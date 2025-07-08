theory ex01
imports Main
begin

value "2 + (2 :: nat)"
value "(2:: nat) + 5 * 3"

lemma "(x::nat) + y = y + x"
apply auto
done

lemma "(x :: nat) + (y + z) = (x + y) + z"
apply auto
done

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
    "count [] _ = 0" |
    "count (x#xs) x' = (if x = x' then Suc (count xs x') else count xs x')"

value "count [] (0::nat)"
value "count [2,2,2,1] (2::nat)"

theorem "count xs x <= length xs"
    by (induct xs) auto

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
    "snoc [] x = [x]" |
    "snoc (x#xs) x' = x # (snoc xs x')"

value "snoc [1, 2] (3 :: nat)"

lemma "snoc [] c = [c]"
    by auto

lemma "snoc [1 :: nat, 2, 3] 4 = [1, 2, 3, 4]"
    by simp

fun reverse :: "'a list \<Rightarrow> 'a list" where
    "reverse [] = []" |
    "reverse (x # xs) = snoc (reverse xs) x"

value "reverse [1 :: nat, 2, 3]"

lemma reverse_snoc[simp]:
    "reverse (snoc xs x) = x # (reverse xs)"
    apply(induct xs)
    apply auto
    done

theorem "reverse (reverse xs) = xs"
    apply(induct xs)
    apply auto
    done