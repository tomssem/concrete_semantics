theory Exercises2
  imports Main
begin

(* Exercise 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_assoc[simp]: "add (add x y) z = add x (add y z)"
  apply (induction x)
   apply (auto)
  done

lemma add_r_0[simp]: "add x 0 = x"
  apply (induction x)
  apply (auto)
  done

lemma add_succ_1[simp]: "add x (Suc y) = Suc (add x y)"
  apply (induction x)
   apply (auto)
  done

lemma add_commut[simp]: "add x y = add y x"
  apply (induction x)
  apply (auto)
  done

(* Exercise 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ [] = 0" |
"count x (y # ys) = (if (x = y) then 1 else 0) +  (count x ys)"

theorem count_lt_length[simp]: "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

(* Exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]"|
"snoc (y#ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []"|
"reverse (x#xs) = snoc (reverse xs) x"

theorem rev_snoc[simp]: "reverse (snoc xs x) = (x#(reverse xs))"
  apply (induction xs)
   apply (auto)
  done

theorem rev_rev_id[simp] : "reverse (reverse x) = x"
  apply (induction x)
   apply (auto)
  done

(* Exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"|
"sum_upto (Suc n) = (Suc n) + (sum_upto n)"

theorem sum_upto_sol[simp]: "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done

(* Exercise 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents:: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil"|
"contents (Node l a r) = [a] @ (contents l) @ (contents r)"

fun sum_tree:: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"|
"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

theorem sum_tree_thm[simp]: "sum_tree t = sum_list (contents t)"
  apply (induction t)
   apply (auto)
  done

(* Exercise 2.7 *)

datatype 'a tree2 = Leaf 'a | Node2 "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leaf x) = Leaf x"|
"mirror2 (Node2 l a r) = (Node2 (mirror2 r) a (mirror2 l))"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node2 l a r) = a # (pre_order l @ pre_order r)"


fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node2 l a r) = post_order l @ post_order r @ [a]"

theorem rev_pre_is_pos[simp]: "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t rule: post_order.induct)
   apply (auto)
  done

(* Exercise 2.8 *)
fun intersperse:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []"|
"intersperse a [x] = [x]"|
"intersperse a (x1 # x2 # xs) = x1 # a # x2 # (intersperse a xs)"

theorem intersperse_map[simp]:
  "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply (auto)
  done

(* exercise 2.9 *)
fun itadd:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n"|
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add m n"
  apply (induction m arbitrary : n)
   apply (auto)
  done

(* exercise 2.10 *)
datatype tree0 = Nil0 | Node0 tree0 tree0

fun nodes::"tree0 \<Rightarrow> nat" where
"nodes Nil0 = 1"|
"nodes (Node0 l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t"|
"explode (Suc n) t = explode n (Node0 t t)"

definition explode_size :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
"explode_size n t = (2^n) * (1 + (nodes t)) - 1"

lemma [simp] : "nodes (explode n (Node0 t t)) = 1 + 2 * nodes (explode n t)"
  apply (induction n arbitrary : t)ifexp=Bc2bool|If ifexp ifexp ifexp|Less2aexp aexp
  apply (auto)
  done

lemma [simp] : "Suc (2 * 2 ^ n + nodes t * (2 * 2 ^ n) - Suc (Suc 0)) = 2 * 2 ^ n + nodes t * (2 * 2 ^ n) - Suc 0"
  apply (induction n)
   apply (auto)
  done


lemma "(nodes (explode n t)) = explode_size n t"
  apply (induction n)
   apply (simp_all add : explode_size_def)
  apply (simp add : algebra_simps)  
  done

datatype exp=Var|Const int|Add exp exp|Mult exp exp

value "(1 * (2::int))"

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const x) _ = x" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mult a b) x = (eval a x) * (eval b x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0"|
"evalp (c#cs) x = c * (x^(length (c#cs))) + (evalp cs x)"

fun degree :: "exp \<Rightarrow> int" where
"degree (Mult Var Var) = 2"|
"degree (Mult Var x) = 1 + (degree x)"|
"degree (Mult x Var) = 1 + (degree x)"|
"degree x = 0"

fun factor :: "exp \<Rightarrow> int" where
"factor (Mult x y) = (factor x) * (factor y)"|
"factor (Const x) = x"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs (Const x) = [x]"|
"coeffs (Add a b) = (factor a) # (coeffs b)"

theorem "evalp (coeffs e) x = eval e x"
  apply (induction e arbitrary : x rule : coeffs.induct)
  apply (simp_all)

end