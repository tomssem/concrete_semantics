theory Scratch2
  imports Main
begin
fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

fun add' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add' 0 n = n" |
"add' (Suc m) n = Suc (add' m n)"

lemma add_O2: "add' m 0 = m"
  apply (induction m)
   apply (auto)
  done

thm add_O2

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev' :: "'a list \<Rightarrow> 'a list" where
"rev' Nil = Nil" |
"rev' (Cons x xs) = app (rev' xs) (Cons x Nil)"

value "rev'(Cons True (Cons False Nil))"

value "rev' (Cons a (Cons b Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
   apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma rev_app [simp]: "rev' (app xs ys) = app (rev' ys) (rev' xs)"
  apply (induction xs)
   apply (auto)
  done

theorem rev_rev [simp]: "rev' (rev' xs) = xs"
  apply (induction xs)
   apply(auto)
  done

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map f Nil = Nil" |
"map f (Cons a as) = Cons (f a) (map f as)"

fun app' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app' Nil ys = ys" |
"app' (Cons x xs) ys = Cons x (app' xs ys)"

type_synonym string = "char list"

value "string = char list"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t"
  apply (induction t)
   apply (auto)
  done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] _ = None" |
"lookup ((a,b)#xs) x = (if (a = x)
                        then Some b
                        else (lookup xs x))"

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc(div2 n)"

lemma "div2(n) = n div 2"
  apply(induction n rule:div2.induct)
    apply (auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys     = ys"|
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma [simp]: "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary : ys)
   apply (auto)
  done

lemma "itrev xs [] = rev xs"
   apply (auto)
  done

end