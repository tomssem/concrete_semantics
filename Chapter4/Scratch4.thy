theory Scratch4
  imports Main
begin

(* Exercise 4.1 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}"|
"set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True"|
"ord (Node l a r) = ((ord l) \<and> (ord r) \<and>
  (case l of
  Tip \<Rightarrow> True |
  Node _ a1 _ \<Rightarrow> a1 < a) \<and>
  (case r of
  Tip \<Rightarrow> True |
  Node _ a2 _ \<Rightarrow> a < a2))"

fun ins :: "int tree \<Rightarrow> int \<Rightarrow> int tree" where
"ins Tip x = (Node Tip x Tip)"|
"ins (Node l y r)  x = (if (y = x)
                        then Node l y r
                        else (if (x < y)
                              then Node (ins l x) y r
                              else Node l y (ins r x)))"

lemma "set (ins t x) = {x} \<union> set t"
  apply (induction t)
   apply (auto)
  done

lemma "ord t \<Longrightarrow> ord (ins t i)"
  apply (induction t arbitrary: i)
   apply (auto split: tree.split)
  done

lemma "\<forall> x. \<exists> y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<forall> xs \<in> A. \<exists> ys. xs = ys @ ys \<Longrightarrow> us \<in> A \<Longrightarrow> \<exists> n . length us = n + n"
  by fastforce

lemma "\<forall> x y. T x y \<or> T y x \<Longrightarrow>
       \<forall> x y. A x y \<and> A y x \<longrightarrow> x = y \<Longrightarrow>
       \<forall> x y. T x y \<longrightarrow> A x y \<Longrightarrow>
       \<forall> x y. A x y \<longrightarrow> T x y"
  by blast

lemma "[a] = [b] \<Longrightarrow> a = b"
  by simp

lemma "(a :: nat) \<le> x + b \<Longrightarrow> 2 * x < c \<Longrightarrow> 2 * a + 1 \<le> 2 * b + c"
  by arith

inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0"|
evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

thm evSS
thm ev.intros
lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply (auto intro: evSS ev0)
  done

lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done


lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply (rule)
  apply (rule)
  apply (rule)
  done

value "ev0 \<Longrightarrow> ev(0+2) \<Longrightarrow>  ev((0+2) +2) = ev 4"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True"|
"evn (Suc 0) = False"|
"evn (Suc (Suc n)) = evn n"

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule: ev.induct)
  by (simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
    apply (auto  intro: ev0 evSS)
  done

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  by (simp_all add: ev0 evSS)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (auto intro: refl step)
  done

lemma star_trans': "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (assumption)
  apply (metis step)
  done

(* exercise 4.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
pal0: "palindrome []"|
pal1: "palindrome [x]"|
paln: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> palindrome (rev xs)"
  apply (induction rule : palindrome.induct)
  by (simp_all add: pal0 pal1 paln)

(* exercise 4.3 *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x"|
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_then_step[simp]:"\<lbrakk>star r x y; r y z\<rbrakk> \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (auto intro: refl step)
  done

lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
   apply (auto simp add: refl)
  done

lemma star'_then_step[simp]:"\<lbrakk>star' r y z; r x y\<rbrakk> \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
   apply (auto intro: refl' step')
  done

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (auto simp add: refl')
  done

(* exercise 4.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x"|
itern: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Succ n) x z"

lemma "star r x y \<Longrightarrow> \<exists> n . iter r n x y"
  apply (induction rule: star.induct)
   apply (auto intro: iter0 itern)
  done

(* exercise 4.5 *)
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S\<^sub>\<epsilon>: "S []"|
S\<^sub>1: "S x \<Longrightarrow> S (a # x @ [b])"|
S\<^sub>2: "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

inductive T :: "alpha list \<Rightarrow> bool" where
T\<^sub>\<epsilon>: "T []"|
T\<^sub>1: "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ [a] @ y @ [b])"

lemma T_imp_S: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  by (auto intro: S\<^sub>\<epsilon> S\<^sub>1 S\<^sub>2)

lemma T_app_nil:"T ([] @ [a] @ x @ [b]) \<Longrightarrow> T (a # x @ [b])"
  by auto

lemma helper: "\<lbrakk>T y; T x\<rbrakk> \<Longrightarrow> T (x @ y)"
  apply (induction rule: T.induct)
   apply (auto)
  using T\<^sub>1 by force

lemma S_imp_T: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (auto simp add: helper intro: T\<^sub>\<epsilon> T\<^sub>1 T_app_nil)
  done

lemma "S w = T w"
  apply (rule) using S_imp_T T_imp_S by auto

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n"|
"aval (V v) s = s v"|
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"
  
inductive aval_rel' :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
naval: "aval_rel' (N n) s n"|
vaval: "aval_rel' (V v) s (s v)"|
plaval: "aval_rel' a1 s v1 \<Longrightarrow>
         aval_rel' a2 s v2 \<Longrightarrow>
         aval_rel' (Plus a1 a2) s (v1 + v2)"

lemma "(aval_rel' e s v) \<Longrightarrow> (aval e s = v)"
  apply (induction rule: aval_rel'.induct)
  by auto

lemma "(aval e s = v) \<Longrightarrow> (aval_rel' e s v)"
  apply (induction e arbitrary: v)
    apply (auto intro: naval vaval plaval)
  done
  

end