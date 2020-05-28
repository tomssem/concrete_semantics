theory Scratch3
  imports Main
begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) _ = n"|
"aval (V v) s = s v"|
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"


value "aval (Plus (N 3) (V ''x'')) ((\<lambda>x.0)(''x'':=7))"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x.0"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n"|
"asimp_const (V x) = V x"|
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
  (N n1, N n2) \<Rightarrow> N (n1 + n2)|
  (b1,b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)"|
"plus (N i) a = (if i = 0 then a else Plus (N i) a)"|
"plus a (N i) = (if i = 0 then a else Plus a (N i))"|
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 rule : plus.induct)
              apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n"|
"asimp (V x) = V x"|
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
    apply (auto)
  apply (simp add : aval_plus)
  done

(* Exercise 3.1 *)
fun optimal:: "aexp \<Rightarrow> bool" where
"optimal (N _) = True"|
"optimal (V _) = True"|
"optimal (Plus (N _) (N _)) = False"|
"optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

lemma "optimal (asimp_const a)"
  apply (induction a rule : optimal.induct)
        apply(auto split: aexp.split)
  done

(* Exercise 3.2 *)
fun plus_complete:: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus_complete (N i1) (N i2) = N (i1 + i2)"|
"plus_complete (N i1) (Plus (V v) (N i2)) = Plus (V v) (N (i1 + i2))"|
"plus_complete (N i1) (Plus (N i2) (V v)) = Plus (V v) (N (i1 + i2))"|
"plus_complete (Plus (V v) (N i1)) (N i2) = Plus (V v) (N (i1 + i2))"|
"plus_complete (Plus (N i1) (V v)) (N i2) = Plus (V v) (N (i1 + i2))"|
"plus_complete a1 a2 = Plus a1 a2"

lemma aval_plus_complete: "aval (plus_complete a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 rule : plus_complete.induct)
                      apply (auto)
  done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n"|
"full_asimp (V v) = V v"|
"full_asimp (Plus a1 a2) = plus_complete (full_asimp a1) (full_asimp a2)"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
    apply (auto)
  apply (simp add : aval_plus_complete)
  done

end