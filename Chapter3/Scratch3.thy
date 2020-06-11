theory Scratch3
  imports Main
begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n"|
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
  apply (induction a)
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

(* Exercise 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst v a  (N x) = (N x)"|
"subst v1 a (V v2) = (if (v1 = v2) then a else (V v2))"|
"subst v a (Plus e1 e2) = Plus (subst v a e1) (subst v a e2)"

lemma subst_lemma : "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
    apply(auto)
  done

lemma subst_equiv:"aval a\<^sub>1 s = aval a\<^sub>2 s \<Longrightarrow> aval (subst x a\<^sub>1 e) s = aval (subst x a\<^sub>2 e) s"
  apply (induction e)
    apply (auto)
  done

datatype aexp' = N' int | V' vname | Plus' aexp' aexp' | Times' aexp' aexp'

fun aval' :: "aexp' \<Rightarrow> state \<Rightarrow> val" where
"aval' (N' n) _ = n"|
"aval' (V' v) s = s v"|
"aval' (Plus' e1 e2) s = (aval' e1 s) + (aval' e2 s)"|
"aval' (Times' e1 e2) s = (aval' e1 s) * (aval' e2 s)"

fun plus' :: "aexp' \<Rightarrow> aexp' \<Rightarrow> aexp'" where
"plus' (N' n1) (N' n2) = N' (n1 + n2)"|
"plus' (N' n) e = (if (n = 0) then e else (Plus' (N' n) e))"|
"plus' e (N' n) = (if (n = 0) then e else (Plus' e (N' n)))"|
"plus' e1 e2 = Plus' e1 e2"

fun times' :: "aexp' \<Rightarrow> aexp' \<Rightarrow> aexp'" where
"times' (N' n1) (N' n2) = N' (n1 * n2)"|
"times' (N' n) e = (if n = 0
                  then (N' 0)
                  else (if n = 1
                       then e
                       else (Times' (N' n) e)))"|
"times' e (N' n) = (if n = 0
                  then (N' 0)
                  else (if n = 1
                       then e
                       else (Times' e (N' n))))"|
"times' e1 e2 = Times' e1 e2"

fun asimp' :: "aexp' \<Rightarrow> aexp'" where
"asimp' (N' n) = (N' n)"|
"asimp' (V' v) = (V' v)"|
"asimp' (Plus' e1 e2) = plus' e1 e2"|
"asimp' (Times' e1 e2) = times' e1 e2"

lemma aval_plus': "aval' (plus' a1 a2) s = aval' a1 s + aval' a2 s"
  apply (induction a1 rule : plus'.induct)
              apply (auto)
  done

lemma aval_times : "aval' (times' a1 a2) s = aval' a1 s * aval' a2 s"
  apply (induction a1 rule : times'.induct)
                      apply(auto)
  done

lemma "aval' (asimp' a) s = aval' a s"
  apply (induction a)
     apply (auto)
   apply (simp_all add: aval_plus' aval_times)
  done

datatype aexp2 = N2 int |
                 V2 vname |
                 Plus2 aexp2 aexp2 |
                 Times2 aexp2 aexp2 |
                 PostInc vname|
                 Div2 aexp2 aexp2
value "(1::nat, 2::nat)"
value "fst (1::nat, 2::nat)"
value "let x = 2::nat in x"
value "let (a, b) = (1::nat, 2::nat) in a"
value "(1::int) div (2::int)"

(* Argument application order is always first then second *)
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (PostInc v) s = Some (s v, s(v := (s v) + 1))"|
"aval2 (N2 n) s = Some (n, s)"|
"aval2 (V2 v) s = Some (s v, s)"|
"aval2 (Plus2 a1 a2) s = (case aval2 a1 s of
                         None \<Rightarrow> None |
                         Some (r1, s1) \<Rightarrow> 
                            (case aval2 a2 s1 of
                            None \<Rightarrow> None |
                            Some (r2, s2) \<Rightarrow> Some (r1 + r2, s2)))"|
"aval2 (Times2 a1 a2) s = (case aval2 a1 s of
                         None \<Rightarrow> None |
                         Some (r1, s1) \<Rightarrow> 
                            (case aval2 a2 s1 of
                            None \<Rightarrow> None |
                            Some (r2, s2) \<Rightarrow> Some (r1 * r2, s2)))"|
"aval2 (Div2 a1 a2) s = (case aval2 a1 s of
                         None \<Rightarrow> None |
                         Some (r1, s1) \<Rightarrow> 
                            (case aval2 a2 s1 of
                            None \<Rightarrow> None |
                            Some (r2, s2) \<Rightarrow> (if r2 = 0 then None else Some (r1 div r2, s2))))"

value "(snd (case (aval2 (N2 2) <>) of
        None \<Rightarrow> (0, <>) |
        Some (v, s) \<Rightarrow> (v, s))) ''x''"

value "(snd (case (aval2 (PostInc ''x'') <>) of
        None \<Rightarrow> (0, <>) |
        Some (v, s) \<Rightarrow> (v, s))) ''x''"

value "(snd (case (aval2 (Div2 (PostInc ''x'') (PostInc ''x'')) <''x'':=6>) of
        None \<Rightarrow> (0, <>) |
        Some (v, s) \<Rightarrow> (v, s))) ''x''"
value "(fst (case (aval2 (Div2 (PostInc ''x'') (PostInc ''x'')) <''x'':=6>) of
        None \<Rightarrow> (0, <>) |
        Some (v, s) \<Rightarrow> (v, s)))"

value "aval2 (Div2 (V2 ''x'') (N2 2)) <''x'':=6>"

(* Exercise 3.6 *)
datatype lexp=Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (Nl n) _ = n"|
"lval (Vl v) s = s v"|
"lval (Plusl l1 l2) s = (lval l1 s) + (lval l2 s)"|
"lval (LET v l1 l2) s = lval l2 (s(v:=(lval l1 s)))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = (N n)"|
"inline (Vl v) = (V v)"|
"inline (Plusl l1 l2) = Plus (inline l1) (inline l2)"|
"inline (LET v l1 l2) = subst v (inline l1) (inline l2)"



lemma inline_correct : "aval (inline l) s = lval l s"
  apply(induction l arbitrary:s)
     apply(auto)
  apply(simp add:subst_lemma)
  done

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v"|
"bval (Not b) s = (\<not>bval b s)"|
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)"|
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False"|
"not (Bc False) = Bc True"|
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b"|
"and b (Bc True) = b"|
"and (Bc False) b = Bc False"|
"and b (Bc False) = Bc False"|
"and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v"|
"bsimp (Not b) = not(bsimp b)"|
"bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)"|
"bsimp (Less a\<^sub>1 a\<^sub>2) = Less (asimp a\<^sub>1) (asimp a\<^sub>2)"

(* Exercise 3.7 *)
definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a\<^sub>1 a\<^sub>2 = And (Not (Less a\<^sub>1 a\<^sub>2)) (Not (Less a\<^sub>2 a\<^sub>1))"

value "bval (Eq (N 1) (N 1)) <>"
value "bval (Eq (N 1) (N 2)) <>"
value "bval (Eq (N 2) (N 1)) <>"

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b\<^sub>1 b\<^sub>2 = Not (And (Not b\<^sub>1) (Not b\<^sub>2))"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a\<^sub>1 a\<^sub>2 = Or (Eq a\<^sub>1 a\<^sub>2) (Less a\<^sub>1 a\<^sub>2)"

value "bval (Le (N 1) (N 1)) <>"
value "bval (Le (N 1) (N 2)) <>"
value "bval (Le (N 2) (N 1)) <>"

lemma "bval (Eq a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s = aval a\<^sub>2 s)"
  apply (auto simp add: Eq_def)
  done  

lemma "bval (Le a\<^sub>1 a\<^sub>2) s = ((aval a\<^sub>1 s) \<le> (aval a\<^sub>2 s))"
  apply (auto simp add: Le_def Or_def Eq_def)
  done

(* Exercise 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) _ = b"|
"ifval (Less2 a\<^sub>1 a\<^sub>2) s = ((aval a\<^sub>1 s) < (aval a\<^sub>2 s))"|
"ifval (If i\<^sub>1 i\<^sub>2 i\<^sub>3) s = (if (ifval i\<^sub>1 s) then (ifval i\<^sub>2 s) else (ifval i\<^sub>3 s))"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = Bc2 v"|
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)"|
"b2ifexp (And b\<^sub>1 b\<^sub>2) = If (b2ifexp b\<^sub>1) (b2ifexp b\<^sub>2) (Bc2 False)"|
"b2ifexp (Less a\<^sub>1 a\<^sub>2) = Less2 a\<^sub>1 a\<^sub>2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = Bc v"|
"if2bexp (Less2 a\<^sub>1 a\<^sub>2) = Less a\<^sub>1 a\<^sub>2"|
"if2bexp (If i\<^sub>1 i\<^sub>2 i\<^sub>3) = Or (And (if2bexp i\<^sub>1) (if2bexp i\<^sub>2))
                            (And (Not (if2bexp i\<^sub>1)) (if2bexp i\<^sub>3))"

lemma "ifval (b2ifexp b) s = bval b s"
  apply (induction b)
     apply (auto)
  done
lemma "bval (if2bexp i) s = ifval i s"
  apply (induction i)
    apply (auto simp add : Or_def)
  done

(* Exercise 3.8 *)
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"|
"pbval (NOT b) s = (\<not> pbval b s)"|
"pbval (AND b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<and> pbval b\<^sub>2 s)"|
"pbval (OR b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<or> pbval b\<^sub>2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR _) = True"|
"is_nnf (NOT (VAR _)) = True"|
"is_nnf (NOT _) = False"|
"is_nnf (AND b\<^sub>1 b\<^sub>2) = (is_nnf b\<^sub>1 \<and> is_nnf b\<^sub>2)"|
"is_nnf (OR b\<^sub>1 b\<^sub>2) = (is_nnf b\<^sub>1 \<or> is_nnf b\<^sub>2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR v) = VAR v"|
"nnf (NOT (VAR v)) = NOT (VAR v)"|
"nnf (NOT (NOT b)) = nnf b"|
"nnf (AND b\<^sub>1 b\<^sub>2) = AND (nnf b\<^sub>1) (nnf b\<^sub>2)"|
"nnf (NOT (AND b\<^sub>1 b\<^sub>2)) = OR (nnf (NOT b\<^sub>1)) (nnf (NOT b\<^sub>2))"|
"nnf (OR b\<^sub>1 b\<^sub>2) = OR (nnf b\<^sub>1) (nnf b\<^sub>2)"|
"nnf (NOT (OR b\<^sub>1 b\<^sub>2)) = AND (nnf (NOT b\<^sub>1)) (nnf (NOT b\<^sub>2))"

lemma "(pbval (nnf b) s = pbval b s)"
  apply (induction b rule:nnf.induct)
     apply(auto)
  done

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk"|
"exec1 (LOAD v) s stk = (s v) # stk"|
"exec1 ADD _ (j # i # stk) = (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk"|
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"|
"comp (V x) = [LOAD x]"|
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

lemma instr_app_stack:"exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s (exec is\<^sub>1 s stk)"
  apply (induction is\<^sub>1 arbitrary: stk)
   apply (auto)
  done

lemma "exec (comp a) s stk = aval a s # stk"
  apply (induction a arbitrary: stk)  
  apply(auto)
    apply (auto simp add: instr_app_stack)
  done

(* Exercise 3.10 *)
fun exec1' :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1' (LOADI n) _ stk = Some (n # stk)"|
"exec1' (LOAD v) s stk = Some ((s v) # stk)"|
"exec1' ADD _ (j # i # stk) = Some ((i + j) # stk)"|
"exec1' ADD _ _ = None"

fun exec' :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec' [] _ stk = Some stk"|
"exec' (i#is) s stk = (case (exec1' i s stk) of
                      None \<Rightarrow> None |
                      Some stk' \<Rightarrow> exec' is s stk')"

lemma instr_app_stack':"(exec' is\<^sub>1 s stk) = Some v \<Longrightarrow> exec' (is\<^sub>1 @ is\<^sub>2) s stk = exec' is\<^sub>2 s v"
  apply (induction is\<^sub>1 arbitrary: stk)
   apply (auto split:option.split)
  done


lemma "exec' (comp a) s stk = Some  (aval a s # stk)"
  apply (induction a arbitrary: stk)
    apply(auto simp add: instr_app_stack')
  done


(* Exercise 3.11 *)
type_synonym reg = nat

(* (ADD r\<^sub>1 r\<^sub>2) adds value in r\<^sub>1 and value in r\<^sub>2 and puts result in r\<^sub>1 *)
datatype rinstr = LDI int reg | LD vname reg | ADD reg reg

fun rexec1:: "rinstr \<Rightarrow> state \<Rightarrow> (reg\<Rightarrow>int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec1 (LDI i r) st regs  = regs(r := i)"|
"rexec1 (LD v r) st regs = regs(r := (st v))"|
"rexec1 (ADD r\<^sub>1 r\<^sub>2) st regs = regs(r\<^sub>1 := ((regs r\<^sub>1) + (regs r\<^sub>2)))"

fun rexec:: "rinstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec [] _ regs = regs"|
"rexec (i#is) st regs = rexec is st (rexec1 i st regs)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
"rcomp (N n) r = [LDI n r]" |
"rcomp (V x) r = [LD x r]" |
"rcomp (Plus e\<^sub>1 e\<^sub>2) r = (rcomp e\<^sub>1 r) @ (rcomp e\<^sub>2 (r+1)) @ [ADD r (r+1)]"

lemma rinstr_app_reg:"rexec (is\<^sub>1 @ is\<^sub>2) s r = rexec is\<^sub>2 s (rexec is\<^sub>1 s r)"
  apply (induction is\<^sub>1 arbitrary: r)
   apply (auto)
  done

lemma [simp]:"q > r \<Longrightarrow> (rexec (rcomp a1 q) s rs) r = rs r"
  apply (induction a1 arbitrary: r rs q)
    apply (auto simp add: rinstr_app_reg)
  done


lemma "rexec(rcomp a r) s rs r = aval a s"
  apply (induction a arbitrary: rs r)
  apply (auto)
  apply (auto simp add: rinstr_app_reg )
  done

end