theory Scratch
  imports Main
begin
datatype my_nat = Z | Succ my_nat

fun my_add :: "my_nat \<Rightarrow> my_nat \<Rightarrow> my_nat" where
"my_add Z n = n" |
"my_add (Succ m) n = Succ (my_add m n)"

lemma add_02: "my_add m Z = m"
  apply(induction m)
  apply(auto)
  done

datatype 'a my_list = Nil | Cons 'a "'a my_list"

fun app :: "'a my_list \<Rightarrow> 'a my_list \<Rightarrow> 'a my_list" where
"app Nil ys = ys" | 
"app (Cons x xs) ys = Cons x (app xs ys)"

fun my_rev :: "'a my_list \<Rightarrow> 'a my_list" where
"my_rev Nil = Nil" |
"my_rev (Cons x xs) = app (my_rev xs) (Cons x Nil)"

value "my_rev (Cons True (Cons False Nil))"

(* comment *)

lemma app_nil2 [simp]: "app xs Nil = xs"
  apply(induction xs)
  apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
  apply(auto)
  done 
 
lemma rev_app [simp]: "my_rev (app xs ys) = app (my_rev ys) (my_rev xs)"
  apply(induction xs)
  apply(auto)
  done
  
theorem rev_rev [simp]: "my_rev (my_rev xs) = xs"
  apply(induction xs)
  apply(auto)
  done

lemma add_assoc [simp]: "my_add x (my_add y z) = my_add (my_add x y) z"
  apply(induction x)
  apply(auto)
  done

lemma add_Z2 [simp]: "my_add x Z = x"
  apply(induction x)
  apply(auto)
  done

lemma add_Succ2 [simp]: "my_add x (Succ y) = Succ (my_add x y)"
  apply(induction x)
  apply(auto)
  done

lemma add_comm [simp]: "my_add x y = my_add y x"
  apply(induction x)
  apply(auto)
  done

(* Ex 2.2 *)
fun double :: "my_nat \<Rightarrow> my_nat" where
  "double Z = Z" |
  "double (Succ x) = Succ (Succ (double x))"

lemma double_add[simp] : "double x = my_add x x"
  apply(induction x)
  apply(auto)
  done

(* Ex 2.3 v1 *)
fun count_v1 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count_v1 x [] = 0" |
  "count_v1 x (y # ys) = (if x = y then Suc (count_v1 x ys) else (count_v1 x ys))"

lemma count_v1_bound [simp]: "count_v1 x y \<le> length y"
  apply(induction y)
  apply(auto)
  done

fun count_v2 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count_v2 x [] = 0" |
  "count_v2 x (y # ys) = (let n = count_v2 x ys in (if x = y then Suc n else n))"

lemma count_v2_bound [simp]: "count_v2 x y \<le> length y"
  apply(induction y)
  apply(auto)
  apply(simp add: Let_def)
  apply(auto)
  done

(* Ex 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
   "snoc [] y = y # []" |
   "snoc (x # xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
   "reverse [] = []" | 
   "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc[simp] : "reverse (snoc xs y) = y # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

lemma reverse_reverse : "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done


(* Ex 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (sum_upto n) + (Suc n)"

lemma sum_upto_f : "sum_upto n = n * (n+1) div 2"
  apply(induction n)
  apply(auto)
  done

(* 2.3 Type And Function Definitions *)

type_synonym string = "char list"

(* 2.3.1 Datatypes *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
  apply(induction t)
  apply(auto)
  done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

fun sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

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
"contents Tip = []" |
"contents (Node l a r) = (contents l) @ [a] @ (contents r)"

fun sum_list :: "nat list \<Rightarrow> nat" where
"sum_list [] = 0" |
"sum_list (x # xs) = x + (sum_list xs)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

lemma sum_list_concat : "sum_list (a @ b) = (sum_list a) + (sum_list b)"
  apply(induction a)
  apply(auto)
  done

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t rule: sum_tree.induct)
  apply(auto)
  apply(simp add:sum_list_concat)
  done

(* Ex 2.7 *)
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = a # ((pre_order l) @ (pre_order r))"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" | 
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ [x]"

lemma rev_concat [simp] : "rev (a @ b) = (rev b) @ (rev a)"
  apply(induction a)
  apply(auto)
  done

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

(* Ex 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [b] = [b]" |
"intersperse a (x # y # z) = (x # a # (intersperse a (y # z)))"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction a xs rule: intersperse.induct)
  apply(auto)
  done

(* 2.4 Induction Heuristics *)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = (rev xs) @ ys"
  apply(induction xs arbitrary: ys)
  apply(auto)
  done

(* Ex 2.9 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 y = y" |
"add (Suc x) y = Suc (add x y)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 y = y" |
"itadd (Suc x) y = itadd x (Suc y)"

lemma add_Suc2 [simp]: "add x (Suc y) = Suc (add x y)"
  apply(induction x)
  apply(auto)
  done

lemma "itadd m n = add m n"
  apply(induction m arbitrary:n)
  apply(auto)
  done

(* 2.5 Simplification *)

(* Ex. 2.10 *)
datatype tree0 = Leaf | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 0" |
"nodes (Node a b) = 1 + (nodes a) + (nodes b)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma explode_nodes [simp]: "nodes (explode x t) = (nodes t) * 2^x + 2^x - 1"
  apply(induction x arbitrary: t)
  apply(auto)
  apply(simp add:algebra_simps)
  done

lemma "nodes (explode n Leaf) = 2^n - 1"
  apply(auto)
  done


(* Ex. 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mult a b) x = (eval a x) * (eval b x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] y = 0" |
"evalp (x # xs) y = x + y * (evalp xs y)"

fun add_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeffs [] [] = []" |
"add_coeffs [] y = y" |
"add_coeffs x [] = x" |
"add_coeffs (x # xs) (y # ys) = (x + y) # (add_coeffs xs ys)"

fun mult_coeffs_const :: "int list \<Rightarrow> int \<Rightarrow> int list" where
"mult_coeffs_const [] y = []" |
"mult_coeffs_const (x # xs) y = (x * y) # (mult_coeffs_const xs y)"

fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeffs [] y = []" |
"mult_coeffs (x # xs) y = add_coeffs (mult_coeffs_const y x) (mult_coeffs xs (0 # y))"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add a b) = add_coeffs (coeffs a) (coeffs b)" |
"coeffs (Mult a b) = mult_coeffs (coeffs a) (coeffs b)"

lemma evalp_add [simp] : "evalp (add_coeffs a b) x = (evalp a x) + (evalp b x)"
  apply(induction rule: add_coeffs.induct)
  apply(auto)
  apply(simp add:algebra_simps)
  done

lemma evalp_mult_shift [simp] : "evalp (0 # p) x = x * (evalp p x)"
  apply(auto)
  done

lemma evalp_mult_const [simp] : "evalp (mult_coeffs_const p y) x = y * (evalp p x)"
  apply(induction p)
  apply(auto)
  apply(simp add:algebra_simps)
  done

lemma evalp_mult [simp] : "evalp (mult_coeffs a b) x = (evalp a x) * (evalp b x)"
  apply(induction rule: mult_coeffs.induct)
  apply(auto)
  apply(simp add:algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary:x)
  apply(auto) 
  done