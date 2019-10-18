(* Run "#use test.ml" in the REPL *)
#use "../unification.ml";;

let var1 = Var ("x");;
let var2 = Var ("y");;
let var3 = Var ("3");;
let var4 = Var ("false");;

(* Symbols *)
let plus = Sym ("add", 2);;
let minus = Sym ("sub", 2);;
let negation = Sym ("not", 1);;
let const1 = Sym ("1", 0);;
let const2 = Sym ("100", 0);;
let greaterThan = Sym ("ge", 2);;
let pair = Sym ("pair", 2);;

let symNeg = Sym ("ar", -1);;
let symN = Sym ("neg", -100);;

(* Signatures *)
let sig1 = [plus; minus];;
let sig2 = [pair; negation];;
let sig3 = [symNeg; negation];;
let sig4 = [symN; const1];;
let sig5 = [const1; const2];;
let sig6 = [const1; pair; const1];;
let math = [plus; minus; negation; const1; const2; pair; greaterThan];;

assert ((check_sig sig1 = true) && (check_sig sig2 = true) && (check_sig sig3 = false));;
assert ((check_sig sig4 = false) && (check_sig sig5 = true) && (check_sig sig6 = false) && (check_sig math = true));;


(* Terms *)
let term1 = V (var1);; (*true*)
let term2 = Node (plus, []);; (*false*)
let term3 = Node (const1, []);; (*true*)
let term4 = Node (const2, [term3]);; (*false*)

let term5 = Node (plus, [term3; term3]);; (*true*)
let term6 = Node (plus, [term3; term4]);; (*false*)
let term7 = Node (negation, [term6]);; (*false*)
let term8 = Node (negation, [term5]);; (*true*)
let term9 = Node (greaterThan, [term8; term3]);; (*true*)

let term10 = V (var4);; (*true*)
let term11 = Node (pair, [term1;term10]);; (*true*)
let term12 = Node (minus, [term11;term11]);; (*true*)
let term13 = Node (greaterThan, [term12; term9]);; (*true*)

assert ( (wfterm math term1 = true) && (wfterm math term2 = false) && (wfterm math term3 = true) && (wfterm math term4 = false));;
assert ( (wfterm math term5 = true) && (wfterm math term6 = false) && (wfterm math term7 = false) && (wfterm math term8 = true) && (wfterm math term9 = true));;
assert ( (wfterm math term10 = true) && (wfterm math term11 = true) && (wfterm math term12 = true) && (wfterm math term13 = true));;


(*testing ht, size, vars *)
assert ( (ht term10 = 0) && (ht term11 = 1) && (ht term12 = 2) && (ht term3 = 0) && (ht term5 = 1) && (ht term8 = 2) && (ht term9 = 3) && (ht term13 = 4));;
assert ( (size term10 = 1) && (size term11 = 3) && (size term12 = 7) && (size term3 = 1) && (size term5 = 3) && (size term8 = 4) && (size term9 = 6) && (size term13 = 14));;

assert ( (vars term10 = [var4]) && (vars term11 = [var1; var4]) && (vars term12 = [var1; var4]) );;
assert ( (vars term3 = []) && (vars term5 = []) && (vars term8 = []) && (vars term9 = []));;
assert ( (vars term13 = [var4; var1]));;

(* Testing Substitutions *)
let subs1 = (var1, term1);;
let subs2 = (var2, term1);;
let subs3 = (var1, term9);;
let subs5 = (var4, term11);;
let subs6 = (var4, term10);;

let sig1 = [subs1; subs2; subs3];;
let sig2 = [subs6; subs5; subs3];;
let sig3 = [subs2; subs5; subs1];;
let sig4 = compose sig1 sig2;;
let sig5 = compose sig3 sig4;;
let sig6 = [subs1; subs2];;

assert (subst [subs1] term1 = V (Var "x"));;
assert ( (subst sig6 term13 = term13) && (subst sig6 term12 = term12) && (subst sig6 term11 = term11) && (subst sig6 term10 = term10) && (subst sig6 term9 = term9) && (subst sig6 term8 = term8) && (subst sig6 term7 = term7) && (subst sig6 term6 = term6));;


(* Testing MGU *)

(* X with X *)
assert ( (mgu term13 term13) = []);;

(* X with Y *)
assert ( (mgu term13 (subst [( var1, V (var2) )] term13) ) = [( var1, V (var2) )]);;

(* X with c *)
assert ( (mgu term13 (subst [( var1, term3 )] term13) ) = [( var1, term3 )]);;

(* X with f without X *)
assert ( (mgu term13 (subst [( var1, term10 )] term13) ) = [( var1, V (var4) )]);;

(* X with f with X *)
try assert ( (mgu term13 (subst [( var1, term11 )] term13) ) = [])
with NOT_UNIFIABLE -> ();;

(* constant with same constant *)
assert ( mgu term3 term3 = []);;

(* Constant with other constant *)
try assert ( mgu (Node (const1, [])) (Node (const2, [])) = [])
with NOT_UNIFIABLE -> ();;

(* Constant with function *)
try assert ( (mgu term3 term8) = [])
with NOT_UNIFIABLE -> ();;

(* f with g *)
try assert ( (mgu term5 term9) = [])
with NOT_UNIFIABLE -> ();;

(* f with f *)
let term14 = subst [(var1, V (var2))] term13;; (* X -> Y *)
let term15 = subst [(var4, V (var3))] term14;; (* var4 -> var3 *)
assert (mgu term13 term15 = [(Var "x", V (Var "y")); (Var "false", V (Var "3"))]);;
assert (mgu term15 term13 = [(Var "y", V (Var "x")); (Var "3", V (Var "false"))]);;

(* Both branches with different substitutions *)
let term16 = Node (plus, [term13; term13]);;
let term17 = Node (plus, [term14; term15]);;

assert (mgu term16 term17 = [(Var "x", V (Var "y")); (Var "false", V (Var "3"))]);;
assert (mgu term17 term16 = [(Var "y", V (Var "x")); (Var "3", V (Var "false"))]);;