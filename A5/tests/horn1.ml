(* Testing Resolution *)
#use "../resolution.ml";;

let p = Sym ("p", 1);;
let f = Sym ("f", 1);;
let x = Var "x";; let y = Var "y";;
let t1 = Node (p, [V x]);;
let t2 = Node (p, [Node (f, [V y])]);;

(* let s = mgu t1 t2;; *)
let l1 = P (t1);; let l2 = N (t2);;
let u = unify_literals l1 l2;;

let c1 = [l1];; let c2 = [l2];;
let c12 = unify_clauses c1 c2;;

let clist = [c1; c2];;
let r = resolve clist;;