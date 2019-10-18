(* Testing Resolution *)
#use "../resolution.ml";;

(* Predicates *)
let ps = Sym ("p", 1);;
let qs = Sym ("q", 2);;
let ws = Sym ("w", 1);;

let a = Var "a";;
let b = Var "b";;
let c = Var "c";;

let p = Node (ps, [V a]);;
let q = Node (qs, [V a; V c]);;
let w = Node (ws, [V b]);;

(* let l1 = P t1;; let l2 = N t1;;
let t3 = P t2;; let l4 = N t2;;
let l5 = P t3;; let l6 = N t3;; *)

let c1 = [N p; N q];;
let c2 = [P w];;

let p = Node (ps, [V c]);;
let q = Node (qs, [V c; V c]);;
let w = Node (ws, [V a]);;

let c3 = [P p];;
let c4 = [P q; N w];;
let clist = [c1; c2; c3; c4];;

let r = resolve clist;;