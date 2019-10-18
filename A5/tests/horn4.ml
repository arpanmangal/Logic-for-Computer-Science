(* Testing Resolution *)
#use "../resolution.ml";;

(* Predicates *)
let ps = Sym ("p", 1);;
let qs = Sym ("q", 2);;
let ws = Sym ("w", 1);;
let vs = Sym ("v", 3);;

let a = Var "a";;
let b = Var "b";;
let c = Var "c";;
let f = Sym ("f", 2);;

let p = Node (ps, [V a]);;
let q = Node (qs, [V a; Node (f, [V c; V b])]);;
let w = Node (ws, [V b]);;
let v = Node (vs, [V a; Node (f, [V a; V c]); V c]);;

let c1 = [N p];;
let c2 = [N q];;
let c3 = [P p; N w];;
let c4 = [P w];;
let c5 = [P q; N v];;
let c6 = [P v];;
let clist = [c1; c2; c3; c5; c4];;
let r = resolve clist;;