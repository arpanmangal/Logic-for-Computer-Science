(* Testing Resolution *)
#use "../resolution.ml";;

(* Predicates *)
let ps = Sym ("p", 1);;
let qs = Sym ("q", 2);;

let a = Var "a";;
let b = Var "b";;
let c = Var "c";;
let f = Sym ("f", 2);;

let p = Node (ps, [V a]);;
let q = Node (qs, [V a; Node (f, [V c; V b])]);;

let c1 = [P p; P q];;
let c2 = [N p; P q];;
let c3 = [P p; N q];;
let c4 = [N p; N q];;
let clist = [c1; c2; c3; c4];;

let r = resolve clist;;
let r = resolve [c1; c2; c3];;
