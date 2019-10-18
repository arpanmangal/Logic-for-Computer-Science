(* Testing Resolution *)
#use "../resolution.ml";;

(* Predicates *)
let p = Sym ("p", 1);;
let q = Sym ("q", 2);;

let f = Sym ("f", 2);;
let g = Sym ("g", 2);;

let x = Var "x";; let y = Var "y";; let z = Var "z";;
let a = Var "a";; let b = Var "b";; 

let l1 = 
    let pr1 = Node (p, [V x]) in
    P pr1
;;
let l2 =
    let pr2 = Node (p, [V y]) in
    N pr2
;;
let l3 = 
    let t1 = V z in
    let t2 = Node (g, [V x; V z]) in
    let pr3 = Node (q, [t1; t2]) in
    P pr3
;;
let l4 = 
    let t1 = Node (f, [V a; V b]) in
    let t2 = Node (g, [V y; V z]) in
    let pr4 = Node (q, [t1; t2]) in
    N pr4
;;

let c1 = [l2; l4];;
let c2 = [l1];;
let c3 = [l3];;
let clist = [c1; c2; c3];;

let u = unify_literals l1 l2;;
let u = unify_literals l3 l4;;

let c12 = unify_clauses c1 c2;;
let c13 = unify_clauses c1 c3;;
let c31 = unify_clauses c3 c1;;

let r = resolve clist;;
let r = resolve [c1; c3];;