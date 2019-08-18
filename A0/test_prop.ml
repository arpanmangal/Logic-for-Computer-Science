(* Testing of the propositions.ml code *)

#use "propositions.ml";;

(* Some letter assignments *)
exception DONT_CARE;;
let gen_rho vx vy vz l = match l with
    | "x" -> vx
    | "y" -> vy
    | "z" -> vz
    | _ -> raise DONT_CARE
    ;;

let rho1 = gen_rho true true true;;
let rho2 = gen_rho true false true;;
let rho3 = gen_rho false true true;;
let rho4 = gen_rho false false true;;
let rho5 = gen_rho true true false;;
let rho6 = gen_rho true false false;;
let rho7 = gen_rho false true false;;
let rho8 = gen_rho false false false;;


(* Propostion 1: p->(q->p) -- Tautology *)
let p1 = Impl(
    L("x"),
    Impl( L("y"), L("x") )
);;

(* Proposition 2: (p->(q->r))->((p->q)->(p->r)) --- Tautology*)
let p2 = Impl(
    Impl( L("x"), Impl(L("y"), L("z")) ),
    Impl( Impl(L("x"), L("y")), Impl(L("x"), L("z")) )
);;

(* Propostion 3: (p <-> T) and (p <-> F) -- Contradiction *)
let p3 = And(
    Iff( L("x"), T),
    Iff( L("x"), F)
);;

(* Proposition 4: F or (T -> F) -- Contradiction *)
let p4 = Or(
    F,
    Impl(T, F)
);;

(* Proposition 5: (x1 and T) or (x2 -> x1) -- Contingency *)
let p5 = Or(
    And( L("x"), T),
    Impl( L("y"), L("x"))
);;

(* Proposition 6: (x1->x2) and (x2->x1) -- Contingency *)
let p6 = And(
    Impl(L("x"), L("y")),
    Impl(L("y"), L("x"))
);;


(* Testing heights *)
assert (ht p1 = 2);;
assert (ht p2 = 3);;
assert (ht p3 = 2);;
assert (ht p4 = 2);;
assert (ht p5 = 2);;
assert (ht p6 = 2);;

(* Testing sizes *)
assert (size p1 = 5);;
assert (size p2 = 13);;
assert (size p3 = 7);;
assert (size p4 = 5);;
assert (size p5 = 7);;
assert (size p6 = 7);;

(* Printing letters in propositions *)
print_set(letters p1);;
print_set(letters p2);;
print_set(letters p3);;
print_set(letters p4);;
print_set(letters p5);;
print_set(letters p6);;

(* Testing truth with different rhos *)
assert (truth p1 rho1 = true);;
assert (truth p1 rho2 = true);;
assert (truth p1 rho3 = true);;
assert (truth p1 rho4 = true);;

assert (truth p2 rho1 = true);;
assert (truth p2 rho2 = true);;
assert (truth p2 rho3 = true);;
assert (truth p2 rho4 = true);;
assert (truth p2 rho5 = true);;
assert (truth p2 rho6 = true);;
assert (truth p2 rho7 = true);;
assert (truth p2 rho8 = true);;

assert (truth p3 rho1 = false);;
assert (truth p3 rho2 = false);;
assert (truth p3 rho3 = false);;
assert (truth p3 rho4 = false);;

assert (truth p4 rho1 = false);;
assert (truth p4 rho2 = false);;
assert (truth p4 rho3 = false);;
assert (truth p4 rho4 = false);;

assert (truth p5 rho1 = true);;
assert (truth p5 rho2 = true);;
assert (truth p5 rho3 = false);;
assert (truth p5 rho4 = true);;

assert (truth p6 rho1 = true);;
assert (truth p6 rho2 = false);;
assert (truth p6 rho3 = false);;
assert (truth p6 rho4 = true);;

(* Testing sub-propositions *)
let tree1 = let pimpliesq = Impl(L("p"), L("q")) in
    And(
        Or(pimpliesq, pimpliesq),
        Or((Not pimpliesq), F)
    );;
let pat1 = Impl(L("p"), L("q"));;

let tree2 = Or(
    T,
    Not(Iff(
        T,
        And(L("x"), T)
    ))
);;
let pat2 = T;;

let paths1 = subprop_at pat1 tree1;;
let paths2 = subprop_at pat2 tree2;;
print_set paths1;;
print_set paths2;;

let path3 = 
    try
        (subprop_at pat2 tree1)
    with 
            NotSubProp -> SS.singleton "exception success"
    ;;
print_set(path3);;