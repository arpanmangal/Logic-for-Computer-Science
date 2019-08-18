(* Testing of the propositions.ml code *)

#use "propositions.ml";;

(* Some letter assignments *)
exception DONT_CARE;;
let rho1 l = match l with
    | "x" -> T
    | "y" -> T
    | "z" -> F
    | _ -> raise DONT_CARE
    ;;

let rho2 l = match l with
    | "x" -> F
    | "y" -> T
    | "z" -> F
    | _ -> raise DONT_CARE
    ;;

let rho3 l = match l with
    | "x" -> F
    | "y" -> F
    | "z" -> F
    | _ -> raise DONT_CARE
    ;;

let rho4 l = match l with
    | "x" -> T
    | "y" -> T
    | "z" -> T
    | _ -> raise DONT_CARE
    ;;

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
assert (ht p1) = 2;;
assert (ht p2) = 2;;
assert (ht p3) = 2;;
assert (ht p4) = 2;;
assert (ht p5) = 2;;
assert (ht p6) = 2;;

(* Testing sizes *)
assert (size p1) = 2;;
assert (size p2) = 2;;
assert (size p3) = 2;;
assert (size p4) = 2;;
assert (size p5) = 2;;
assert (size p6) = 2;;

(* Printing letters in propositions *)
print_set(letters p1);;
print_set(letters p2);;
print_set(letters p3);;
print_set(letters p4);;
print_set(letters p5);;
print_set(letters p6);;

(* Testing truth with different rhos *)
assert (truth p1 rho1) = T;;
assert (truth p1 rho2) = T;;
assert (truth p1 rho3) = T;;
assert (truth p1 rho4) = T;;
assert (truth p2 rho1) = T;;
assert (truth p2 rho2) = T;;
assert (truth p2 rho3) = T;;
assert (truth p2 rho4) = T;;
assert (truth p3 rho1) = F;;
assert (truth p3 rho2) = F;;
assert (truth p3 rho3) = F;;
assert (truth p3 rho4) = F;;
assert (truth p4 rho1) = F;;
assert (truth p4 rho2) = F;;
assert (truth p4 rho3) = F;;
assert (truth p4 rho4) = F;;

(* Testing sub-propositions *)
