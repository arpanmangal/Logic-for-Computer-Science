(* Common code for Tests of A0 *)

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