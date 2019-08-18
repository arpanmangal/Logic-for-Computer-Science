(* Assignment 0 : Syntax and Semantics of Propositional Logic *)

(* Terminology:
prop ::= T | F | L of string
        | Not (p)
        | And (p1, p2) | Or (p1, p2)
        | Impl (p1, p2) | Iff (p1, p2)
*)

(* Loading modules *)
module SS = Set.Make(String);;

(* prop definition *)
type prop = 
    | T
    | F
    | L of string
    | Not of prop
    | And of prop * prop
    | Or of prop * prop
    | Impl of prop * prop
    | Iff of prop * prop
    ;;

(* height of proposition *)
let rec ht p = match p with
    | T -> 0
    | F -> 0
    | L (x) -> 0
    | Not (q) -> 1 + (ht q)
    | And (q1, q2) -> 1 + (max (ht q1) (ht q2))
    | Or (q1, q2) -> 1 + (max (ht q1) (ht q2))
    | Impl (q1, q2) -> 1 + (max (ht q1) (ht q2))
    | Iff (q1, q2) -> 1 + (max (ht q1) (ht q2))
    ;;

(* Size of proposition *)
let rec size p = match p with
    | T -> 1
    | F -> 1
    | L (x) -> 1
    | Not (q) -> 1 + (size q)
    | And (q1, q2) -> 1 + (size q1) + (size q2)
    | Or (q1, q2) -> 1 + (size q1) + (size q2)
    | Impl (q1, q2) -> 1 + (size q1) + (size q2)
    | Iff (q1, q2) -> 1 + (size q1) + (size q2)
    ;;

(* Letters in a proposition *)
let rec letters p = match p with
    | T -> SS.empty
    | F -> SS.empty
    | L (x) -> SS.singleton x
    | Not (q) -> letters q
    | And (q1, q2) -> SS.union (letters q1) (letters q2)
    | Or (q1, q2) -> SS.union (letters q1) (letters q2)
    | Impl (q1, q2) -> SS.union (letters q1) (letters q2)
    | Iff (q1, q2) -> SS.union (letters q1) (letters q2)
    ;;

(* Printing the set *)
let print_set s = 
    SS.iter print_endline s;;

(* Prepending string to set of strings *)
let concat s1 s2 =
    String.concat s1 ["";s2];;

let prepend_string str set = 
    SS.map (concat str) set;;

(* sub-proposition *)
let rec subprop_at p1 p2 = if p1 = p2 then SS.singleton "" else
    match p2 with
    | T -> SS.empty
    | F -> SS.empty
    | L (x) -> SS.empty
    | Not (q) -> prepend_string "n" (subprop_at p1 q)
    | And (q1, q2) -> SS.union (prepend_string "0" (subprop_at p1 q1)) (prepend_string "1" (subprop_at p1 q2))
    | Or (q1, q2) -> SS.union (prepend_string "0" (subprop_at p1 q1)) (prepend_string "1" (subprop_at p1 q2))
    | Impl (q1, q2) -> SS.union (prepend_string "0" (subprop_at p1 q1)) (prepend_string "1" (subprop_at p1 q2))
    | Iff (q1, q2) -> SS.union (prepend_string "0" (subprop_at p1 q1)) (prepend_string "1" (subprop_at p1 q2))
    ;;
    (* | Not (q) -> if (q = p) then (prepend_string "0" (subprop_at p1 q)) else (subprop_at p1 q) *)

(* truth of prop *)
let rec truth p rho = match p with
    | T -> true
    | F -> false
    | L (x) -> rho x
    | Not (q) -> not (truth q rho)
    | And (q1, q2) -> (truth q1 rho) && (truth q2 rho)
    | Or (q1, q2) -> (truth q1 rho) || (truth q2 rho)
    | Impl (q1, q2) -> (not (truth q1 rho)) || (truth q2 rho)
    | Iff (q1, q2) -> (truth (Impl (q1, q2)) rho) && (truth (Impl (q2, q1)) rho)
    ;;

(* Converting to NNF *)
let rec nnf p = match p with
    | T -> T
    | F -> F
    | L(x) -> L(x)
    | And(q1, q2) -> And(nnf(q1), nnf(q2))
    | Or(q1, q2) -> Or(nnf(q1), nnf(q2))
    | Impl (q1, q2) -> Or (nnf(Not q1), nnf(q2))
    | Iff (q1, q2) -> And ( nnf(Impl (q1,q2)), nnf(Impl(q2,q1)) )
    | Not T -> F
    | Not F -> F
    | Not (L x) -> Not (L x)
    | Not (Not q) -> nnf q
    | Not (And (q1, q2)) -> Or (nnf(Not q1), nnf(Not q2))
    | Not (Or (q1, q2)) -> And (nnf(Not q1), nnf(Not q2))
    | Not (Impl (q1, q2)) -> And (nnf(q1), nnf(Not q2))
    | Not (Iff (q1, q2)) -> Or ( nnf(Not(Impl(q1, q2))), nnf(Not(Impl(q2, q1))) )
    ;;

(* Converting to DNF *)
let dnf p =
    let rec nnf_to_dnf p = match p with
        | Or (q1, q2) -> Or (nnf_to_dnf(q1), nnf_to_dnf(q2))
        | And (Or(q1, q2), q3) -> Or (
            nnf_to_dnf(And(q1, q3)),
            nnf_to_dnf(And(q2, q3))
        )
        | And (q1, Or(q2, q3)) -> Or (
            nnf_to_dnf(And(q1, q2)),
            nnf_to_dnf(And(q1, q3))
        )
        | _ -> p
    in
    nnf_to_dnf (nnf p)
    ;;


(* Converting to CNF *)
let cnf p =
    let rec nnf_to_cnf p = match p with
        | And (q1, q2) -> And (nnf_to_cnf(q1), nnf_to_cnf(q2))
        | Or (And(q1, q2), q3) -> And (
            nnf_to_cnf(Or(q1, q3)),
            nnf_to_cnf(Or(q2, q3))
        )
        | Or (q1, And(q2, q3)) -> And (
            nnf_to_cnf(Or(q1, q2)),
            nnf_to_cnf(Or(q1, q3))
        )
        | _ -> p
    in
    nnf_to_cnf (nnf p)
    ;;
