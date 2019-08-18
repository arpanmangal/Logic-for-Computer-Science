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
    | Not (q) -> 1 + (ht q)
    | And (q1, q2) -> 1 + (ht q1) + (ht q2)
    | Or (q1, q2) -> 1 + (ht q1) + (ht q2)
    | Impl (q1, q2) -> 1 + (ht q1) + (ht q2)
    | Iff (q1, q2) -> 1 + (ht q1) + (ht q2)
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
(* let rec nnf p = match p with
    | L (x) -> L (x)
    | Not T -> F
    | Not F -> T
    | Not (Not q) -> q
    | Impl (q1, q2) -> nnf (Or( (Not q1), q2 ))
    | Iff (q1, q2) -> nnf (And( (Impl q1 q2), (Impl q2 q1) ))
    | _ -> p
    ;; *)