(* Terminology:
prop ::= T | F | L of int
        | Not (p)
        | And (p1, p2) | Or (p1, p2)
        | Impl (p1, p2) | Iff (p1, p2)
*)

(* prop definition *)
type prop = 
    | T
    | F
    | L of int
    | Not of prop
    | And of prop * prop
    | Or of prop * prop
    | Impl of prop * prop
    | Iff of prop * prop
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
    | Not F -> T
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

(* Returns true if there are > 0 letters in p *)
let rec vbl_present p = match p with
    | T -> false
    | F -> false
    | L (v) -> true 
    | Not (q) -> vbl_present q
    | And (q1, q2) -> (vbl_present q1) || (vbl_present q2)
    | Or (q1, q2) -> (vbl_present q1) || (vbl_present q2)
    | Impl (q1, q2) -> (vbl_present q1) || (vbl_present q2)
    | Iff (q1, q2) -> (vbl_present q1) || (vbl_present q2)
;;

(* Truth value *)
let rec truth p = 
    let _a = assert (not (vbl_present (p))) in
    match p with
    | T -> true
    | F -> false
    | L(x) -> false
    | Not (q) -> not (truth q)
    | And (q1, q2) -> (truth q1) && (truth q2)
    | Or (q1, q2) -> (truth q1) || (truth q2)
    | Impl (q1, q2) -> (not (truth q1)) || (truth q2)
    | Iff (q1, q2) -> (truth (Impl (q1, q2))) && (truth (Impl (q2, q1)))
;;

(* Substitutions *)
let rec subst t vbl bool = match t with
    | T -> T
    | F -> F
    | L (v) -> if v = vbl then bool else L (v)
    | Not (q) -> Not (subst q vbl bool)
    | And (q1, q2) -> And (subst q1 vbl bool, subst q2 vbl bool)
    | Or (q1, q2) -> Or (subst q1 vbl bool, subst q2 vbl bool)
    | Impl (q1, q2) -> Impl (subst q1 vbl bool, subst q2 vbl bool)
    | Iff (q1, q2) -> Iff (subst q1 vbl bool, subst q2 vbl bool)
;;
