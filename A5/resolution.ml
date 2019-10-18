(* Code for Resolution *)
#use "unification.ml";;
#use "set.ml";;

type literal = P of term | N of term;;
type clause = literal list;;
type formula = clause list;;


(* Resolving two literals *)
exception NO_UNIF_LITERAL;;
let unify_literals l1 l2 = 
    match l1 with
    | P (t1) -> (match l2 with
        | P (t2) -> raise NO_UNIF_LITERAL
        | N (t2) -> try mgu t1 t2 with NOT_UNIFIABLE -> raise NO_UNIF_LITERAL )
    | N (t1) -> (match l2 with
        | N (t2) -> raise NO_UNIF_LITERAL
        | P (t2) -> try mgu t1 t2 with NOT_UNIFIABLE -> raise NO_UNIF_LITERAL )
;;

(* Resolving two clauses -- O(len(c1) * len(c2)) *)
exception NO_UNIF_CLAUSE;;
exception SIGMA_NOT_FOUND;;
let unify_clauses c1 c2 =
    let _a = assert (List.length c1 > 0 && List.length c2 > 0) in
    let rec unify_literal l c2 = match c2 with 
        | [] -> raise SIGMA_NOT_FOUND
        | x::xs -> 
            try 
                let sigma = unify_literals l x in
                (l, x, sigma)
            with NO_UNIF_LITERAL -> unify_literal l xs
    in
    let rec find_sigma c1 = match c1 with
        | [] -> raise NO_UNIF_CLAUSE
        | x::xs -> try unify_literal x c2 with SIGMA_NOT_FOUND -> find_sigma xs
    in
    let (l1, l2, sigma) = find_sigma c1 in
    let c12 = union c1 c2 in
    let c12 = difference c12 [l1; l2] in
    let apply_sigma l = match l with
        | P (t) -> P (subst sigma t)
        | N (t) -> N (subst sigma t)
    in
    List.map apply_sigma c12
;;
