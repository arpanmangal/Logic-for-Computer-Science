(* Assignment 2: Hilbert Style Proof System *)

(* Terminology:
prop ::= T | F | L of string
        | Not (p)
        | And (p1, p2) | Or (p1, p2)
        | Impl (p1, p2) | Iff (p1, p2)
*)


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

(* gamma defination *)
type gamma = prop list;;

(* definition of hprooftree and node *)
type hprooftree = 
    | Ass of gamma * prop
    | K of gamma * prop
    | S of gamma * prop
    | R of gamma * prop
    | MP of gamma * prop * hprooftree * hprooftree
;;


(* Helper function *)
let extract_gamma pft = match pft with
    | Ass(g, _p) -> g
    | K(g, _p) -> g
    | S(g, _p) -> g
    | R(g, _p) -> g
    | MP(g, _p, _pft1, _pft2) -> g
;;
let extract_prop pft = match pft with
    | Ass(_g, p) -> p
    | K(_g, p) -> p
    | S(_g, p) -> p
    | R(_g, p) -> p
    | MP(_g, p, _pft1, _pft2) -> p
;;


(* Checking validity of hprooftree *)
let rec valid_hprooftree pft = match pft with
    | Ass (gm, pr) -> List.mem pr gm
    | K (gm, pr) -> (match pr with
            | Impl(p1, Impl(q1, p2)) -> if (p1 = p2) then true else false
            | _ -> false
        )
    | S (gm, pr) -> (match pr with
            | Impl(
                Impl(p1, Impl(q1, r1)),
                Impl(Impl(p2, q2), Impl(p3, r2))
            ) -> if (p1 = p2) && (p2 == p3) && (q1 == q2) && (r1 == r2) then true else false
            | _ -> false
        )
    | R (gm, pr) -> (match pr with
            | Impl(
                Impl(Not(p1), Not(q1)),
                Impl(Impl(Not(p2), q2), p3)
            ) -> if (p1 == p2) && (p2 == p3) && (q1 == q2) then true else false
            | _ -> false
        )
    | MP (gm, pr, pft1, pft2) ->
        let match_gamma pft = (extract_gamma pft) = gm
        in
        if match_gamma pft1 = false then
            false
        else if match_gamma pft2 = false then
            false
        else
            let q = pr in
            let p = extract_prop pft2 in
            if extract_prop pft1 <> Impl(p, q) then
                false
            else if valid_hprooftree pft1 = false then
                false
            else if valid_hprooftree pft2 = false then
                false
            else
                true
;;


let pad pft prop_set = 
    let _a = assert (valid_hprooftree pft) in
    match pft with
    | Ass (g, p) -> Ass (g@prop_set, p)
    | K (g, p) -> K (g@prop_set, p)
    | S (g, p) -> Ass (g@prop_set, p)
    | R (g, p) -> R (g@prop_set, p)
    | MP (g, p, pft1, pft2) -> 
        let padded_pft1 = pad pft1 prop_set in
        let padded_pft2 = pad pft2 prop_set in
        MP (g@prop_set, p, padded_pft1, padded_pft2)
;;
    

let prune pft = 
    let rec find_delta pft = match pft with
        | Ass (g, p) -> [p]
        | K (g, p) -> []
        | S (g, p) -> []
        | R (g, p) -> []
        | MP (g, p, pft1, pft2) -> (find_delta pft1) @ (find_delta pft2)
    in
    let delta = find_delta pft in
    let rec replace_gamma pft = match pft with
        | Ass (g, p) -> Ass (delta, p)
        | K (g, p) -> K (delta, p)
        | S (g, p) -> S (delta, p)
        | R (g, p) -> R (delta, p)
        | MP (g, p, pft1, pft2) -> MP (delta, p, (replace_gamma pft1), (replace_gamma pft2))
    in
    replace_gamma pft
;;


(* dedthm function *)
(* let rec dedthm pft p = 
    let gam = extract_gamma pft in
    let _a = assert (p in gam) in
    let q = extract_prop p in
     *)