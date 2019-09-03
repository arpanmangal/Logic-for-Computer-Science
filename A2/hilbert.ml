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
        let extract_gamma pft = match pft with
            | Ass(g, _p) -> g
            | K(g, _p) -> g
            | S(g, _p) -> g
            | R(g, _p) -> g
            | MP(g, _p, _pft1, _pft2) -> g
        in
        let extract_prop pft = match pft with
            | Ass(_g, p) -> p
            | K(_g, p) -> p
            | S(_g, p) -> p
            | R(_g, p) -> p
            | MP(_g, p, _pft1, _pft2) -> p
        in
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

