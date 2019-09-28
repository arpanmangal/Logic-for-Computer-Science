(* Assignment 4 *)

#use "natural_deduction.ml"

exception Normalized;;
let rec find_rpair r_pft = match r_pft with
    | Hyp (gam, p) -> raise Normalized
    | TI (gam) -> raise Normalized
    | ImpliesI (gam, p, pft1) -> find_rpair (pft1)
    | ImpliesE (gam, q, pft1, pft2) -> (match pft1 with
            | ImpliesI (gam', pq, pft) -> r_pft
            | _ -> try find_rpair pft1
                   with Normalized -> find_rpair pft2 
        )
    | NotInt (gam, p, pft) -> find_rpair pft
    | NotClass (gam, p, pft) -> find_rpair pft
    | AndI (gam, p, pft1, pft2) ->
        (try find_rpair pft1
        with Normalized -> find_rpair pft2)
    | AndEL (gam, p, pft) -> (match pft with
            | AndI (gam', pq, pft1, pft2) -> r_pft
            | _ -> find_rpair pft
        )
    | AndER (gam, p, pft) -> (match pft with
            | AndI (gam', pq, pft1, pft2) -> r_pft
            | _ -> find_rpair pft
        )
    | OrIL (gam, p, pft) -> find_rpair pft
    | OrIR (gam, p, pft) -> find_rpair pft
    | OrE (gam, p, pft1, pft2, pft3) -> (match pft1 with
            | OrIL (gam', p', pft) -> r_pft
            | OrIR (gam', p', pft) -> r_pft
            | _ -> 
                (try find_rpair pft1
                with Normalized -> (
                    try find_rpair pft2
                    with Normalized -> find_rpair pft3
                ))
        )
;;