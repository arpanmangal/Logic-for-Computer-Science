(* Assignment 4 *)

#use "natural_deduction.ml"

exception Normalized;;
let rec find_rpair r_pft = 
    let rpair = match r_pft with
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
    in
    let _a = assert (valid_ndprooftree rpair) in
    rpair
;;


(* Simplifying the given r-pair *)
exception INVALID_TREE;;

(* Finding the proof of q given proofs of gam,p |- q and gam |- p*)
let rec change_gamma pft newGamma = 
    let _a = assert (valid_ndprooftree pft) in
    let padded_pft = (match pft with
        | Hyp (g, p) -> Hyp (newGamma, p)
        | TI (g) -> TI (newGamma)
        | ImpliesI (g, Impl(p, q), pft1) -> ImpliesI (newGamma, p, pad pft1 (union newGamma [p]))
        | ImpliesE (g, p, pft1, pft2) -> ImpliesE (newGamma, p, pad pft1 newGamma, pad pft2 newGamma)
        | NotInt (g, p, pft1) -> NotInt (newGamma, p, pad pft1 newGamma)
        | NotClass (g, p, pft1) -> NotClass (newGamma, p, pad pft1 (union newGamma [p]))
        | AndI (g, p, pft1, pft2) -> AndI (newGamma, p, pad pft1 newGamma, pad pft2 newGamma)
        | AndEL (g, p, pft1) -> AndEL (newGamma, p, pad pft1 newGamma)
        | AndER (g, p, pft1) -> AndER (newGamma, p, pad pft1 newGamma)
        | OrIL (g, p, pft1) -> OrIL (newGamma, p, pad pft1 newGamma)
        | OrIR (g, p, pft1) -> OrIR (newGamma, p, pad pft1 newGamma) 
        | OrE (g, p, pft1, pft2, pft3) -> OrE (newGamma, p, pad pft1 newGamma, pad pft2 newGamma, pad pft3 newGamma)
        | _ -> raise INVALID_TREE
    ) in
    let _a = assert (valid_ndprooftree padded_pft) in
    padded_pft
;;

let rec simple_pft_q pft_pq pft_p new_gam = 
    let p = extract_prop pft_p in
    let simple_tree = match pft_pq with
        | TI (old_gam) -> TI (new_gam)
        | Hyp (old_gam, q) -> if p = q then change_gamma pft_p new_gam else Hyp (new_gam, q)
        | ImpliesI (old_gam, Impl(p', q'), pft') ->
            ImpliesI (new_gam, Impl(p', q'), 
                simple_pft_q pft' pft_p (union new_gam [p']))
        | ImpliesE (old_gam, q, pft1, pft2) ->
            ImpliesE (new_gam, q,
                simple_pft_q pft1 pft_p new_gam, simple_pft_q pft2 new_gam)
        | NotInt (old_gam, p, pft1) ->
            NotInt (new_gam, p, simple_pft_q pft1 pft_p new_gam)
        | NotClass (old_gam, p, pft1) ->
            NotClass (new_gam, p, simple_pft_q pft1 pft_p (union new_gam [Not p]))
        | AndI (old_gam, pq, pft1, pft2) ->
            AndI (new_gam, pq, simple_pft_q pft1 pft_p new_gam, simple_pft_q pft2 pft_p new_gam)
        | AndEL (old_gam, p, pft1) ->
            AndEL (new_gam, p, simple_pft_q pft1 new_gam)
        | AndER (old_gam, q, pft1) ->
            AndER (new_gam, q, simple_pft_q pft1 new_gam)
        | OrIL (old_gam, pq, pft1) -> OrIL (new_gam, pq, simple_pft_q pft1 new_gam)
        | OrIR (old_gam, pq, pft1) -> OrIR (new_gam, pq, simple_pft_q pft1 new_gam) 
        | OrE (old_gam, r, pft1, pft2, pft3) ->
            let (p, q) = (match extract_prop pft1 with
                    | Or (p, q) -> p, q
                    | _ -> raise INVALID_TREE
                ) in
            OrE (new_gam, r, 
                simple_pft_q pft1 new_gam, 
                simple_pft_q pft2 (union new_gam [p]), 
                simple_pft_q pft3 (union new_gam [q])
            )
        | _ -> raise INVALID_TREE
    in
    let _a = assert (valid_ndprooftree simple_tree) in
    simple_tree
;;

let rec simplify1 pft = 
    let simple_tree = match pft with
        | AndEL (gam, p, pft) -> (match pft with
                | AndI (gam, pq, pft_p, pft_q) -> pft_p
                | _ -> raise INVALID_TREE
            )
        | AndER (gam, q, pft) -> (match pft with
                | AndI (gam, pq, pft_p, pft_q) -> pft_q
                | _ -> raise INVALID_TREE
            )
        | ImpliesE (gam, q, pft1, pft2) -> (match pft1 with
                | ImpliesI (gam, pIMPq, pft') -> simple_pft_q pft' pft2 gam
                | _ -> raise INVALID_TREE
            )
        | Or (gam, r, pft1, pft2, pft3) ->
            let p, q = (match extract_prop pft1 with
                | Or (p, q) -> (p, q)
                | _ -> raise INVALID_TREE
            ) in
            (match pft1 with 
                | OrIL (gam, pq, pft) -> simple_pft_q pft2 pft gam
                | OrIR (gam, pq, pft) -> simple_pft_q pft3 pft gam
                | _ -> raise INVALID_TREE
            )
        | _ -> raise INVALID_TREE
    in
    let _a = assert (valid_ndprooftree simple_tree) in
    simple_tree
;;


(* Fully normalizing the tree *)
