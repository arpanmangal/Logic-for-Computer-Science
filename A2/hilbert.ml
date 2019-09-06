(* Assignment 2: Hilbert Style Proof System *)

(* Terminology:
prop ::= T | F | L of string
        | Not (p)
        | And (p1, p2) | Or (p1, p2)
        | Impl (p1, p2) | Iff (p1, p2)
*)

#use "set.ml";;

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


let rec pad pft prop_set = 
    let _a = assert (valid_hprooftree pft) in
    match pft with
    | Ass (g, p) -> Ass ((union g prop_set), p)
    | K (g, p) -> K ((union g prop_set), p)
    | S (g, p) -> S ((union g prop_set), p)
    | R (g, p) -> R ((union g prop_set), p)
    | MP (g, p, pft1, pft2) -> 
        let padded_pft1 = pad pft1 prop_set in
        let padded_pft2 = pad pft2 prop_set in
        let padded_pft = MP ((union g prop_set), p, padded_pft1, padded_pft2) in
        let _a = assert (valid_hprooftree padded_pft) in
        padded_pft
;;
    

let prune pft = 
    let rec find_delta pft = match pft with
        | Ass (g, p) -> [p]
        | K (g, p) -> []
        | S (g, p) -> []
        | R (g, p) -> []
        | MP (g, p, pft1, pft2) -> union (find_delta pft1) (find_delta pft2)
    in
    let delta = find_delta pft in
    let rec replace_gamma pft = match pft with
        | Ass (g, p) -> Ass (delta, p)
        | K (g, p) -> K (delta, p)
        | S (g, p) -> S (delta, p)
        | R (g, p) -> R (delta, p)
        | MP (g, p, pft1, pft2) -> MP (delta, p, (replace_gamma pft1), (replace_gamma pft2))
    in
    let pruned_pft = replace_gamma pft in
    let _a = assert (valid_hprooftree pruned_pft) in
    pruned_pft
;;


(* graft function *)
exception Q_NOT_FOUND;;
exception EMPTY_PFT_LIST;;
let extract_one_gamma pft_list = match pft_list with
    | [] -> raise EMPTY_PFT_LIST
    | x::xs -> extract_gamma x
;;

let q_pft_map pft_list gam =
    let rec make_q_map q_map pft_list = match pft_list with
        | [] -> q_map
        | x::xs -> 
            let _a = assert ((extract_gamma x) = gam) in
            let prop_x = extract_prop x in
            let new_map = fun q -> if q = prop_x then x else q_map q in
            make_q_map new_map xs
    in 
    let empty_q_map = fun (_ : prop) -> if (true = false) then S(gam, F) else raise Q_NOT_FOUND in
    make_q_map empty_q_map pft_list
;;

let graft pft pft_list =
    let delta = extract_gamma pft in
    let _a = assert (List.length delta = List.length pft_list) in
    if pft_list = [] then
        let _a = assert (delta = []) in
        pft
    else
        let gam = extract_one_gamma pft_list in
        let q_map = q_pft_map pft_list gam in
        let rec stich pft = match pft with
            | Ass (g, p) -> q_map p
            | K (g, p) -> K (gam, p)
            | S (g, p) -> S (gam, p) 
            | R (g, p) -> R (gam, p)
            | MP (g, p, pft1, pft2) -> MP(gam, p, (stich pft1), (stich pft2))
        in
        let spft = stich pft in
        let _a = assert (valid_hprooftree spft) in
        spft
;;

(* dedthm function *)
let pft_p_imp_p p gam =
    let q = F in
    let pp = Impl(p, p) in
    let qp = Impl(q, p) in
    let p_qp = Impl(p, qp) in
    let qp_p = Impl(qp, p) in
    let f1 = p_qp in
    let f2 = Impl(p, qp_p) in
    let f3 = Impl(p_qp, pp) in
    let f4 = Impl(f2, f3) in
    let pft = MP(
        gam,
        pp,
        MP(
            gam,
             f3,
            S(gam, f4),
            K(gam, f2)
        ),
        K(gam, f1)
    )
    in
    let _valid = assert (valid_hprooftree pft) in
    pft
;;

let rec dedthm pft p = 
    let gam = extract_gamma pft in
    let _a = assert (List.mem p gam) in
    let newGam = remove_element gam p in
    let q = extract_prop pft in
    if p = q then
        pft_p_imp_p p newGam
    else
        let pq = Impl(p, q) in
        let q_pq = Impl(q, pq) in
        let pft_q_pq = K (newGam, q_pq) in
        match pft with
            | Ass (g, q) ->
                let pft_q = Ass (newGam, q) in
                MP(newGam, pq, pft_q_pq, pft_q)
            | K (g, q) -> 
                let pft_q = K (newGam, q) in
                MP(newGam, pq, pft_q_pq, pft_q)
            | S (g, q) -> 
                let pft_q = S (newGam, q) in
                MP(newGam, pq, pft_q_pq, pft_q)
            | R (g, q) -> 
                let pft_q = R (newGam, q) in
                MP(newGam, pq, pft_q_pq, pft_q)
            | MP (g, q, pft1, pft2) -> 
                let r = extract_prop pft2 in
                let rq = extract_prop pft1 in
                let _a = assert(Impl(r, q) = rq) in
                let p_rq = Impl(p, rq) in
                let pr = Impl(p, r) in
                let pq = Impl(p, q) in
                let pr_pq = Impl(pr, pq) in
                let prq_prpq = Impl(p_rq, pr_pq) in
                let pft_p_rq = dedthm pft1 p in
                let pft_pr = dedthm pft2 p in
                let pft_prq_prpq = S(newGam, prq_prpq) in
                let pft_pr_pq = MP(newGam, pr_pq, pft_prq_prpq, pft_p_rq) in
                let pft_pq = MP(newGam, pq, pft_pr_pq, pft_pr) in
                let _a = assert (valid_hprooftree pft_pq) in
                pft_pq
;; 