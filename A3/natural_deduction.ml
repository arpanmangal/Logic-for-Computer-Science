(* Assignment 3: Natural Deduction Proof System *)

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

(* definition of ndprooftree *)
type ndprooftree =
    | Hyp of gamma * prop
    | TI of gamma
    | ImpliesI of gamma * prop * ndprooftree
    | ImpliesE of gamma * prop * ndprooftree * ndprooftree
    | NotInt of gamma * prop * ndprooftree
    | NotClass of gamma * prop * ndprooftree
    | AndI of gamma * prop * ndprooftree * ndprooftree
    | AndEL of gamma * prop * ndprooftree
    | AndER of gamma * prop * ndprooftree
    | OrIL of gamma * prop * ndprooftree
    | OrIR of gamma * prop * ndprooftree
    | OrE of gamma * prop * ndprooftree * ndprooftree * ndprooftree
;;

(* Helper function *)
let extract_gamma pft = match pft with
    | Hyp (g, p) -> g
    | TI (g) -> g
    | ImpliesI (g, p, pft1) -> g
    | ImpliesE (g, p, pft1, pft2) -> g
    | NotInt (g, p, pft1) -> g
    | NotClass (g, p, pft1) -> g
    | AndI (g, p, pft1, pft2) -> g
    | AndEL (g, p, pft1) -> g
    | AndER (g, p, pft1) -> g
    | OrIL (g, p, pft1) -> g
    | OrIR (g, p, pft1) -> g
    | OrE (g, p, pft1, pft2, pft3) -> g
;;

let extract_prop pft = match pft with
    | Hyp (g, p) -> p
    | TI (g) -> T
    | ImpliesI (g, p, pft1) -> p
    | ImpliesE (g, p, pft1, pft2) -> p
    | NotInt (g, p, pft1) -> p
    | NotClass (g, p, pft1) -> p
    | AndI (g, p, pft1, pft2) -> p
    | AndEL (g, p, pft1) -> p
    | AndER (g, p, pft1) -> p
    | OrIL (g, p, pft1) -> p
    | OrIR (g, p, pft1) -> p
    | OrE (g, p, pft1, pft2, pft3) -> p
;;


(* Checking the validity of ndprooftree*)
let rec valid_ndprooftree pft = match pft with
    | Hyp (g, p) -> List.mem p g
    | TI (g) -> true
    | ImpliesI (g, p, pft1) -> 
        if (valid_ndprooftree pft1 = false) then false else
        (match p with
        | Impl(p1, q1) -> 
            let g' = extract_gamma pft1 in
            let q2 = extract_prop pft1 in
            if difference g' g <> [p1] then false
            else if q1 <> q2 then false
            else true
        | _ -> false)
    | ImpliesE (g, p, pft1, pft2) ->
        if (valid_ndprooftree pft1 = false) then false else
        if (valid_ndprooftree pft2 = false) then false else
        let q1 = p in
        if extract_gamma pft1 <> g then false
        else if extract_gamma pft2 <> g then false
        else 
            let p1 = extract_prop pft2 in
            if extract_prop pft1 <> Impl(p1, q1) then false
            else true
    | NotInt (g, p, pft1) ->
        if (valid_ndprooftree pft1 = false) then false else 
        if g <> extract_gamma pft1 then false
        else if extract_prop pft1 <> F then false
        else true
    | NotClass (g, p, pft1) ->
        if (valid_ndprooftree pft1 = false) then false else
        let g' = extract_gamma pft1 in
        let np1 = Not (p) in
        let np2 = (match p with
            | Not (p') -> p'
            | _ -> Not (p)
        ) in
        if (not_equal (union g [np1]) g') && (not_equal (union g [np2]) g') then false 
        (* let notp = (difference g' g) in *)
        (* if List.length notp <> 1 then false else *)
        (* let notp = (match notp with *)
            (* | x::[] -> x *)
            (* | _ -> L "randomness") in *)
        (* if ((notp <> Not (p)) && (Not (notp) <> p)) then false *)
        else if extract_prop pft1 <> F then false
        else true
    | AndI (g, p, pft1, pft2) -> 
        if (valid_ndprooftree pft1 = false) then false else
        if (valid_ndprooftree pft2 = false) then false else
        (match p with
        | And(p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_gamma pft2 <> g then false
            else if extract_prop pft1 <> p1 then false
            else if extract_prop pft2 <> q1 then false
            else true
        | _ -> false)
    | AndEL (g, p, pft1) -> 
        if (valid_ndprooftree pft1 = false) then false else
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | And(p1, q1) -> if p = p1 then true else false
            | _ -> false)
    | AndER (g, p, pft1) ->
        if (valid_ndprooftree pft1 = false) then false else
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | And(p1, q1) -> if p = q1 then true else false
            | _ -> false)
    | OrIL (g, p, pft1) -> 
        if (valid_ndprooftree pft1 = false) then false else
        (match p with
        | Or (p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_prop pft1 = p1 then true else false
        | _ -> false)
    | OrIR (g, p, pft1) ->
        if (valid_ndprooftree pft1 = false) then false else
        (match p with
        | Or (p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_prop pft1 = q1 then true else false
        | _ -> false)
    | OrE (g, p, pft1, pft2, pft3) ->
        if (valid_ndprooftree pft1 = false) then false else
        if (valid_ndprooftree pft2 = false) then false else
        if (valid_ndprooftree pft3 = false) then false else
        let r = p in
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | Or (p1, q1) ->
                if not_equal (union g [p1]) (extract_gamma pft2) then false
                else if not_equal (union g [q1]) (extract_gamma pft3) then false
                (* else if difference (extract_gamma pft3) g <> [q1] then false *)
                else if extract_prop pft2 <> r then false
                else if extract_prop pft3 <> r then false
                else true
            | _ -> false)
;;


(* Padding *)
let rec replace_gamma pft newGamma = match pft with
    | Hyp (g, p) -> Hyp (newGamma, p)
    | TI (g) -> TI (newGamma)
    | ImpliesI (g, p, pft1) -> ImpliesI (newGamma, p, pft1)
    | ImpliesE (g, p, pft1, pft2) -> ImpliesE (newGamma, p, pft1, pft2)
    | NotInt (g, p, pft1) -> NotInt (newGamma, p, pft1)
    | NotClass (g, p, pft1) -> NotClass (newGamma, p, pft1)
    | AndI (g, p, pft1, pft2) -> AndI (newGamma, p, pft1, pft2)
    | AndEL (g, p, pft1) -> AndEL (newGamma, p, pft1)
    | AndER (g, p, pft1) -> AndER (newGamma, p, pft1)
    | OrIL (g, p, pft1) -> OrIL (newGamma, p, pft1)
    | OrIR (g, p, pft1) -> OrIR (newGamma, p, pft1) 
    | OrE (g, p, pft1, pft2, pft3) -> OrE (newGamma, p, pft1, pft2, pft3)
;;

let rec pad pft delta =
    let _a = assert (valid_ndprooftree pft) in
    let g = extract_gamma pft in
    let newGamma = union g delta in
    let padded_pft = replace_gamma pft newGamma in
    let _a = assert (valid_ndprooftree padded_pft) in
    padded_pft
;;


(* Pruning *)
let prune pft = 
    let rec find_delta pft = match pft with
        | Hyp (g, p) -> [p]
        | TI (g) -> []
        | ImpliesI (g, p, pft1) -> find_delta pft1
        | ImpliesE (g, p, pft1, pft2) -> union (find_delta pft1) (find_delta pft2)
        | NotInt (g, p, pft1) -> find_delta pft1
        | NotClass (g, p, pft1) -> find_delta pft1
        | AndI (g, p, pft1, pft2) -> union (find_delta pft1) (find_delta pft2)
        | AndEL (g, p, pft1) -> find_delta pft1
        | AndER (g, p, pft1) -> find_delta pft1
        | OrIL (g, p, pft1) -> find_delta pft1
        | OrIR (g, p, pft1) -> find_delta pft1
        | OrE (g, p, pft1, pft2, pft3) -> union (find_delta pft1) (union (find_delta pft2) (find_delta pft3))
    in
    let delta = find_delta pft in
    let pruned_pft = replace_gamma pft delta in
    let _a = assert (valid_ndprooftree pruned_pft) in
    pruned_pft
;;


(* Graft function *)
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
    let empty_q_map = fun (_ : prop) -> if (true = false) then Hyp(gam, F) else raise Q_NOT_FOUND in
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
            | Hyp (g, p) -> q_map p
            | TI (g) -> TI (g)
            | ImpliesI (g, p, pft1) -> ImpliesI (g, p, stich pft1)
            | ImpliesE (g, p, pft1, pft2) -> ImpliesE (g, p, stich pft1, stich pft2)
            | NotInt (g, p, pft1) -> NotInt (g, p, stich pft1)
            | NotClass (g, p, pft1) -> NotClass (g, p, stich pft1)
            | AndI (g, p, pft1, pft2) -> AndI (g, p, stich pft1, stich pft2)
            | AndEL (g, p, pft1) -> AndEL (g, p, stich pft1)
            | AndER (g, p, pft1) -> AndER (g, p, stich pft1)
            | OrIL (g, p, pft1) -> OrIL (g, p, stich pft1)
            | OrIR (g, p, pft1) -> OrIR (g, p, stich pft1)
            | OrE (g, p, pft1, pft2, pft3) -> OrE (g, p, stich pft1, stich pft2, stich pft3)
        in
        let spft = stich pft in
        let _a = assert (valid_ndprooftree spft) in
        spft
;;
