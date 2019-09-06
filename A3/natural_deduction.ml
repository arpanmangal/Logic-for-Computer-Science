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
let valid_ndprooftree pft = match pft with
    | Hyp (g, p) -> List.mem p g
    | TI (g) -> true
    | ImpliesI (g, p, pft1) -> (match p with
        | Impl(p1, q1) -> 
            let g' = extract_gamma pft1 in
            let q2 = extract_prop pft1 in
            if difference g' g <> [p1] then false
            else if q1 <> q2 then false
            else true
        | _ -> false)
    | ImpliesE (g, p, pft1, pft2) ->
        let q1 = p in
        if extract_gamma pft1 <> g then false
        else if extract_gamma pft2 <> g then false
        else 
            let p1 = extract_prop pft2 in
            if extract_prop pft1 <> Impl(p1, q1) then false
            else true
    | NotInt (g, p, pft1) -> 
        if g <> extract_gamma pft1 then false
        else if extract_prop pft1 <> F then false
        else true
    | NotClass (g, p, pft1) ->
        let g' = extract_gamma pft1 in
        if difference g' g <> [Not (p)] then false
        else if extract_prop pft1 <> F then false
        else true
    | AndI (g, p, pft1, pft2) -> (match p with
        | And(p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_gamma pft2 <> g then false
            else if extract_prop pft1 <> p1 then false
            else if extract_prop pft2 <> q1 then false
            else true
        | _ -> false)
    | AndEL (g, p, pft1) -> 
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | And(p1, q1) -> if p = p1 then true else false
            | _ -> false)
    | AndER (g, p, pft1) ->
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | And(p1, q1) -> if p = q1 then true else false
            | _ -> false)
    | OrIL (g, p, pft1) -> (match p with
        | Or (p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_prop pft1 = p1 then true else false
        | _ -> false)
    | OrIR (g, p, pft1) ->( match p with
        | Or (p1, q1) -> 
            if extract_gamma pft1 <> g then false
            else if extract_prop pft1 = q1 then true else false
        | _ -> false)
    | OrE (g, p, pft1, pft2, pft3) ->
        let r = p in
        if extract_gamma pft1 <> g then false
        else (match (extract_prop pft1) with
            | Or (p1, q1) ->
                if difference (extract_gamma pft2) g <> [p1] then false
                else if difference (extract_gamma pft3) g <> [q1] then false
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