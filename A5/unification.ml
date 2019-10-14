(* Terms, Substitution and Unification *)

#use "helper.ml";;

(* Variable, symbol and term definition *)
type variable = Var of string;;
type symbol = Sym of string * int;; (* symbol * arity *)
type term = V of variable | Node of symbol * (term list);;

(* Signature *)
type signature = symbol list;;

let rec check_sig signat = match signat with
    | [] -> true
    | (x::xs) -> (match x with
        Sym (name, arity) -> if arity < 0 then false else not (List.mem x xs) && (check_sig xs)
    )
;;

(* Terms *)
let rec wfterm signat t = match t with
    | V (var) -> true
    | Node (sym, l) -> (match sym with
        Sym (name, arity) -> (List.mem sym signat) && (List.length l = arity) && (foldl andT true (List.map (wfterm signat) l))
    )
;;


(* Computing height, size and vars *)
let rec ht t = match t with
    | V (var) -> 0
    | Node (sym, []) -> 0
    | Node (sym, l) -> 1 + (foldl max 0 (List.map ht l))
;;

let rec size t = match t with
  | V (var) -> 1
  | Node (sym, []) -> 1
  | Node (sym, l) -> 1 + (foldl add 0 (List.map size l))
;;

let rec vars t = match t with
  | V (var) -> [var]
  | Node (sym, []) -> []
  | Node (sym, l) -> foldl union [] (List.map vars l)
;;


(* Representation for substitution function sigma *)
(* As a list of ordered pairs of (var, subs) *)
type sigma = (variable * term) list;;


(* Substitution sigList applied to t *)
let rec subst sigList t = match t with
    | V (var) -> 
        (* Search the list for vbl *)
        let rec search l = match l with
            | [] -> V (var)
            | (x::xs) -> (match x with
                (vbl, t') -> if (var = vbl) then t' else search xs
            )
        in
        search sigList
    | Node (sym, []) -> Node (sym, [])
    | Node (sym, l) -> Node (sym, List.map (subst sigList) l)
;;

(* Composition: sig2 applied after sig1
  if x belongs to dom (sig1) then sig = sig2 (sig1 x) else sig1 x *)
let compose sig1 sig2 =
    let sig2sigma subsPair = (match subsPair with
        (var, t) -> (var, subst sig2 t)    
    ) in
    (List.map sig2sigma sig1) @ sig2
;;


(* Most General Unifier *)
exception NOT_UNIFIABLE;;
let rec mgu_foldl f sigma l1 l2 = match l1, l2 with
    | [], [] -> sigma
    | x::xs, y::ys ->
        let sigmai = f (subst sigma x) (subst sigma y) in
        mgu_foldl f (compose sigma sigmai) xs ys
    | _ -> raise NOT_UNIFIABLE
;;

let rec mgu t1 t2 = match t1, t2 with
    | V var1, V var2 -> if var1 = var2 then [] else [(var1, V var2)]
    | V var1, Node (sym, []) -> [(var1, Node (sym, []))]
    | Node (sym, []), V var2 -> [(var2, Node (sym, []))]
    | V var1, Node (sym, l) ->
        let varList = vars (Node (sym, l)) in
        if List.mem var1 varList then raise NOT_UNIFIABLE else [(var1, Node (sym, l))]
    (* | Node (sym1, []), Node (sym2, []) ->
        if sym1 <> sym2 then raise NOT_UNIFIABLE else [] *)
    | Node (sym, l), V var2 -> 
        let varList = vars (Node (sym, l)) in
        if List.mem var2 varList then raise NOT_UNIFIABLE else [(var2, Node (sym, l))]
    | Node (sym1, l1), Node (sym2, l2) ->
        if sym1 <> sym2 then raise NOT_UNIFIABLE else
        if l1 = [] && l2 = [] then [] else
        if l1 = [] || l2 = [] then raise NOT_UNIFIABLE else
        mgu_foldl mgu [] l1 l2
;;
