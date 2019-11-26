#use "conversions.ml";;

(* triplets is (i,l,h) *)
(* ROBDD is (T, H) *)
type triplet = TR of int * int * int;;
type robdd = R of int * ((int, triplet) Hashtbl.t) * ((triplet, int) Hashtbl.t);;

(* Initializing a robdd *)
let init useless = 
    let t_tab = Hashtbl.create 10000 in
    let h_tab = Hashtbl.create 10000 in
    let _a = Hashtbl.add t_tab 0 (TR (1000, -1, -1)) in
    let _a = Hashtbl.add t_tab 1 (TR (1000, -1, -1)) in
    R (2, t_tab, h_tab)
;;

let add rob trip = match rob with R (next, t_tab, h_tab) ->
    let _a = Hashtbl.add t_tab next trip in
    R (next + 1, t_tab, h_tab)
;;

let lookupT rob u = match rob with R (next, t_tab, h_tab) ->
    Hashtbl.find t_tab u
;;

let insert rob trip u = match rob with R (next, t_tab, h_tab) ->
    Hashtbl.add h_tab trip u
;;

(* let member rob trip = match rob with R (next, t_tab, h_tab) ->
    Hashtbl.find  *)

(* Returns the robdd, node_id *)
let mk rob trip = 
    match rob with R (next, t_tab, h_tab) ->
    match trip with TR (i, l, h) -> 
    (* Redundant *)
    if l = h then (rob, l) else
    (* Already present *)
    try (rob, Hashtbl.find h_tab trip) with Not_found -> 
    (* Add new triplet *)
    let rob = add rob trip in
    let u = next in
    let _a = insert rob trip u in
    (rob, u)
;;


(* Building the ROBDD *)
let build t = 
    (* Initialize robdd *)
    let rob = init 0 in
    (* local build *)
    let rec build rob t i = 
        if not (vbl_present t) then
            if truth t = false then (rob, 0) else (rob, 1)
        else
            let (rob, v0) = build rob (subst t i F) (i+1) in
            let (rob, v1) = build rob (subst t i T) (i+1) in
            mk rob (TR (i, v0, v1))
    in
    build rob t 1
;;