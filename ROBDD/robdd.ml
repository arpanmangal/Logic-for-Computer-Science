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

(* Applying a operation *)
type operator = AND | OR;;
let apply op ru1 ru2 =
    (* Initialize robdd *)
    let rob = init 0 in
    let g_tab = Hashtbl.create 10000 in

    (* extract u1 u2 *)
    match ru1 with (rob1, u1') ->
    match ru2 with (rob2, u2') ->

    (* App function *)
    let rec app rob u1 u2 = 
        (* if already calculated then use as is *)
        try (rob, Hashtbl.find g_tab (u1, u2)) with Not_found ->
        let result = 
            (* if both of them is 0 or 1 *)
            if (u1 = 0 || u1 = 1) && (u2 = 0 || u2 = 1) then
                let u = (match op with
                | AND -> if (u1 + u2 = 2) then 1 else 0
                | OR -> if (u1 + u2 = 0) then 0 else 1) in
                (rob, u)
            else
                match (lookupT rob1 u1) with TR(v1, l1, h1) ->
                match (lookupT rob2 u2) with TR(v2, l2, h2) ->
                if v1 = v2 then
                    (* Distribute on both *)
                    let (rob, v1') = app rob l1 l2 in
                    let (rob, v2') = app rob h1 h2 in
                    mk rob (TR (v1, v1', v2'))
                else if v1 > v2 then
                    (* v1 comes before *)
                    let (rob, v1') = app rob l1 v2 in
                    let (rob, v2') = app rob h1 v2 in
                    mk rob (TR (v1, v1', v2'))
                else
                    (* v1 comes after *)
                    let (rob, v1') = app rob v1 l2 in
                    let (rob, v2') = app rob v1 h2 in
                    mk rob (TR (v2, v1', v2'))
        in
        (* Add into G *)
        match result with (rob, u) ->
        let _i = Hashtbl.add g_tab (u1, u2) u in
        result
    in

    match rob1 with R(next1, t_tab1, h_tab1) ->
    match rob2 with R(next2, t_tab2, h_tab2) ->
    let result = app rob (next1 - 1) (next2 - 1) in
    result
;;


(* Restrict *)
let restrict ru j b =
    (* Extract robb, u *)
    match ru with (rob1, u) ->

    (* Initialize robdd *)
    let rob = init 0 in

    (* res function *)
    let rec res rob u =
        match (lookupT rob1 u) with TR(v1, l1, h1) ->
        if v1 > j then
            (* j is not my child *)
            (rob, u)
        else if v1 < j then 
            match (lookupT rob1 u) with TR(v1, l1, h1) ->
            let (rob, u1) = res rob l1 in
            let (rob, u2) = res rob h1 in
            mk rob (TR (v1, u1, u2)) 
        else if v1 = j && b = 0 then
            match (lookupT rob1 u) with TR(v1, l1, h1) ->
            res rob l1
        else 
            match (lookupT rob1 u) with TR(v1, l1, h1) ->
            res rob h1
    in
    res rob u
;;


(* Anysat *)
exception Error;;
type mapping = Mapp of int * int;;
let rec anysat ru = 
    (* Extract robdd, u *)
    match ru with (rob, u) ->

    if u = 0 then raise Error
    else if u = 1 then []
    else
        match (lookupT rob u) with TR(v, l, h) ->
        if l = 0 then (Mapp(v, 1)::(anysat (rob, h)))
        else (Mapp(v, 0)::(anysat (rob, h)))
;;

let rec allsat ru = 
    (* Extract robdd, u *)
    match ru with (rob, u) ->

    if u = 0 then []
    else if u = 1 then [[]]
    else
        match (lookupT rob u) with TR(v, l, h) ->
        let m0 = Mapp(v, 0) in
        let m1 = Mapp(v, 1) in
        let ass_low = allsat (rob, l) in
        let ass_high = allsat (rob, h) in
        (* ass is a list of list and returns a list of lists *)
        let rec lows ass = match ass with
            | [] -> []
            | x::xs -> (m0::x)::(lows xs)
        in
        let rec highs ass = match ass with
            | [] -> []
            | x::xs -> (m1::x)::(highs xs)
        in
        (lows ass_low) @ (highs ass_high)
;;

(* Simplify *)
let simplify du ru =
    (* Initialize robdd *)
    let rob = init 0 in

    let rec sim du ru rob =
        (* Extract d and u *)
        match ru with (rob_ru, u) ->
        match du with (rob_du, d) ->

        match (lookupT rob_du d) with TR(d_v, d_l, d_h) ->
        match (lookupT rob_ru u) with TR(u_v, u_l, u_h) ->

        if d = 0 then (rob, 0)
        else if u <= 1 then (rob, u)
        else if d = 1 then
            let (rob, u1) = sim (rob_du, d) (rob_ru, u_l) rob in
            let (rob, u2) = sim (rob_du, d) (rob_ru, u_h) rob in
            mk rob (TR (u_v, u1, u2)) 
        else if d_v = u_v then
            if d_l = 0 then sim (rob_du, d_h) (rob_ru, u_h) rob
            else if d_h = 0 then sim (rob_du, d_l) (rob_ru, u_l) rob
            else
                let (rob, u1) = sim (rob_du, d_l) (rob_ru, u_l) rob in
                let (rob, u2) = sim (rob_du, d_h) (rob_ru, u_h) rob in
                mk rob (TR (u_v, u1, u2))
        else if d_v < u_v then
            let (rob, u1) = sim (rob_du, d_l) (rob_ru, u) rob in
            let (rob, u2) = sim (rob_du, d_h) (rob_ru, u) rob in
            mk rob (TR (d_v, u1, u2))
        else
            let (rob, u1) = sim (rob_du, d) (rob_ru, u_l) rob in
            let (rob, u2) = sim (rob_du, d) (rob_ru, u_h) rob in
            mk rob (TR (u_v, u1, u2))
    in
    sim du ru rob
;;