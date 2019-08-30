(* Assignment 1 : Analytic Tableaux *)

(* Terminology:
prop ::= T | F | L of string
        | Not (p)
        | And (p1, p2) | Or (p1, p2)
        | Impl (p1, p2) | Iff (p1, p2)

node ::= {
        value: prop * bool
        examined: bool
        closed: bool
        num_desc: int
    }

tableaux ::= List of node IDs

Each node ID will correspond to a node and will be stored in a functional dictionary

nodes are numbered as strings s.t. prefixes of the string represent parents
and children are 0 or 1 appended to the current node number.
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

(* definition of node as a function *)
type nodeVal = Value of prop * bool;;
type node = {
    value : nodeVal;
    examined : bool;
    closed : bool;
    num_desc : int;
};;
let newNode p truth = {
    value = Value(p, truth);
    examined = false;
    closed = false;
    num_desc = 0;
};;
let nodeExamined aNode = {
    aNode with examined = true;
};;
let nodeClosed aNode = {
    aNode with closed = true;
};;
let nodeDesc aNode num_desc = {
    aNode with num_desc = num_desc;
};;
let getNodeProp aNode = 
    let aNodeVal = aNode.value in
    match aNodeVal with Value (p, t) -> p
;;
let getNodeTruth aNode = 
    let aNodeVal = aNode.value in
    match aNodeVal with Value (p, t) -> t
;;


(* definition of a tableaux *)
(* type tableaux = List of string;; *)
exception INVALID_NODE_ID;;
let emptyTab = fun (_ : string) -> if (true = false) then newNode T false else raise INVALID_NODE_ID;;
(* let emptyTab (_ : string) : node = (newNode T false);; *)
(* Can change the defaults *)
(* let addNodeInTab aTab key p truth =
    let aNewNode = (newNode p truth) in
    fun key' -> if key' = key then aNewNode else aTab key;; *)
let addNodeInTab aTab nodeID aNode =
    fun node_id -> if node_id = nodeID then aNode else aTab node_id
;;

(* Developing the tableaux *)
(* Helper functions *)
let concat s1 s2 =
    String.concat s1 ["";s2]
;;
let concat3 s1 s2 s3 =
    concat (concat s1 s2) s3
;;
let concat4 s1 s2 s3 s4 =
    concat (concat3 s1 s2 s3) s4
;;
let concat5 s1 s2 s3 s4 s5 =
    concat (concat4 s1 s2 s3 s4) s5
;;

let nList n = 
    if n = 0 then [] else
    let rec createList mx l = if mx <= 0 then l
        else 
        let mx1 = mx - 1 in
        match l with
        | [] -> createList mx1 [mx1]
        | x::xs -> createList mx1 (mx1::l)
    in
    createList n []
    ;;

let allPrefixes s = 
    let sLen = String.length s in
    if sLen = 0 then [] else
    if sLen = 1 then [""] else
    List.map (String.sub s 0) (nList sLen)
;;

(* Printing stuff *)
let rec print_prop p = match p with
    | T -> "T"
    | F -> "F"
    | L(x) -> concat3 "L(" x ")"
    | Not(q) -> concat3 "Not(" (print_prop q) ")"
    | And(q1, q2) -> concat5 "And(" (print_prop q1) "," (print_prop q2) ")"
    | Or(q1, q2) -> concat5 "Or(" (print_prop q1) "," (print_prop q2) ")"
    | Impl(q1, q2) -> concat5 "Impl(" (print_prop q1) "," (print_prop q2) ")"
    | Iff(q1, q2) -> concat5 "Iff(" (print_prop q1) "," (print_prop q2) ")"
;;

(* Printing of the tableaux *)
let print_bool b = 
    if b then "true" else "false"
;;
let print_tableaux aTab =
    let rec print_tab nodeID =
        let currNode = aTab nodeID in
        let _print_tab = match currNode.value with 
            | Value (p, t) -> Printf.printf "| ID - %s : prop = %s || truth = %s || closed = %s || examined = %s || num_desc = %d|\n" nodeID (print_prop p) (print_bool t) (print_bool currNode.closed) (print_bool currNode.examined) (currNode.num_desc)
        in
        if currNode.num_desc = 1 then 
            print_tab (concat nodeID "0")
        else if currNode.num_desc = 2 then
            let _print_left = print_tab (concat nodeID "0") in
            let _print_right = print_tab (concat nodeID "1") in
            ()
    in
    print_tab ""
;;

(* 1. Closing all paths from this node *)
let rec closePath aTab nodeID = 
    let currNode = aTab nodeID in
    let currClosedNode = nodeClosed currNode in
    let aTab = addNodeInTab aTab nodeID currClosedNode in
    if currNode.num_desc = 0 then aTab else
        let aTab = closePath aTab (concat nodeID "0") in
        if currNode.num_desc = 2 then 
            closePath aTab (concat nodeID "1")
        else
            aTab
    ;;

(* 2. Closing all the contradicting paths *)
let contrad_path aTab nodeID =
    let isContradiction nodeID1 nodeID2 =
        let node1 = aTab nodeID1 in
        let node2 = aTab nodeID2 in 
        if (((getNodeProp node1) = (getNodeProp node2)) && ((getNodeTruth node1) <> (getNodeTruth node2)))
        then true else false
    in
    let rec closeContradPaths aTab nodeID = 
        let currNode = aTab nodeID in
        let parents = allPrefixes nodeID in
        let f truth aNodeID = truth || (isContradiction aNodeID nodeID) in
        let isContraNode = (List.fold_left f false parents) in
        if isContraNode then 
            closePath aTab nodeID 
        else
            if currNode.num_desc = 0 then aTab else
                let aTab = closeContradPaths aTab (concat nodeID "0") in
                if currNode.num_desc = 2 
                then
                    closeContradPaths aTab (concat nodeID "1")
                else
                    aTab
    in
    closeContradPaths aTab nodeID
;;

(* 3. Validity of a Tableaux *)
let valid_tableau aTab =
    let _print = print_tableaux aTab in
    true
;;

(* 4. Selecting an unexamined node which is not closed *)
exception FULLY_DEVELOPED;;
let select_node aTab =
    let rec select_node nodeID =
        let currNode = aTab nodeID in
        if (currNode.closed = true) then
            raise FULLY_DEVELOPED
        else
            if (currNode.examined = false) then nodeID else
            if (currNode.num_desc = 0) then
                if (currNode.examined = true) then raise FULLY_DEVELOPED else nodeID
            else
                try
                    select_node (concat nodeID "0")
                with 
                    FULLY_DEVELOPED -> if (currNode.num_desc = 1) then 
                            raise FULLY_DEVELOPED
                        else
                            select_node (concat nodeID "1")
    in
    select_node ""
;;

(* 5. Deveoping the Tableaux *)
let rec extend_path_1_way aTab nodeID p1 t1 =
    let currNode = aTab nodeID in
    (* let _not_examined = assert(currNode.examined = false) in *)
    if (currNode.closed = true) then aTab else
    if (currNode.num_desc = 0) then
        let aTab = addNodeInTab aTab nodeID (nodeDesc currNode 1) in
        addNodeInTab aTab (concat nodeID "0") (newNode p1 t1)
    else
        let aTab = extend_path_1_way aTab (concat nodeID "0") p1 t1 in
        if (currNode.num_desc = 1) then 
            aTab
        else
            extend_path_1_way aTab (concat nodeID "1") p1 t1
;;

let rec extend_path_2_way aTab nodeID p1 t1 p2 t2 =
    let currNode = aTab nodeID in
    (* let _not_examined = assert(currNode.examined = false) in *)
    if (currNode.closed = true) then aTab else
    if (currNode.num_desc = 0) then
        let aTab = addNodeInTab aTab nodeID (nodeDesc currNode 2) in
        let aTab = addNodeInTab aTab (concat nodeID "0") (newNode p1 t1) in
        addNodeInTab aTab (concat nodeID "1") (newNode p2 t2)
    else
        let aTab = extend_path_2_way aTab (concat nodeID "0") p1 t1 p2 t2 in
        if (currNode.num_desc = 1) then
            aTab
        else
            extend_path_2_way aTab (concat nodeID "1") p1 t1 p2 t2
;;

exception INVALID_NODE_STRUC;;
let step_develop aTab nodeID =
    let currNode = aTab nodeID in
    let _not_examined = assert(currNode.examined = false) in
    if (currNode.closed = true) then aTab else
    if (currNode.value = Value(T, true) || currNode.value = Value(F, false)) then
        addNodeInTab aTab nodeID (nodeExamined currNode)
    else if (currNode.value = Value(T, false) || currNode.value = Value(F, true)) then
        let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
        closePath aTab nodeID
    else
        let aTab = contrad_path aTab nodeID in
        if (aTab nodeID <> currNode) then
            addNodeInTab aTab nodeID (nodeExamined currNode)
        else
            match currNode.value with
                | Value (L(x), t) -> addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Not (p1), t) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    extend_path_1_way aTab nodeID p1 (not t)
                | Value (And(p1, p2), true) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_1_way aTab nodeID p1 true in
                    let aTab = extend_path_1_way aTab nodeID p2 true in
                    aTab
                | Value (Or(p1, p2), false) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_1_way aTab nodeID p1 false in
                    let aTab = extend_path_1_way aTab nodeID p2 false in
                    aTab
                | Value (Impl(p1, p2), false) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_1_way aTab nodeID p1 true in
                    let aTab = extend_path_1_way aTab nodeID p2 false in
                    aTab
                | Value (And(p1, p2), false) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_2_way aTab nodeID p1 false p2 false in
                    aTab
                | Value (Or(p1, p2), true) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_2_way aTab nodeID p1 true p2 true in
                    aTab
                | Value (Impl(p1, p2), true) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_2_way aTab nodeID p1 false p2 true in
                    aTab
                | Value (Iff(p1, p2), t) ->
                    let aTab = addNodeInTab aTab nodeID (nodeExamined currNode) in
                    let aTab = extend_path_1_way aTab nodeID (And(Impl(p1, p2), Impl(p2,p1))) t in
                    aTab
                | _ -> raise INVALID_NODE_STRUC
;;
    

let develop_tableaux p t =
    let aTab = emptyTab in
    let aTab = addNodeInTab aTab "" (newNode p t) in
    let rec next_step aTab = 
        (* let _p = print_tableaux aTab in *)
        (* let _p = Printf.printf("--------\n") in *)
        try
            let nodeID = select_node aTab in
            let aTab = step_develop aTab nodeID in
            (* let _p = print_tableaux aTab in
            let _p = Printf.printf("---\n") in *)
            let aTab = contrad_path aTab nodeID in
            next_step aTab
        with
            FULLY_DEVELOPED -> aTab
    in
    next_step aTab
;;


(* 6. Finding the truth assignments *)
type assignment = Ass of prop * bool;;
let is_letter l = match l with
    | L(x) -> true
    | _ -> false
;;

let find_assignments p t = 
    let aTab = develop_tableaux p t in
    let rec assignment_list nodeID = 
        let currNode = aTab nodeID in
        if (currNode.closed = true) then
            []
        else 
            let curr_ass = match currNode.value with
                        | Value (L(x), t) -> [Ass(L(x), t)]
                        | Value (p, t) -> []
            in
            if (currNode.num_desc = 0) then
                if curr_ass = [] then [] else [curr_ass]
            else 
                let make_tot_ass partial_ass =
                    if curr_ass = [] then
                        partial_ass
                    else
                        let concat l = curr_ass@l in
                        List.map concat partial_ass
                in
                let left_ass = assignment_list (concat nodeID "0") in
                let left_tot_ass = make_tot_ass left_ass in
                if (currNode.num_desc = 1) then
                    left_tot_ass
                else
                    let right_ass = assignment_list (concat nodeID "1") in
                    let right_tot_ass = make_tot_ass right_ass in
                    left_tot_ass @ right_tot_ass
    in
    assignment_list ""
;;

(* 7. Tautology and Contradictions *)
let open_path_exists aTab =
    let rec open_path nodeID = 
        let currNode = aTab nodeID in
        if (currNode.closed = true) then
            false
        else if (currNode.num_desc = 0) then
            true
        else if (currNode.num_desc = 1) then
            open_path (concat nodeID "0")
        else
            (open_path (concat nodeID "0")) || (open_path (concat nodeID "1"))
    in
    open_path ""
;;

let check_tautology p = 
    let aTab = develop_tableaux p false in
    if open_path_exists aTab then
        let _p = Printf.printf "It's not a tautology :(\n" in
        find_assignments p false
    else
        let _p = Printf.printf "It's a tautology :)\n" in
        let _p = print_tableaux aTab in
        []
;;

let check_contradiction p = 
    let aTab = develop_tableaux p true in
    if open_path_exists aTab then
        let _p = Printf.printf "It's not a contradiction :(\n" in
        find_assignments p true
    else
        let _p = Printf.printf "It's a contradiction :)\n" in
        let _p = print_tableaux aTab in
        []
;;