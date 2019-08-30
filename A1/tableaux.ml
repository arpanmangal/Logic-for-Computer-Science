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
(* let emptyTab (_ : string) : node = (newNode T false);; Can change the defaults *)
(* let addNodeInTab aTab key p truth =
    let aNewNode = (newNode p truth) in
    fun key' -> if key' = key then aNewNode else aTab key;; *)
let addNodeInTab aTab nodeID aNode =
    fun nodeID' -> if nodeID' = nodeID then aNode else aTab nodeID
;;


(* Developing the tableaux *)
(* Helper functions *)
let concat s1 s2 =
    String.concat s1 ["";s2];;

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
    let _not_examined = assert(currNode.examined = false) in
    if (currNode.closed = true) then aTab else
    if (currNode.num_desc = 0) then
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
    let _not_examined = assert(currNode.examined = false) in
    if (currNode.closed = true) then aTab else
    if (currNode.num_desc = 0) then
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
                    let aTab = extend_path_1_way aTab nodeID p1 (not t) in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (And(p1, p2), true) ->
                    let aTab = extend_path_1_way aTab nodeID p1 true in
                    let aTab = extend_path_1_way aTab nodeID p2 true in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Or(p1, p2), false) ->
                    let aTab = extend_path_1_way aTab nodeID p1 false in
                    let aTab = extend_path_1_way aTab nodeID p2 false in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Impl(p1, p2), false) ->
                    let aTab = extend_path_1_way aTab nodeID p1 true in
                    let aTab = extend_path_1_way aTab nodeID p2 false in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (And(p1, p2), false) ->
                    let aTab = extend_path_2_way aTab nodeID p1 false p2 false in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Or(p1, p2), true) ->
                    let aTab = extend_path_2_way aTab nodeID p1 true p2 true in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Impl(p1, p2), true) ->
                    let aTab = extend_path_2_way aTab nodeID p1 false p2 true in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | Value (Iff(p1, p2), t) ->
                    let aTab = extend_path_1_way aTab nodeID (And(Impl(p1, p2), Impl(p2,p1))) t in
                    addNodeInTab aTab nodeID (nodeExamined currNode)
                | _ -> raise INVALID_NODE_STRUC
;;
    