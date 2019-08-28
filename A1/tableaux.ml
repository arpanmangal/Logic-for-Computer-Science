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
type tableaux = List of string;;
let emptyTab (_ : string) : node = (newNode T false);; (* Can change the defaults *)
let addNodeInTab aTab key p truth = fun key' -> if key' = key then (newNode p truth) else aTab key;;


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
let rec closePath aTab nodeID = let currNode = aTab nodeID
    in
    let _currClosedNode = nodeClosed currNode
    in
    if currNode.num_desc = 0 then () else
        let _closeLeft = closePath aTab (concat nodeID "0")
        in
        if currNode.num_desc = 2 then 
            closePath aTab (concat nodeID "1")
        else
            ()
    ;;

(* 2. Closing all the contradicting paths *)
let contrad_path aTab =
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
        if isContraNode then closePath aTab nodeID else
            if currNode.num_desc = 0 then () else
                let _contraLeft = closeContradPaths aTab (concat nodeID "0")
                in
                if currNode.num_desc = 2 
                then
                    closeContradPaths aTab (concat nodeID "1")
                else
                    ()
    in
    closeContradPaths aTab ""
;;