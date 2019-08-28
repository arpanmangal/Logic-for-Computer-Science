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


(* definition of a tableaux *)
type tableaux = List of string;;
let emptyTab (_ : string) : node = (newNode T false);; (* Can change the defaults *)
let addNodeInTab aTab key p truth = fun key' -> if key' = key then (newNode p truth) else aTab key;;



(* Developing the tableaux *)