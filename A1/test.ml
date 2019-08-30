(* Testing tableaux.ml *)

#use "tableaux.ml";;

(* Testing printing of Tableaux *)
let tab = 
    let aTab = addNodeInTab emptyTab "" (newNode (Not F) true) in
    addNodeInTab aTab "0" (newNode F false)
;;
print_tableaux tab;;

(* Not F true *)
(* let p1 = Not(F);;
let aTab = addNodeInTab emptyTab "" (newNode p1 true);;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let bTab = step_develop aTab next_expand;;
print_tableaux bTab;; *)

(* F->T true
let p1 = Impl(F, T);;
let aTab = addNodeInTab emptyTab "" (newNode p1 true);;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;; *)