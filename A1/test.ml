(* Testing tableaux.ml *)

#use "tableaux.ml";;

Printf.printf("========================================================================================================");;

exception EXCEPTION_EXPECTED;;

(* Not F true *)
let p = Not(F);;
let aTab = addNodeInTab emptyTab "" (newNode p true);;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;;
let a = try
    let sn = select_node aTab in
    raise EXCEPTION_EXPECTED
with
    FULLY_DEVELOPED -> "FULLY_DEVELOPED"
;;

Printf.printf("========================================================================================================");;

(* F->T true *)
let p = Impl(F, T);;
let aTab = addNodeInTab emptyTab "" (newNode p true);;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;;
let next_expand = select_node aTab;;
let aTab = step_develop aTab next_expand;;
print_tableaux aTab;;
let a = try
    let _sn = select_node aTab in
    raise EXCEPTION_EXPECTED
with
    FULLY_DEVELOPED -> "FULLY_DEVELOPED"
;;

Printf.printf("========================================================================================================");;
