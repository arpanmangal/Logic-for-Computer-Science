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
    let _sn = select_node aTab in
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

(* F->T false *)
let p = Impl(F, T);;
let aTab = develop_tableaux p false;;
print_tableaux aTab;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* F->T true *)
let p = Impl(F, T);;
let aTab = develop_tableaux p true;;
print_tableaux aTab;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* p->(q->p) *)
let p = Impl(
    L("x"),
    Impl(L("y"), L("x"))
);;
let aTab = develop_tableaux p false;;
print_tableaux aTab;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* ((x1->x2)->x1)->x1 *)
let p = 
    let x1 = L "x1" in
    let x2 = L "x2" in
    Impl (
        Impl(
            Impl(x1, x2),
            x1
        ),
        x1
    )
;;
(* let aTab = develop_tableaux p false;; *)
(* print_tableaux aTab;; *)
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(*(not p -> not q) -> ((not p -> q) - p)) *)
(* let p = Impl(
    L("x"),
    Impl(L("y"), L("x"))
);;
let aTab = develop_tableaux p false;;
print_tableaux aTab;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");; *)
