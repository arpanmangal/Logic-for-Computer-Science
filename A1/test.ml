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
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(*(not p -> not q) -> ((not p -> q) - p)) *)
let p = 
    let p = L "p" in
    let q = L "q" in
    let np = Not p in
    let nq = Not q in
    Impl(
        Impl(np, nq),
        Impl(
            Impl(np, q),
            p
        )
    )
;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* T or F *)
let p = Or(T, F);;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* T and F *)
let p = And(T, F);;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

let p = Iff(T, T);;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

let p = Iff(F, F);;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

let p = Iff(T, F);;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

Printf.printf("========================================================================================================");;

(* p or q  or  p or not q *)
let p =
    let p = L "p" in
    let q = L "q" in
    let nq = Not q in
    Or(
        Or (p, q),
        Or (p, nq)
    )
;;

check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;

(* iff(p, q) and iff(p, notq) *)
let p =
    let p = L "p" in
    let q = L "q" in
    let nq = Not q in
    let pIFFq = Iff(p, q) in
    let pIFFnq = Iff(p, nq) in
    And(pIFFq, pIFFnq)
;;
check_tautology p;;
check_contradiction p;;

Printf.printf("========================================================================================================");;
