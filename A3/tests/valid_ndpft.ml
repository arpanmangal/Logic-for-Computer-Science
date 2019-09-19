(* Testing Natural Deduction Trees *)
#use "../natural_deduction.ml";;

let p = And(L "x", T);;
let q = Or(T, L "z");;
let gam = [T;L "y";q];;
let gam_p = union gam [p];;

let nd1 = Hyp(gam_p, p);;
let nd2 = Hyp(gam, q);;
let nd3 = Hyp(gam_p, q);;
let nd4 = TI(gam);;

assert (valid_ndprooftree nd1);;
assert (valid_ndprooftree nd2);;
assert (valid_ndprooftree nd3);;
assert (valid_ndprooftree nd4);;



let nd_pIMPq = ImpliesI (gam, Impl(p, q), nd2);;
assert (not (valid_ndprooftree nd_pIMPq));;
let nd_pIMPq = ImpliesI (gam, Impl(p, q), nd3);;
assert (valid_ndprooftree nd_pIMPq);;

let p = L "p";; let q = L "q";;
let gam_pq = [Impl(p,q); p]
let nd_q = ImpliesE (
    gam_pq, q,
    Hyp(gam_pq, Impl(p,q)),
    Hyp(gam_pq, p)
);;
assert (valid_ndprooftree nd_q);;


let rgam = [L "z"; Impl(T, F)];;
let nd_F = ImpliesE (
    rgam, F,
    Hyp(rgam, Impl(T, F)),
    TI(rgam)
);;
assert (valid_ndprooftree nd_F);;
let nd_P = NotInt (rgam, L "some_p", nd_F);;
assert (valid_ndprooftree nd_P);;

let gam = [L"r"; F];;
let pgam = union gam [p];;
let npgam = union gam [Not(p)];;
let nd_class = NotClass (gam, p, Hyp(npgam, F));;
let nd_class2 = NotClass (gam, Not p, Hyp(pgam, F));;
assert (valid_ndprooftree nd_class);;
assert (valid_ndprooftree nd_class2);;

let nd_andI = AndI (
    gam, And(p, Not p), 
    nd_class, nd_class2
);;
assert (valid_ndprooftree nd_andI);;

let nd_EL = AndEL (gam, p, nd_andI);;
let nd_ER = AndER (gam, Not p, nd_andI);;
assert (valid_ndprooftree nd_EL);;
assert (valid_ndprooftree nd_ER);;

let p = L "p";; let q = T;; let r = L "r";;
let gam = [p; r];;
let nd_p = Hyp(gam, p);;
let nd_q = TI(gam);;
let nd_orIL = OrIL (gam, Or (p, q), nd_p);;
let nd_orIR = OrIR (gam, Or (p, q), nd_q);;
assert (valid_ndprooftree nd_orIL);;
assert (valid_ndprooftree nd_orIR);;

let pgam = union gam [p];;
let qgam = union gam [q];;
let nd_orE = OrE (
    gam, r,
    nd_orIL,
    Hyp(pgam, r),
    Hyp(qgam, r)
);;
assert (valid_ndprooftree nd_orE);;
let nd_orE = OrE (
    gam, r,
    nd_orIR,
    Hyp(pgam, r),
    Hyp(qgam, r)
);;
assert (valid_ndprooftree nd_orE);;


(* assert(false);; *)
