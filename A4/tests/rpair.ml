(* Tests for r-pairs *)

#use "../rpair.ml";;

(* Basic trees *)
let gam = [L "x"; L "y"];;
let p = L "x";; let q = T;;
let pft1 = AndEL (gam, p, AndI(
    gam, And(p, q), Hyp(gam, p), TI(gam)
));;

let gam = [L "x"; L "y"];;
let p = L "x";; let q = T;;
let pft2 = AndER (gam, q, AndI(
    gam, And(p, q), Hyp(gam, p), TI(gam)
));;

let gam = [L "x"; L "y"];;
let p = T;; let q = L "x";;
let pft3 = ImpliesE (gam, q,
    ImpliesI (gam, Impl(p, q), Hyp (union gam [p], q)),
    TI (gam)
);;

let gam = [L "x"; L "y"];;
let p = T;; let q = L "x";; let r = T;; let x = L "x";;
let pft4 = OrE (gam, r, 
    OrIL (gam, Or(p, q), TI(gam)),
    Hyp (union gam [p], r),
    TI(union gam [q])
);;

let gam = [L "x"; L "y"];;
let p = T;; let q = L "x";; let r = T;; let x = L "x";;
let pft5 = OrE (gam, r, 
    OrIR (gam, Or(p, q), Hyp(gam, q)),
    Hyp (union gam [p], r),
    TI(union gam [q])
);;

(* Checking validity *)
assert (valid_ndprooftree pft1);;
assert (valid_ndprooftree pft2);;
assert (valid_ndprooftree pft3);;
assert (valid_ndprooftree pft4);;
assert (valid_ndprooftree pft5);;

(* Finding r-pairs *)
let r1 = find_rpair pft1;; assert (r1 = pft1);;
let r2 = find_rpair pft2;; assert (r2 = pft2);;
let r3 = find_rpair pft3;; assert (r3 = pft3);;
let r4 = find_rpair pft4;; assert (r4 = pft4);;
let r5 = find_rpair pft5;; assert (r5 = pft5);;

let s1 = simplify1 r1;;
let s2 = simplify1 r2;;
let s3 = simplify1 r3;;
let s4 = simplify1 r4;;
let s5 = simplify1 r5;;