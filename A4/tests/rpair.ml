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


(* The big massive trees *)

(* Individual proofs *)
let x = T;; let w = L "w";;
let v = L "v";; let v' = T;;
let y = L "y";; let z = L "z";; let z1 = T;; let z2 = L "z2";;
let gam = [w; v; L "random"; Impl(v, y); Or(z1, z2)];;

let pft_x = ImpliesE(
    gam, x,
    ImpliesI (gam, Impl(w, x), TI (union gam [w])),
    Hyp (gam, w)
);; assert (valid_ndprooftree pft_x);;

let pft_y = ImpliesE(
    gam, y,
    Hyp(gam, Impl(v, y)),
    AndEL(gam, v, 
        AndI(gam, And(v, v'), Hyp(gam, v), TI(gam))
    )
);; assert (valid_ndprooftree pft_y);;

let sx = normalise pft_x;;
let sy = normalise pft_y;;


let z = x;; let z1 = T;;
let gam_x = union gam [x];; let gam_y = union gam [y];;
let pft_x_z = AndEL(
    gam_x, z,
    AndI (gam_x, And(z, z1), Hyp(gam_x, z), TI(gam_x))
);; assert (valid_ndprooftree pft_x_z);;
let sxz = normalise pft_x_z;;

let pft_y_z = TI(gam_y);;
let syz = normalise pft_y_z;;

let pft_Z1 = OrE(
    gam, z,
    OrIL (gam, Or(x, y), pft_x),
    pft_x_z,
    pft_y_z
);; assert (valid_ndprooftree pft_Z1);;
let sZ1 = normalise pft_Z1;;


let z1 = T;; let z2 = L "z2";;
let z = Or(z1, z2);;
let gam_x = union gam [x];; let gam_y = union gam [y];;

let pft_x_z = Hyp(gam_x, z);; assert (valid_ndprooftree pft_x_z);;
let sxz = normalise pft_x_z;;

let pft_y_z = OrIL (
    gam_y, z,
    ImpliesE(gam_y, z1,
        ImpliesI(gam_y, Impl(y, z1), TI(gam_y)),
        Hyp(gam_y, y)
    )
);; assert (valid_ndprooftree pft_y_z);;
let syz = normalise pft_y_z;;

let pft_Z2 = OrE(
    gam, z,
    OrIR (gam, Or(x, y), pft_y),
    pft_x_z,
    pft_y_z
);; assert (valid_ndprooftree pft_Z2);;
let sZ2 = normalise pft_Z2;;


