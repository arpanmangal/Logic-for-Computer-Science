(* Testing Natural Deduction Trees *)
(* Contains proofs for pad, prune and graft *)
#use "../natural_deduction.ml";;

let gam = [L "x"; L "p"];;
let p = L "p";;

let pIMPp = ImpliesI (
    gam, Impl(p, p),
    Hyp ((union gam [p]), p)
);;

assert (valid_ndprooftree pIMPp);;

let pruned = prune pIMPp;;

let padded = pad pIMPp [L "z"];;
let pruned = prune padded;;
let padded = pad pruned [p];;
let pruned = prune padded;;



(* A big proof-tree *)
let x = L "x";; let y = L "y";;
let gam1 = [x; F];;
let gam2 = [L "z"; T];;
let gam = gam1;;

let pftF1 = Hyp (union gam [F], F);;
let pftF2 = ImpliesI (gam, Impl(F, F), pftF1);;
let pftF3 = NotClass (gam, F, Hyp (union gam [Not F], F));;
let pftF4 = AndI (
        gam, And (F, x),
        pftF3, Hyp (gam, x)
    );;
let pftF5 = AndEL (gam, F, pftF4);;
let pftF6 = ImpliesE (gam, F, pftF2, pftF5);;
assert (valid_ndprooftree pftF1);;
assert (valid_ndprooftree pftF2);;
assert (valid_ndprooftree pftF3);;
assert (valid_ndprooftree pftF4);;
assert (valid_ndprooftree pftF5);;
assert (valid_ndprooftree pftF6);;

let q' = Impl (y, y);;
let pftQ = ImpliesI (
    gam, q',
    Hyp ((union gam [y]), y)
);;
assert (valid_ndprooftree pftQ);;

let p = T;;
let q = And (F, q');;
let pftAND = AndI (gam, q, pftF6, pftQ);;
assert (valid_ndprooftree pftAND);;

let pftPorQ = OrIR (gam, Or(p, q), pftAND);;
assert (valid_ndprooftree pftPorQ);;

let pftT1 = Hyp (union gam [p], T);;
let pftT2 = TI (union gam [q]);;

assert (valid_ndprooftree pftT1);;
assert (valid_ndprooftree pftT2);;

let bigPFT = OrE (gam, T, pftPorQ, pftT1, pftT2);;
assert (valid_ndprooftree bigPFT);;

extract_gamma bigPFT;;

let padded = pad bigPFT gam2;;
let pruned = prune (bigPFT);;
let pruned2 = prune (padded);;

extract_gamma padded;;
extract_gamma pruned;;
extract_gamma pruned2;;

assert (valid_ndprooftree pruned2);;

let g = L "g";;
let one_gamma = [F; g; Impl(g, x)];;
let pft_list = [
    Hyp (one_gamma, F);
    ImpliesE (one_gamma, x, Hyp(one_gamma, Impl(g,x)), Hyp(one_gamma, g))
];;

extract_gamma bigPFT;;
let gft = graft bigPFT pft_list;;
extract_gamma gft;;

let pgft = prune gft;;
extract_gamma pgft;;

(* let p = T;; let q = L "q";;
let gam = [L "bh"];;
let pftPorQ = OrIL (gam, Or(p, q), TI(gam));;
let pft2 = Hyp (union gam [p], T);;
let pft3 = TI (union gam [q]);;
let smallPFT = OrE (gam, T, pftPorQ, pft2, pft3);;
extract_gamma smallPFT;;
prune smallPFT;; *)

(* assert (false);; *)