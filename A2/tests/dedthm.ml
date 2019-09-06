(* Testing Hilbert Trees *)
#use "../hilbert.ml";;

let p1 = And(T, F);;
let p2 = Iff(Not T, L "x");;
let p3 = Impl(Iff(L "x", L "y"), Not F);;

let p1_p1 = pft_p_imp_p p1 [L "f"];;
let p2_p2 = pft_p_imp_p p2 [L "x"; T];;
let p3_p3 = pft_p_imp_p p3 [L "d"; F];;

let pft1 = 
    let x = L "x" in
    let y = L "y" in
    let gammaP = [x;y;T] in
    Ass(gammaP, x)
;;
let dpft1 = dedthm pft1 T;;

let pft2 = 
    let x = L "x" in
    let y = L "y" in
    let xy = Impl(x, y) in
    let gammaP = [xy; T] in
    Ass(gammaP, xy)
;;
let dpft2 = dedthm pft2 T;;

let pft3 =
    let x = L "x" in
    let y = L "y" in
    let z = L "z" in
    let xy = Impl(x, y) in
    let z_xy = Impl(z, xy) in
    let zx = Impl(z, x) in
    let zy = Impl(z, y) in
    let zx_zy = Impl(zx, zy) in
    let zxy_zxzy = Impl(z_xy, zx_zy) in
    let gammaP = [T] in
    S(gammaP, zxy_zxzy)
;;
let dpft3 = dedthm pft3 T;;


let pft4 = 
    let x = L "x" in
    let y = L "y" in 
    let p = T in
    let xy = Impl(x, y) in
    let gammaP = [xy; x; y; p] in
    let pft = MP(gammaP, y, Ass(gammaP, xy), Ass(gammaP, x)) in
    let _a = assert (valid_hprooftree pft) in
    pft
;;
let dpft4 = dedthm pft4 T;;

let pft5 =
    let x = L "x" in
    let y = L "y" in
    let w = L "w" in
    let xy = Impl(x, y) in
    let y_xy = Impl(y, xy) in
    let delta = [w; y] in
    let pft = MP(delta, xy, K(delta, y_xy), Ass(delta, y)) in
    let _a = assert (valid_hprooftree pft) in
    pft
;;
let dpft5 = dedthm pft5 (L "w");;

assert(valid_hprooftree dpft1);;
assert(valid_hprooftree dpft2);;
assert(valid_hprooftree dpft3);;
assert(valid_hprooftree dpft4);;
assert(valid_hprooftree dpft5);;
