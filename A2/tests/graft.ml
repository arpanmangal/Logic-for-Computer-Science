(* Testing Hilbert Trees *)
#use "../hilbert.ml";;

let gam = 
    let gam = empty_set () in
    let gam = add_val T gam in
    let gam = add_val (Impl (T, L "w")) gam in
    let gam = add_val (L "y") gam in
    gam
;;

gam;;

let pft1 = 
    let x = L "x" in
    let y = L "y" in
    let xy = Impl(x, y) in
    let y_xy = Impl(y, xy) in
    MP (gam, xy, K(gam, y_xy), Ass(gam, y))
;;

let pft2 =
    let w = L "w" in
    let tw = Impl(T, w) in
    MP (gam, w, Ass(gam, tw), Ass(gam, T))
;;

assert (valid_hprooftree pft1);;
assert (valid_hprooftree pft2);;

let pft =
    let x = L "x" in
    let y = L "y" in
    let w = L "w" in
    let xy = Impl(x, y) in
    let xy_w = Impl(xy, w) in

    let delta = [w;xy] in

    let w_xyw = Impl(w, xy_w) in
    let mp1 = MP(delta, xy_w, K(delta, w_xyw), Ass(delta, w)) in
    MP (delta, w, mp1, Ass(delta, xy))
;;

assert (valid_hprooftree pft);;


let gpft = graft pft [pft1; pft2];;
assert (valid_hprooftree gpft);;

extract_gamma gpft;;
extract_prop gpft;;
