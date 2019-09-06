(* Testing Hilbert Trees *)
#use "../hilbert.ml";;

let ht =
    let p = Or(T, F) in
    let q = F in
    let r = p in
    let pq = Impl(p, q) in
    let pr = Impl(p, r) in
    let qr = Impl(q, r) in
    let p_qr = Impl(p, qr) in
    let pq_pr = Impl(pq, pr) in
    
    let gam = empty_set() in 
    let gam = add_val p gam in
    let gam = add_val pq gam in

    let s = S(gam, Impl(p_qr, pq_pr)) in
    let k = K(gam, p_qr) in
    let mp = MP(gam, pq_pr, s, k) in
    let ass = Ass(gam, pq) in
    
    MP (gam, pr, mp, ass)
;;

assert (valid_hprooftree ht);;

let ht1 = pad ht [Impl(T, F); Not (L "x")];;
let pht = prune ht;;
let pht1 = prune ht1;;

extract_gamma ht;;
extract_gamma ht1;;
extract_gamma pht;;
extract_gamma pht1;;
