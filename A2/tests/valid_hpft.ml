(* Testing Hilbert Trees *)
#use "../hilbert.ml";;

let gam = 
    let p = And(Or(L "y", L "ui"), Not (T)) in
    let q = Iff (F, And(T, F)) in
    let np = Not p in
    let nq = Not q in
    let np_nq = Impl(np, nq) in

    let g1 = Impl(F, T) in
    let g2 = Or (L "x", L "y") in
    let g3 = Not (L "z") in
    let g4 = np_nq in
    let gam = empty_set () in
    let gam = add_val g1 gam in
    let gam = add_val g2 gam in
    let gam = add_val g3 gam in
    add_val g4 gam
;;

let h1 = Ass(gam, Not (L "z"));;
assert (valid_hprooftree h1);;

let h2 = 
    let p = And(Or(L "y", L "ui"), Not (T)) in
    let q = Iff (F, And(T, F)) in
    K (gam, Impl(p, Impl(q, p)))
;;
assert (valid_hprooftree h2);;

let h3 = 
    let p = And(Or(L "y", L "ui"), Not (T)) in
    let q = Iff (F, And(T, F)) in
    let r = T in
    let qr = Impl(q, r) in
    let pq = Impl(p, q) in
    let pr = Impl(p, r) in
    let p_qr = Impl(p, qr) in
    let pq_pr = Impl(pq, pr) in
    let s = Impl(p_qr, pq_pr) in
    S (gam, s)
;;
assert (valid_hprooftree h3);;

let h4 = 
    let p = And(Or(L "y", L "ui"), Not (T)) in
    let q = Iff (F, And(T, F)) in
    let np = Not p in
    let nq = Not q in
    let np_nq = Impl(np, nq) in
    let np_q_p = Impl(Impl(np, q), p) in
    let r = Impl(np_nq, np_q_p) in
    R (gam, r)
;;
assert (valid_hprooftree h4);;

let h5 =
    let p = And(Or(L "y", L "ui"), Not (T)) in
    let q = Iff (F, And(T, F)) in
    let np = Not p in
    let nq = Not q in
    let np_nq = Impl(np, nq) in
    let np_q_p = Impl(Impl(np, q), p) in
    MP(gam, np_q_p, h4, Ass(gam, np_nq))
;;
assert (valid_hprooftree h5);;
