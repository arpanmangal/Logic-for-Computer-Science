(* Tests for conversions.ml *)

#use "test.ml";;
#use "conversions.ml";;

(* Testing NNF *)
let np1 = nnf p1;;
let np2 = nnf p2;;
let np3 = nnf p3;;
let np4 = nnf p4;;
let np5 = nnf p5;;
let np6 = nnf p6;;

assert (truth p1 rho1 = truth np1 rho1);;
assert (truth p1 rho2 = truth np1 rho2);;
assert (truth p1 rho3 = truth np1 rho3);;
assert (truth p1 rho4 = truth np1 rho4);;

assert (truth p2 rho1 = truth np2 rho1);;
assert (truth p2 rho2 = truth np2 rho2);;
assert (truth p2 rho3 = truth np2 rho3);;
assert (truth p2 rho4 = truth np2 rho4);;
assert (truth p2 rho5 = truth np2 rho5);;
assert (truth p2 rho6 = truth np2 rho6);;
assert (truth p2 rho7 = truth np2 rho7);;
assert (truth p2 rho8 = truth np2 rho8);;

assert (truth p3 rho1 = truth np3 rho1);;
assert (truth p3 rho2 = truth np3 rho2);;
assert (truth p3 rho3 = truth np3 rho3);;
assert (truth p3 rho4 = truth np3 rho4);;

assert (truth p4 rho1 = truth np4 rho1);;
assert (truth p4 rho2 = truth np4 rho2);;
assert (truth p4 rho3 = truth np4 rho3);;
assert (truth p4 rho4 = truth np4 rho4);;

assert (truth p5 rho1 = truth np5 rho1);;
assert (truth p5 rho2 = truth np5 rho2);;
assert (truth p5 rho3 = truth np5 rho3);;
assert (truth p5 rho4 = truth np5 rho4);;

assert (truth p6 rho1 = truth np6 rho1);;
assert (truth p6 rho2 = truth np6 rho2);;
assert (truth p6 rho3 = truth np6 rho3);;
assert (truth p6 rho4 = truth np6 rho4);;


(* Testing CNF *)
let cp1 = cnf p1;;
let cp2 = cnf p2;;
let cp3 = cnf p3;;
let cp4 = cnf p4;;
let cp5 = cnf p5;;
let cp6 = cnf p6;;

assert (truth p1 rho1 = truth cp1 rho1);;
assert (truth p1 rho2 = truth cp1 rho2);;
assert (truth p1 rho3 = truth cp1 rho3);;
assert (truth p1 rho4 = truth cp1 rho4);;

assert (truth p2 rho1 = truth cp2 rho1);;
assert (truth p2 rho2 = truth cp2 rho2);;
assert (truth p2 rho3 = truth cp2 rho3);;
assert (truth p2 rho4 = truth cp2 rho4);;
assert (truth p2 rho5 = truth cp2 rho5);;
assert (truth p2 rho6 = truth cp2 rho6);;
assert (truth p2 rho7 = truth cp2 rho7);;
assert (truth p2 rho8 = truth cp2 rho8);;

assert (truth p3 rho1 = truth cp3 rho1);;
assert (truth p3 rho2 = truth cp3 rho2);;
assert (truth p3 rho3 = truth cp3 rho3);;
assert (truth p3 rho4 = truth cp3 rho4);;

assert (truth p4 rho1 = truth cp4 rho1);;
assert (truth p4 rho2 = truth cp4 rho2);;
assert (truth p4 rho3 = truth cp4 rho3);;
assert (truth p4 rho4 = truth cp4 rho4);;

assert (truth p5 rho1 = truth cp5 rho1);;
assert (truth p5 rho2 = truth cp5 rho2);;
assert (truth p5 rho3 = truth cp5 rho3);;
assert (truth p5 rho4 = truth cp5 rho4);;

assert (truth p6 rho1 = truth cp6 rho1);;
assert (truth p6 rho2 = truth cp6 rho2);;
assert (truth p6 rho3 = truth cp6 rho3);;
assert (truth p6 rho4 = truth cp6 rho4);;


(* Testing DNF *)
let dp1 = dnf p1;;
let dp2 = dnf p2;;
let dp3 = dnf p3;;
let dp4 = dnf p4;;
let dp5 = dnf p5;;
let dp6 = dnf p6;;

assert (truth p1 rho1 = truth dp1 rho1);;
assert (truth p1 rho2 = truth dp1 rho2);;
assert (truth p1 rho3 = truth dp1 rho3);;
assert (truth p1 rho4 = truth dp1 rho4);;

assert (truth p2 rho1 = truth dp2 rho1);;
assert (truth p2 rho2 = truth dp2 rho2);;
assert (truth p2 rho3 = truth dp2 rho3);;
assert (truth p2 rho4 = truth dp2 rho4);;
assert (truth p2 rho5 = truth dp2 rho5);;
assert (truth p2 rho6 = truth dp2 rho6);;
assert (truth p2 rho7 = truth dp2 rho7);;
assert (truth p2 rho8 = truth dp2 rho8);;

assert (truth p3 rho1 = truth dp3 rho1);;
assert (truth p3 rho2 = truth dp3 rho2);;
assert (truth p3 rho3 = truth dp3 rho3);;
assert (truth p3 rho4 = truth dp3 rho4);;

assert (truth p4 rho1 = truth dp4 rho1);;
assert (truth p4 rho2 = truth dp4 rho2);;
assert (truth p4 rho3 = truth dp4 rho3);;
assert (truth p4 rho4 = truth dp4 rho4);;

assert (truth p5 rho1 = truth dp5 rho1);;
assert (truth p5 rho2 = truth dp5 rho2);;
assert (truth p5 rho3 = truth dp5 rho3);;
assert (truth p5 rho4 = truth dp5 rho4);;

assert (truth p6 rho1 = truth dp6 rho1);;
assert (truth p6 rho2 = truth dp6 rho2);;
assert (truth p6 rho3 = truth dp6 rho3);;
assert (truth p6 rho4 = truth dp6 rho4);;