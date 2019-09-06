(* Testing the set file *)
#use "../set.ml"

let s1 = empty_set ();;
let s2 = add_val 45 s1;;
let s3 = add_val 23 s2;;
let s4 = add_val 89 s2;;
let s5 = add_val 23 s3;;

let u = union s4 s5;;
assert (equal u [23; 45; 89]);;

let i = intersection s4 s5;;
assert (equal i [45]);;

assert (subset s2 s5);;
assert (subset s1 s4);;

let r = remove_element s5 45;;
assert (equal u [89; 23]);; 

let d = difference s5 s4;;
assert (equal d [23]);;
