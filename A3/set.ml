(* A generic set represention and functions *)

let empty_set () = [];;
let add_val v set = if List.mem v set then set else v::set;;
let rec union set1 set2 = match set2 with
    | [] -> set1
    | x::xs -> add_val x (union set1 xs)
;;
let rec equal set1 set2 = 
    union set1 set2 = set1
;;

let intersection set1 set2 = 
    let rec cum_inter set1 set2 inter = match set2 with
        | [] -> inter
        | x::xs -> if List.mem x set1 then
            cum_inter set1 xs (x::inter) 
          else
            cum_inter set1 xs inter
    in
    cum_inter set1 set2 (empty_set ())
;;

(* set1 <= set2 *)
let subset set1 set2 =
    let member status v = status && List.mem v set2 in
    List.fold_left member true set1
;;

(* let rec foldl f status l = match l with
    | [] -> status
    | x::xs -> foldl (f status x) xs
;; *)

(* set1 - set2 *)
let rec remove_element set e = match set with
    | [] -> set
    | x::xs -> if x = e then remove_element xs e else x::(remove_element xs e)
;;

let rec difference set1 set2 = match set2 with
    | [] -> set1
    | x::xs -> difference (remove_element set1 x) xs
;;