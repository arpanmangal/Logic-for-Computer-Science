(* Helper functions like foldl *)

let rec foldl f e l = match l with
  | [] -> e
  | (x::xs) -> foldl f (f x e) xs
  ;;

let equal x y = (x = y);;
let add x y = (x + y);;
let andT x y = (x && y);;
let concat l1 l2 = l1 @ l2;;
let rec union l1 l2 = match l2 with
  | [] -> l1
  | (x::xs) -> if ((List.filter (equal x) l1) = []) then (union (x::l1) xs) else (union l1 xs)
  ;;
let rec isInside e l = match l with
  | [] -> false
  | (x::xs) -> if (x = e) then true else isInside e xs
  ;;