(* Duplicate list predicate *)
(* Checks if all elements in a list are equal to a given value *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

(* let [@simp] [@grind] rec mem (x : int) (l : ilist) : bool =
  match l with
  | Nil -> false
  | Cons { head = h; tail = t } -> (h = x) || mem x t *)

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs

let [@simp] [@grind] rec all_equal (l : ilist) (x : int) : bool =
  match l with
  | Nil -> true
  | Cons { head = h; tail = t } -> (h = x) && all_equal t x
