(* Unique list predicate *)
(* Checks if all elements in a list are distinct *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs

let [@simp] [@grind] rec mem (l : ilist) (x : int)  : bool =
  match l with
  | Nil -> false
  | Cons { head = h; tail = t } -> (h = x) || mem t x

let [@simp] [@grind] rec uniq (l : ilist) : bool =
  match l with
  | Nil -> true
  | Cons { head = h; tail = t } -> not (mem t h) && uniq t
