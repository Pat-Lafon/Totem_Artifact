(* Sized list predicate *)
(* Checks if a list respects a size bound *)

type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec len (l : ilist) : int =
  match l with
  | Nil -> 0
  | Cons { head = _; tail = xs } -> 1 + len xs