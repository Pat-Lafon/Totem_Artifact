(* Tree height function *)
(* Computes the height of a binary tree *)

type [@grind] itree = Leaf | Node of { value : int; left : itree; right : itree }

let [@simp] [@grind] rec depth (t : itree) : int = match t with
| Leaf -> 0
| Node { value = v; left = l; right = r } -> if (depth l > depth r) then (1 + depth l) else (1 + depth r)
