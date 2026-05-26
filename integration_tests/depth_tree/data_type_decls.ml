(* The datatype constructor should use the lower case instead of the first char *)
type unit = TT
type bool = True | False
type itree = Leaf | Node of { value : int; left : itree; right : itree }
