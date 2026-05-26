(* The datatype constructor should use the lower case instead of the first char *)
type unit = TT
type bool = True | False
type irbtree = Rbtleaf | Rbtnode of bool * irbtree * int * irbtree
