val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( * ) : int -> int -> int
val not : bool -> bool
val ite : bool -> 'a -> 'a -> 'a

(* others *)
val int_range : int -> int -> int
val bool_gen : unit -> bool
val int_gen : unit -> int
val nat_gen : unit -> int
val int_range_inc : int -> int -> int
val int_range_inex : int -> int -> int
val int_range_inex_zero : int -> int
val difference_inex : int -> int -> int
val increment : int -> int
val decrement : int -> int
val double : int -> int
val lt_eq_one : int -> bool
val gt_eq_int_gen : int -> int
val sizecheck : int -> bool
val subs : int -> int
val incr : int -> int
val dummy : unit

(* constructors for irbtree *)
val is_rbtleaf : irbtree -> bool
val is_rbtnode : irbtree -> bool
val color : irbtree -> bool
val left : irbtree -> irbtree
val right : irbtree -> irbtree
val value : irbtree -> int

(* method predicates for irbtree *)
val num_black : irbtree -> int -> bool -> bool
val no_red_red : irbtree -> bool -> bool
val rbtree_invariant : irbtree -> int -> bool -> bool
