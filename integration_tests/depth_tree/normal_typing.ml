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
(* dt *)

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

(* method predicates *)
(* for lists *)
(* val len : 'a list -> int -> bool
val emp : 'a list -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : int list -> int -> bool
val sorted : 'a list -> bool
val uniq : 'a list -> bool
val all_evens : 'a list -> bool *)

(* constructors for lists *)
val is_nil : ilist -> bool
val is_cons : ilist -> bool
val head : ilist -> int
val tail : ilist -> ilist

(* constructors for trees *)
val is_leaf : itree -> bool
val is_node : itree -> bool
val value : itree -> int
val left : itree -> itree
val right : itree -> itree

(* for tree *)
val depth : itree -> int -> bool
(* val leaf : itree -> bool *)(*
val root : 'a tree -> 'a -> bool
val lch : 'a tree -> 'a tree -> bool
val rch : 'a tree -> 'a tree -> bool
val tree_mem : itree -> int -> bool *)
val bst : itree -> bool -> bool
val complete : itree -> bool -> bool
val lower_bound : itree -> int -> bool -> bool
val upper_bound : itree -> int -> bool -> bool
