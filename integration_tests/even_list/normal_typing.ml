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
val len : ilist -> int -> bool
val nil : ilist
val cons : int -> ilist -> ilist
val is_cons : ilist -> bool
val is_nil : ilist -> bool
val head : ilist -> int
val tail : ilist -> ilist
val list_mem : ilist -> int -> bool
val sorted : ilist -> bool
val uniq : ilist -> bool
val is_even : int -> bool -> bool
val all_evens : ilist -> bool -> bool
