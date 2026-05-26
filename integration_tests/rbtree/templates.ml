let[@axiom] rec_arg (arg : int) (param : int) = param >= 0 && param < arg

let[@axiom] rec_arg2 (arg1 : int) (param1 : int) (arg2 : int) (param2 : int) =
  param1 >= 0 && param2 >= 0
  && ((param1 < arg1 && param2 == arg2) || param2 < arg2)

let[@axiom] template_eq_0 (x : int) = x == 0
let[@axiom] template_lt (a : int) (b : int) = a < b
let[@axiom] template_leq_1 (a : int) = a <= 1
let[@axiom] template_rb_leaf (v : irbtree) = is_rbtleaf v
let[@axiom] template_no_red_red (v : irbtree) = no_red_red v true
(* let[@axiom] template_red_root (v : irbtree) = (is_rbtnode v && (color v) == true)
let[@axiom] template_black_root (v : irbtree) = (is_rbtnode v && (color v) == false) *)
let[@axiom] template_num_black (v : irbtree) (n : int) = num_black v n true
let[@axiom] template_num_black_0 (v : irbtree) = num_black v 0 true
