let[@axiom] rec_arg (arg : int) (param : int) = param >= 0 && param < arg

let[@axiom] rec_arg2 (arg1 : int) (param1 : int) (arg2 : int) (param2 : int) =
  param1 >= 0 && param2 >= 0
  && ((param1 < arg1 && param2 == arg2) || param2 < arg2)

let[@axiom] template_eq_0 (x : int) = x == 0
let[@axiom] template_lt (a : int) (b : int) = a < b
let[@axiom] template_leq_1 (a : int) = a <= 1
let[@axiom] template_emp (l : ilist) = is_nil l
let[@axiom] template_singleton (l : ilist) = len l 1
let[@axiom] template_sorted (l : ilist) = sorted l true
