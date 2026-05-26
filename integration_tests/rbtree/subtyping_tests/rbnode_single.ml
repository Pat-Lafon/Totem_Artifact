let[@assert] rty1 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false)))
   && (is_rbtnode v) && ((color v) == true) && num_black v 0 true && no_red_red v true
   && clr
    : [%v: irbtree])
    [@under]

let[@assert] rty2 =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let clr = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if clr then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (fun ((t [@exists]) : irbtree) ->
     is_rbtleaf t && (is_rbtnode v) && ((color v) == true)
     && ((is_rbtleaf v) || ((is_rbtnode v) && (not ((color v) == false))))
     && clr
     && (left v) == t && (right v) == t
    : [%v: irbtree])
    [@under]
